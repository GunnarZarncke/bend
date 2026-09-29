// hypervisor: the bare lane's boot and alternates, included by bare.c at
// the end of the runtime: the float text stubs, the MMU, the default
// vectors, bend_main and _start, and the event loop without descriptors.
// SPEC.md, section 10.

static int f32_text(char* buf, f32 v) {
  err_fail("no float text on the bare lane");
  return 0;
}

static Term f32_show(Env e, Term x) {
  err_fail("no float text on the bare lane");
  return 0;
}

static Term f32_read(Env e, Term s) {
  err_fail("no float text on the bare lane");
  return 0;
}


// Boot
// ====

// _start (core 0; the others park in wfi) sets the stack, zeroes .bss,
// opens FP at EL2, points VBAR_EL2 at bend_vectors, turns the MMU on over
// an identity map (device below 1 GiB, normal memory above), runs the
// init array (the effects register there), then calls bend_main and
// exits QEMU with its code over semihosting, unless bare_again is set:
// then it zeroes .bss, runs the init array and bend_main again, a fresh
// instance over the same persist region. An effect installs its own
// vectors with msr vbar_el2; the default ones print the fault and exit 2.

// bend_l1 sits in .data (a restart zeroes .bss under a live MMU)
static u64 bend_l1[512] __attribute__((aligned(4096))) = { 1 };



__attribute__((used)) void bare_mmu(void) {
  bend_l1[0] = 0x401ull;
  for (u64 i = 1; i < 4; i += 1) {
    bend_l1[i] = (i << 30) | 0x705ull;
  }
  u64 sctlr;
  __asm__ volatile("msr mair_el2, %0" : : "r"(0xFF00ull));
  __asm__ volatile("msr tcr_el2, %0" : : "r"(0x80803520ull));
  __asm__ volatile("msr ttbr0_el2, %0" : : "r"((u64)(uintptr_t)bend_l1));
  __asm__ volatile("dsb ish\n\ttlbi alle2\n\tdsb ish\n\tisb" : : : "memory");
  __asm__ volatile("mrs %0, sctlr_el2" : "=r"(sctlr));
  sctlr |= 1ull | 4ull | (1ull << 12);
  __asm__ volatile("msr sctlr_el2, %0\n\tisb" : : "r"(sctlr) : "memory");
}

__attribute__((used, noreturn)) void bare_fault(u64 esr, u64 elr, u64 far) {
  if (far >= (u64)(uintptr_t)__stack_hi
    && far < (u64)(uintptr_t)__stack_hi + 65536) {
    err_fail(ERR_TEXT[ERR_DEEP]);
  }
  printf("bend: fault at EL2 esr=%llx elr=%llx far=%llx\n",
    (unsigned long long)esr, (unsigned long long)elr,
    (unsigned long long)far);
  bare_exit(2);
}

static char* bare_argv[] = { "bend" };

__attribute__((used)) int bend_main(void) {
  bare_brk = __arena_start;
  io_argv  = bare_argv;
  io_argc  = 1;
  io_loop(corpus_setup(false, 1, 0));
  io_sync();
  return 0;
}

__asm__(
  ".section .text.boot,\"ax\"\n"
  ".global _start\n"
  "_start:\n"
  "  mrs x0, mpidr_el1\n"
  "  and x0, x0, #0xffffff\n"
  "  cbnz x0, 9f\n"
  "  ldr x0, =__stack_top\n"
  "  mov sp, x0\n"
  "  ldr x0, =__bss_start\n"
  "  ldr x1, =__bss_end\n"
  "1:\n"
  "  cmp x0, x1\n"
  "  b.hs 2f\n"
  "  str xzr, [x0], #8\n"
  "  b 1b\n"
  "2:\n"
  "  mov x0, #0x33ff\n"
  "  msr cptr_el2, x0\n"
  "  ldr x0, =bend_vectors\n"
  "  msr vbar_el2, x0\n"
  "  isb\n"
  "  bl bare_mmu\n"
  "5:\n"
  "  ldr x19, =__init_array_start\n"
  "  ldr x20, =__init_array_end\n"
  "3:\n"
  "  cmp x19, x20\n"
  "  b.hs 4f\n"
  "  ldr x0, [x19], #8\n"
  "  blr x0\n"
  "  b 3b\n"
  "4:\n"
  "  bl bend_main\n"
  "  ldr x1, =bare_again\n"
  "  ldr w2, [x1]\n"
  "  cbz w2, 8f\n"
  "  ldr x0, =__bss_start\n"
  "  ldr x1, =__bss_end\n"
  "6:\n"
  "  cmp x0, x1\n"
  "  b.hs 5b\n"
  "  str xzr, [x0], #8\n"
  "  b 6b\n"
  "8:\n"
  "  bl bare_exit\n"
  "9:\n"
  "  wfi\n"
  "  b 9b\n"
  ".balign 2048\n"
  ".global bend_vectors\n"
  "bend_vectors:\n"
  ".rept 16\n"
  ".balign 128\n"
  "  mrs x0, esr_el2\n"
  "  mrs x1, elr_el2\n"
  "  mrs x2, far_el2\n"
  "  b bare_fault\n"
  ".endr\n"
  ".text\n"
);


// Alternates
// ==========
// the event loop without descriptors; the shim declares these

// The term stack is the linker's region at the top of RAM: a deep
// recursion runs off it into unbacked space, which faults into the vectors.
static IoWork* io_done_q;

static void io_take(Env e) {
  while (io_done_q != NULL) {
    IoWork* a = io_pop(&io_done_q);
    a->item   = a->pack(e, a);
    io_push(&io_runs, a);
    io_busy -= 1;
  }
}

static Term io_work(IoWork* w, IoCall call, IoPack pack) {
  w->call  = call;
  w->pack  = pack;
  io_busy += 1;
  call(w);
  io_push(&io_done_q, w);
  return IO_PARK;
}

// No descriptors: the loop takes the finished calls, then spins to the
// earliest deadline and wakes the timers that passed.
static void io_wait(Env e) {
  io_take(e);
  if (io_runs != NULL) {
    return;
  }
  u64 soon = io_park != NULL ? io_park->next->time : 0;
  if (soon == 0) {
    err_fail("a descriptor wait on the bare lane");
  }
  while (io_tick() < soon) {
    __asm__ volatile("yield");
  }
  u64     now  = io_tick();
  IoWork* todo = io_park;
  io_park = NULL;
  while (todo != NULL) {
    IoWork* a = io_pop(&todo);
    if (a->time == 0 || a->time > now) {
      io_park_add(a);
      continue;
    }
    Term x = a->pack(e, a);
    if (x != IO_PARK) {
      a->item = x;
      io_push(&io_runs, a);
    }
  }
}
