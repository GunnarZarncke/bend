// hypervisor: the EL2 shim, the C the kernel trusts, part one: the state
// (guest save areas, stage-2 tables, handoff slots) in the persist
// region, the trap vectors and the context switch, the word crossings
// and the GICv3 timer setup. hv.c, part two, has the guests and the
// effects. Effect sources splice in the order main reaches their defs,
// so Hv.instance, main's first call, imports this file and it comes
// first. SPEC.md, section 8, lists the effects.

#include <stddef.h>

#define HV_GUESTS  8
#define HV_BLOCK   (2ull << 20)
#define HV_BASE    0xA0000000ull   // block 0 of the ownership list
#define HV_L2_GIB  0x80000000ull   // the GiB the level-2 table maps
#define HV_L2_AT   ((HV_BASE - HV_L2_GIB) / HV_BLOCK)
#define HV_TIMER   26              // the EL2 physical timer's PPI
#define HV_MAGIC   0x48565631u
#define GICD       0x08000000ull
#define GICR       0x080A0000ull
#define GICR_SGI   (GICR + 0x10000)

// the guest register file the shim saves and restores; the window the
// kernel sees is x0..x3 and elr
typedef struct {
  u64 x[31];
  u64 sp_el1;
  u64 sp_el0;
  u64 elr;
  u64 spsr;
  u64 sys[17];
  u64 esr;
  u64 far;
  u64 hpfar;
  u64 pad;
} HvArea;

_Static_assert(offsetof(HvArea, sp_el1) == 248, "sp_el1");
_Static_assert(offsetof(HvArea, sys) == 280, "sys");
_Static_assert(sizeof(HvArea) == 448, "area");

typedef struct {
  u64 l1[512] __attribute__((aligned(4096)));
  u64 l2[512] __attribute__((aligned(4096)));
} HvTables;

// the handoff record: two slots, the newer generation wins
typedef struct {
  u32 gen;
  u32 len;
  u32 words[4094];
} HvSlot;

typedef struct {
  u64      host_sp;            // first: the exit path finds it by symbol
  u32      magic;
  u32      guests;
  u32      instances;
  u32      pad;
  HvArea   area[HV_GUESTS];
  HvSlot   slot[2];
  HvTables tab[HV_GUESTS] __attribute__((aligned(4096)));
} HvState;

#define HV ((HvState*)__persist_start)

// Registers
// ---------

#define HV_RD(name, v) __asm__ volatile("mrs %0, " name : "=r"(v))
#define HV_WR(name, v) __asm__ volatile("msr " name ", %0" : : "r"((u64)(v)))

#define ICC_SRE_EL2     "S3_4_C12_C9_5"
#define ICC_PMR_EL1     "S3_0_C4_C6_0"
#define ICC_IGRPEN1_EL1 "S3_0_C12_C12_7"
#define ICC_IAR1_EL1    "S3_0_C12_C12_0"
#define ICC_EOIR1_EL1   "S3_0_C12_C12_1"
#define CNTHP_CTL_EL2   "S3_4_C14_C2_1"
#define CNTHP_TVAL_EL2  "S3_4_C14_C2_0"

static inline void hv_w32(u64 at, u32 v) {
  *(volatile u32*)(uintptr_t)at = v;
}

static inline u32 hv_r32(u64 at) {
  return *(volatile u32*)(uintptr_t)at;
}

// Switch
// ------
// hv_enter(area, &host_sp) saves the callee-saved registers and the
// stack, loads the guest and ERETs. A guest exit lands in hv_vectors,
// which saves the guest into the area TPIDR_EL2 names, restores the host
// and returns from hv_enter with the exit kind: 0 sync, 1 irq, 2 other.

#define HV_SYS(X) \
  X("sctlr_el1", 280) X("ttbr0_el1", 288) X("ttbr1_el1", 296) \
  X("tcr_el1", 304) X("mair_el1", 312) X("amair_el1", 320) \
  X("vbar_el1", 328) X("spsr_el1", 336) X("elr_el1", 344) \
  X("esr_el1", 352) X("far_el1", 360) X("tpidr_el0", 368) \
  X("tpidr_el1", 376) X("tpidrro_el0", 384) X("contextidr_el1", 392) \
  X("cpacr_el1", 400) X("par_el1", 408)

#define HV_LD(r, o) "  ldr x2, [x0, #" #o "]\n  msr " r ", x2\n"
#define HV_ST(r, o) "  mrs x1, " r "\n  str x1, [x0, #" #o "]\n"

#define HV_SAVE(kind) \
  "  str x0, [sp, #-16]!\n" \
  "  mrs x0, tpidr_el2\n" \
  "  stp x1, x2, [x0, #8]\n" \
  "  stp x3, x4, [x0, #24]\n" \
  "  stp x5, x6, [x0, #40]\n" \
  "  stp x7, x8, [x0, #56]\n" \
  "  stp x9, x10, [x0, #72]\n" \
  "  stp x11, x12, [x0, #88]\n" \
  "  stp x13, x14, [x0, #104]\n" \
  "  stp x15, x16, [x0, #120]\n" \
  "  stp x17, x18, [x0, #136]\n" \
  "  stp x19, x20, [x0, #152]\n" \
  "  stp x21, x22, [x0, #168]\n" \
  "  stp x23, x24, [x0, #184]\n" \
  "  stp x25, x26, [x0, #200]\n" \
  "  stp x27, x28, [x0, #216]\n" \
  "  stp x29, x30, [x0, #232]\n" \
  "  ldr x1, [sp], #16\n" \
  "  str x1, [x0]\n" \
  HV_ST("sp_el1", 248) HV_ST("sp_el0", 256) HV_ST("elr_el2", 264) \
  HV_ST("spsr_el2", 272) HV_SYS(HV_ST) HV_ST("esr_el2", 416) \
  HV_ST("far_el2", 424) HV_ST("hpfar_el2", 432) \
  "  mov w0, #" #kind "\n" \
  "  b hv_exit\n"

__asm__(
  ".text\n"
  ".global hv_enter\n"
  "hv_enter:\n"
  "  stp x29, x30, [sp, #-16]!\n"
  "  stp x27, x28, [sp, #-16]!\n"
  "  stp x25, x26, [sp, #-16]!\n"
  "  stp x23, x24, [sp, #-16]!\n"
  "  stp x21, x22, [sp, #-16]!\n"
  "  stp x19, x20, [sp, #-16]!\n"
  "  mov x2, sp\n"
  "  str x2, [x1]\n"
  "  msr tpidr_el2, x0\n"
  HV_LD("sp_el1", 248) HV_LD("sp_el0", 256) HV_LD("elr_el2", 264)
  HV_LD("spsr_el2", 272) HV_SYS(HV_LD)
  "  ldp x2, x3, [x0, #16]\n"
  "  ldp x4, x5, [x0, #32]\n"
  "  ldp x6, x7, [x0, #48]\n"
  "  ldp x8, x9, [x0, #64]\n"
  "  ldp x10, x11, [x0, #80]\n"
  "  ldp x12, x13, [x0, #96]\n"
  "  ldp x14, x15, [x0, #112]\n"
  "  ldp x16, x17, [x0, #128]\n"
  "  ldp x18, x19, [x0, #144]\n"
  "  ldp x20, x21, [x0, #160]\n"
  "  ldp x22, x23, [x0, #176]\n"
  "  ldp x24, x25, [x0, #192]\n"
  "  ldp x26, x27, [x0, #208]\n"
  "  ldp x28, x29, [x0, #224]\n"
  "  ldr x30, [x0, #240]\n"
  "  ldp x0, x1, [x0]\n"
  "  eret\n"
  "hv_exit:\n"
  "  ldr x1, =__persist_start\n"
  "  ldr x2, [x1]\n"
  "  mov sp, x2\n"
  "  ldp x19, x20, [sp], #16\n"
  "  ldp x21, x22, [sp], #16\n"
  "  ldp x23, x24, [sp], #16\n"
  "  ldp x25, x26, [sp], #16\n"
  "  ldp x27, x28, [sp], #16\n"
  "  ldp x29, x30, [sp], #16\n"
  "  ret\n"
  "hv_exit_sync:\n"
  HV_SAVE(0)
  "hv_exit_irq:\n"
  HV_SAVE(1)
  "hv_exit_other:\n"
  HV_SAVE(2)
  "hv_own:\n"
  "  mrs x0, esr_el2\n"
  "  mrs x1, elr_el2\n"
  "  mrs x2, far_el2\n"
  "  b bare_fault\n"
  ".balign 2048\n"
  ".global hv_vectors\n"
  "hv_vectors:\n"
  ".rept 8\n"
  "  b hv_own\n"
  ".balign 128\n"
  ".endr\n"
  "  b hv_exit_sync\n"
  ".balign 128\n"
  "  b hv_exit_irq\n"
  ".balign 128\n"
  "  b hv_exit_other\n"
  ".balign 128\n"
  "  b hv_exit_other\n"
  ".balign 128\n"
  ".rept 4\n"
  "  b hv_exit_other\n"
  ".balign 128\n"
  ".endr\n"
);

extern u64 hv_enter(HvArea* area, u64* host_sp);
extern char hv_vectors[];

// Words
// -----
// a List<U32> crosses as its words

static u32 hv_words(Env e, Term s, u32* out, u32 cap) {
  u32 n = 0;
  while (term_aux(s) == CID(Con)) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    if (n < cap) {
      out[n] = (u32)fb[0];
    }
    n += 1;
    s = fb[1];
  }
  return n < cap ? n : cap;
}

static Term hv_list(Env e, const u32* in, u32 n) {
  Term xs = term_pak(CID(Nil), 0);
  for (u32 i = n; i > 0; i -= 1) {
    xs = io_node(e, CID(Con), (Term)in[i - 1], xs);
  }
  return xs;
}

// Gic
// ---
// the EL2 timer interrupt over GICv3: the distributor, this core's
// redistributor, and the system register interface

static void hv_gic_init(void) {
  hv_w32(GICD, hv_r32(GICD) | 0x13);
  hv_w32(GICR + 0x14, hv_r32(GICR + 0x14) & ~2u);
  while (hv_r32(GICR + 0x14) & 4) {
  }
  hv_w32(GICR_SGI + 0x80, 0xFFFFFFFFu);
  hv_w32(GICR_SGI + 0x100, 1u << HV_TIMER);
  hv_w32(GICR_SGI + 0x400 + (HV_TIMER & ~3u), 0x80808080u);
  HV_WR(ICC_SRE_EL2, 0xF);
  __asm__ volatile("isb");
  HV_WR(ICC_PMR_EL1, 0xFF);
  HV_WR(ICC_IGRPEN1_EL1, 1);
  __asm__ volatile("isb");
}

// Instance
// --------
// counts the instances since init; main calls it first, so this file is
// spliced first and hv.c sees its names

Term hv_instance_run(Env e, Term* f, IoWork* w) {
  if (HV->magic == HV_MAGIC) {
    HV->instances += 1;
  }
  return (Term)(HV->magic == HV_MAGIC ? HV->instances : 0);
}

static void __attribute__((constructor)) hv_instance_use(void) {
  io_eff(CID(Hv.instance), hv_instance_run, 0);
}
