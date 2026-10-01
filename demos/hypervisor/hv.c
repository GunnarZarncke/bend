// hypervisor: the EL2 shim, part two: the test guests and the effects
// init, commit, arm, enter, the handoff (load, store) and again. The
// state, the switch and the helpers are in hv_state.c, spliced before it.

// Guests
// ------
// the test guests: A and B print their letter three times, yielding
// between; C prints, spins, prints, quits; D prints, then writes a block
// it does not own. Assembled by gen_guests.sh.

static const u32 hv_guest_a[] = { 0xd2800073, 0xd2800820, 0xd4000022,
  0xd4000002, 0xf1000673, 0x54ffff81, 0xd4000042, 0x14000000 };
static const u32 hv_guest_b[] = { 0xd2800073, 0xd2800840, 0xd4000022,
  0xd4000002, 0xf1000673, 0x54ffff81, 0xd4000042, 0x14000000 };
static const u32 hv_guest_c[] = { 0xd2800860, 0xd4000022, 0xd2a08013,
  0xf1000673, 0x54ffffe1, 0xd2800860, 0xd4000022, 0xd4000042, 0x14000000 };
static const u32 hv_guest_d[] = { 0xd2800880, 0xd4000022, 0xd2a80000,
  0xf9000000, 0xd2800880, 0xd4000022, 0xd4000042, 0x14000000 };

// set 1, diff.sh's: every instruction form Isa.bend models, WFI, a read
// of a block not owned, a branch out of the guest's blocks
static const u32 hv_guest_e0[] = { 0xd28000a1, 0xd2800002, 0x91000c42,
  0xf1000421, 0x54ffffc1, 0xaa0203e0, 0x9100c800, 0xd4000022, 0xd2bfffe3,
  0x11000464, 0x6b040085, 0x54000040, 0xd4000122, 0xd40000e2, 0xf1000406,
  0x54000044, 0xd4000122, 0xd28008a0, 0xd4000022, 0xd29fe008, 0xf2a24688,
  0xf2d579a8, 0xf2e000e8, 0xd368fd09, 0xd35f792a, 0x8a08014b, 0xd347fd0c,
  0xd37df18d, 0x8a0a01ae, 0x53057d0f, 0x531759f0, 0x0a080211, 0xaa1101d2,
  0xd4000002, 0xd2a80007, 0xf90004e7, 0x14000000 };
static const u32 hv_guest_e1[] = { 0x910003f4, 0xd2824681, 0xd28acf02,
  0xa9bf0be1, 0xf81f8fe1, 0xf84087e3, 0xa8c117e4, 0xd1010295, 0xf90002a5,
  0xf90006a4, 0xf94006a6, 0xa94022a7, 0xf8010ea1, 0xf85f06a9, 0xa90226a3,
  0x910000c0, 0xd1400400, 0xd1079c00, 0xd4000022, 0xd2b5000a, 0xf940014b,
  0xd4000042, 0x14000000 };
static const u32 hv_guest_e2[] = { 0xd2822221, 0xd518d081, 0xd2844442,
  0xd51bd042, 0xd51bd062, 0xd518d021, 0xd2860003, 0xd518c003, 0xd5186002,
  0xd5185201, 0xd518a202, 0xd538d084, 0xd53bd045, 0x8b050086, 0xd2800a60,
  0xd4000022, 0xd503207f, 0xd2800ae0, 0xd4000022, 0xd4000042, 0x14000000 };
static const u32 hv_guest_e3[] = { 0xd2800920, 0xd4000022, 0x15000000,
  0xd4000042 };

static const u32* hv_guests[2][4] = {
  { hv_guest_a, hv_guest_b, hv_guest_c, hv_guest_d },
  { hv_guest_e0, hv_guest_e1, hv_guest_e2, hv_guest_e3 } };
static const u32 hv_guest_len[2][4] = { { 8, 8, 9, 8 }, { 37, 23, 21, 4 } };


// guest g's first block: the 8 hypervisor blocks, then 8 per guest
static u64 hv_guest_pa(u32 g) {
  return HV_BASE + (8 + 8 * (u64)g) * HV_BLOCK;
}

static void hv_guest_load(u32 g) {
  u64  pa   = hv_guest_pa(g);
  u32* code = (u32*)(uintptr_t)pa;
  u32  n    = g < 4 ? hv_guest_len[hv_set][g] : 0;
  for (u32 i = 0; i < n; i += 1) {
    code[i] = hv_guests[hv_set][g][i];
  }
  if (n == 0) {
    code[0] = 0xd4000042;   // hvc #2: a guest with no program quits
  }
  __asm__ volatile("dsb ish\n\tic iallu\n\tdsb ish\n\tisb" : : : "memory");
  HvArea* a = &HV->area[g];
  memset(a, 0, sizeof *a);
  a->elr    = pa;
  a->sp_el1 = pa + (1 << 20);
  a->spsr   = 0x3C5;          // EL1h, interrupts masked at EL1
}

// Init
// ----

Term hv_init_run(Env e, Term* f, IoWork* w) {
  u32 n = (u32)f[0];
  if (n > HV_GUESTS) {
    err_fail("too many guests");
  }
  memset(HV, 0, sizeof(HvState) - sizeof(HvTables) * HV_GUESTS);
  HV->magic  = HV_MAGIC;
  HV->guests = n;
  for (u32 g = 0; g < n; g += 1) {
    hv_guest_load(g);
    memset(&HV->tab[g], 0, sizeof(HvTables));
    HV->tab[g].l1[HV_L2_GIB >> 30] = (u64)(uintptr_t)HV->tab[g].l2 | 3;
  }
  HV_WR("vbar_el2", (u64)(uintptr_t)hv_vectors);
  HV_WR("vtcr_el2", 0x23560ull);
  HV_WR("hcr_el2", 1ull | (1ull << 3) | (1ull << 4) | (1ull << 5)
    | (1ull << 13) | (1ull << 19) | (1ull << 31));
  __asm__ volatile("isb");
  hv_gic_init();
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) hv_init_use(void) {
  io_eff(CID(Hv.init), hv_init_run, 0);
}

// Commit
// ------
// guest g's level-2 table maps block b at its own address if and only if
// the mask's word b is 1

Term hv_commit_run(Env e, Term* f, IoWork* w) {
  u32 g = (u32)f[0];
  u32 mask[256];
  u32 n = hv_words(e, f[1], mask, 256);
  if (g >= HV->guests) {
    err_fail("commit: no such guest");
  }
  u64* l2 = HV->tab[g].l2;
  for (u32 b = 0; b < 256; b += 1) {
    u64 pa = HV_BASE + b * HV_BLOCK;
    l2[HV_L2_AT + b] = b < n && mask[b] != 0 ? pa | 0x7FDull : 0;
  }
  HV_WR("vttbr_el2", (u64)(uintptr_t)HV->tab[g].l1 | ((u64)(g + 1) << 48));
  __asm__ volatile("dsb ish\n\ttlbi vmalls12e1is\n\tdsb ish\n\tisb"
    : : : "memory");
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) hv_commit_use(void) {
  io_eff(CID(Hv.commit), hv_commit_run, 0);
}

// Arm
// ---

Term hv_arm_run(Env e, Term* f, IoWork* w) {
  u64 freq;
  HV_RD("cntfrq_el0", freq);
  u64 ticks = (u64)(u32)f[0] * freq / 1000000ull;
  HV_WR(CNTHP_CTL_EL2, 0);
  HV_WR(CNTHP_TVAL_EL2, ticks);
  HV_WR(CNTHP_CTL_EL2, 1);
  __asm__ volatile("isb");
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) hv_arm_use(void) {
  io_eff(CID(Hv.arm), hv_arm_run, 0);
}
// Enter
// -----
// takes the guest and its window (10 words), runs it until an exit, and
// answers the exit as words: kind, esr, far, x0..x3, pc, high half first.
// kind: 0 timer, 1 hvc, 2 data abort, 3 inst abort, 4 wfi, 5 fault

Term hv_enter_run(Env e, Term* f, IoWork* w) {
  u32 g = (u32)f[0];
  u32 win[10];
  u32 n = hv_words(e, f[1], win, 10);
  if (g >= HV->guests || n != 10) {
    err_fail("enter: no such guest, or a short window");
  }
  HvArea* a = &HV->area[g];
  for (u32 i = 0; i < 4; i += 1) {
    a->x[i] = (u64)win[2 * i] << 32 | win[2 * i + 1];
  }
  a->elr = (u64)win[8] << 32 | win[9];
  u64 kind = hv_enter(a, &HV->host_sp);
  HV->snap = *a;
  u64 esr  = a->esr;
  u64 far  = 0;
  u32 k    = 5;
  if (kind == 1) {
    u64 iar;
    HV_RD(ICC_IAR1_EL1, iar);
    if ((iar & 0xFFFFFF) == HV_TIMER) {
      HV_WR(CNTHP_CTL_EL2, 0);
    }
    if ((iar & 0xFFFFFF) < 1020) {
      HV_WR(ICC_EOIR1_EL1, iar);
    }
    k = 0;
  } else if (kind == 0) {
    HvKind d = hv_decide(esr, a->far, a->hpfar, a);
    k   = (u32)d.kind;
    far = d.far;
  }
  u32 out[15] = { k, (u32)(esr >> 32), (u32)esr, (u32)(far >> 32), (u32)far,
    (u32)(a->x[0] >> 32), (u32)a->x[0], (u32)(a->x[1] >> 32), (u32)a->x[1],
    (u32)(a->x[2] >> 32), (u32)a->x[2], (u32)(a->x[3] >> 32), (u32)a->x[3],
    (u32)(a->elr >> 32), (u32)a->elr };
  return hv_list(e, out, 15);
}

static void __attribute__((constructor)) hv_enter_use(void) {
  io_eff(CID(Hv.enter), hv_enter_run, 0);
}

// Handoff
// -------
// load answers the newer slot's words (none before the first store);
// store fills the other slot, then bumps its generation

static HvSlot* hv_newer(void) {
  HvSlot* a = &HV->slot[0];
  HvSlot* b = &HV->slot[1];
  if (HV->magic != HV_MAGIC || (a->gen == 0 && b->gen == 0)) {
    return NULL;
  }
  return a->gen > b->gen ? a : b;
}

Term hv_load_run(Env e, Term* f, IoWork* w) {
  HvSlot* s = hv_newer();
  if (s == NULL) {
    return term_pak(CID(Nil), 0);
  }
  return hv_list(e, s->words, s->len);
}

static void __attribute__((constructor)) hv_load_use(void) {
  io_eff(CID(Hv.load), hv_load_run, 0);
}

Term hv_store_run(Env e, Term* f, IoWork* w) {
  HvSlot* old = hv_newer();
  HvSlot* s   = old == &HV->slot[0] ? &HV->slot[1] : &HV->slot[0];
  s->len = hv_words(e, f[0], s->words, 4094);
  __asm__ volatile("dsb ish" : : : "memory");
  s->gen = (old == NULL ? 0 : old->gen) + 1;
  __asm__ volatile("dsb ish" : : : "memory");
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) hv_store_use(void) {
  io_eff(CID(Hv.store), hv_store_run, 0);
}

// Again
// -----
// asks the boot for one more instance, and counts them

Term hv_again_run(Env e, Term* f, IoWork* w) {
  bare_again = 1;
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) hv_again_use(void) {
  io_eff(CID(Hv.again), hv_again_run, 0);
}
