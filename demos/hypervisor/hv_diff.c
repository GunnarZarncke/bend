// hypervisor: the effects only diff.bend uses, spliced after hv.c: the
// guest set Hv.init loads, and the area as the last exit saved it.

// Select
// ------

Term hv_select_run(Env e, Term* f, IoWork* w) {
  hv_set = (u32)f[0] < 2 ? (u32)f[0] : 0;
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) hv_select_use(void) {
  io_eff(CID(Hv.select), hv_select_run, 0);
}

// Snap
// ----
// the area as the last exit saved it, before hv.c adjusts it: 55
// registers (x0..x30, sp_el1, sp_el0, elr, spsr, the 17 EL1 registers,
// esr, far, hpfar), high half first. diff.sh compares it with Isa.bend's.

Term hv_snap_run(Env e, Term* f, IoWork* w) {
  u64* r = (u64*)&HV->snap;
  u32  out[110];
  for (u32 i = 0; i < 55; i += 1) {
    out[2 * i]     = (u32)(r[i] >> 32);
    out[2 * i + 1] = (u32)r[i];
  }
  return hv_list(e, out, 110);
}

static void __attribute__((constructor)) hv_snap_use(void) {
  io_eff(CID(Hv.snap), hv_snap_run, 0);
}
