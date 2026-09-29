# Bend Hypervisor: the plan

Five workstreams, in the order they should run. The first two change the
Bend side only; the third builds a machine semantics; the last two need
hardware. Each ends in something the gates can check. Throughout, the
laws in LAWS.bend are the human's: every workstream below that states a
law leaves the statement to be written or rewritten by hand, and the AI
fills the proof.

## 1. The model in Bend's idioms

Goal: the machine is an affine `Type` with arrays and machine words, so
the model reads as Bend and runs as Bend, and the proofs stay short.

1. `Machine{pages: Array<Owner>, vcpus: Array<VCpu>, cur: U32}` as a
   `Type`; guest ids `U32` (the VMID the hardware sees). The kernel
   threads the machine through, never copies it. `Kernel` stays `Data`.
2. A lemma library the proofs need and Base lacks, as `demos/hypervisor/
   Lemmas.bend` for now, offered to Base later:
   - `U32.is_eq(a, b) == True{}` implies `a == b`, and its converse;
   - `Array.get` after `Array.set` at the same index, and at another
     index (the frame lemma over the array's tree, by induction on the
     depth and the index's bits);
   - `Array.map`-style walks preserve size.
3. Re-prove `masks_disjoint` and `handle_frame` over the new model. The
   frame proof changes shape: `vcpu_map` becomes `Array.set` of an
   `Array.get`, and the affine machine must be matched apart and rebuilt
   in every lemma.
4. The record: `encode` walks the arrays; `decode` builds them with
   `Array.new` and `Array.set`. State the round trip as a law over machines
   whose ids and sizes fit a word.
5. The simulator and bare.bend follow; the drivers do not change shape.

Done when: `bend PROOF.bend --verdict` prints ALL PROOFS CHECK on the
array model, `run.sh` passes, and main.bend's log is unchanged.

Risk: proofs over `Array`'s tree may be slow in the checker or long in
text. If so, keep a list model as the specification and prove the array
model refines it (one lemma per accessor), rather than proving the laws
twice.

## 2. Noninterference

Goal: the theorem the two current laws are lemmas of, stated over traces
and proved.

1. A trace semantics in Bend. A trace is a list of exits; a run folds
   `handle` over it from a boot state. The guest step stays outside the
   model: the trace is the hypothesis. This matches the simulator, so the
   simulator becomes the reference implementation of the semantics.
2. The statement, in the human's words. The candidate that is true:
   for a guest `a`, the sequence of `a`'s saved windows and live bit along
   a run is a function of the sequence of `a`'s own exits. Timing is
   excluded on purpose: when `a` runs depends on the others through the
   schedule, and that is allowed.
3. The proof, a two-run argument: two traces with the same projection
   onto `a` keep `a`'s vCPU equal at every step. The induction needs
   - `handle_frame` (have it): another guest's exit leaves `a` alone;
   - `handle_own`: `a`'s exit updates `a`'s vCPU by a function of the
     exit and `a`'s old vCPU only (case analysis on `handle`);
   - `sched_enters_saved`: `Enter{g, r}` carries `r = regs(vcpus[g])`
     (read off `sched.at`);
   - a lemma that the projection of a trace is preserved by the
     cases. Expect a few hundred lines of proof term; the cases are
     mechanical once the statement is right.
4. The handoff: the theorem must hold across instances. With the record
   round trip law of workstream 1, a run over instances is a run over the
   concatenated trace, and the theorem lifts.
5. State the hardware axiom as a Bend `law` with no def, so it is visible
   as an open claim: a guest step changes no block outside its map and no
   register outside its file. Workstream 3 is what would fill it.

Done when: LAWS.bend states the theorem and the axiom; PROOF.bend proves
the theorem; `--verdict` agrees.

## 3. Verifying the assembly

Goal: the trap shim, the context switch and the guest-step axiom become
theorems about a machine semantics, in the manner of seL4's binary
verification but on three hundred words rather than ten thousand lines.

1. An ARM64 subset semantics in Bend, `Isa.bend`: a state (general
   registers, the system registers the shim touches, PSTATE, the current
   exception level, memory as a map from block to bytes plus the
   ownership list, the stage-2 map), and a step function over the
   instruction forms the shim uses (about forty: loads and stores, pairs,
   moves, branches, `mrs`/`msr`, `eret`, `hvc`, `wfi`, barriers), plus
   exception entry (the vector offset, ESR, ELR, SPSR, FAR, HPFAR) and
   the stage-2 walk with its faults. This is the trusted spec of the
   hardware from then on; keep it small and test it (step 4).
2. The shim as data: gen_guests.sh already assembles guests; the same
   path assembles hv_state.c's `__asm__` blocks into a word list checked
   into a `.bend` file.
3. Theorems: running the semantics from a guest exit through `hv_exit`
   reaches `hv_enter`'s return with the area holding the guest's file and
   the host registers restored; running `hv_enter` from a window reaches
   `eret` with the guest's file loaded; stage-2 walks over a committed
   table map exactly the mask's blocks. The last one discharges the
   axiom of workstream 2 for guest loads, stores and fetches.
4. Differential tests: the same guest traces on QEMU and on the
   semantics, compared word for word at every exit. A gate-shaped check;
   it is also how the semantics earns trust.
5. The C effects: each is a few lines around one instruction. Rewrite
   them in assembly and verify them the same way, or keep them in C and
   wait for the Bend-in-Bend compiler's preservation theorem to cover
   them along with the runtime. Assembly first: it needs no compiler
   theorem.

Done when: the axiom's def is filled from `Isa.bend`, and the
differential harness passes.

Risk: exception and translation semantics are where an ISA model goes
wrong. Model only what the shim exercises, and let the differential
tests decide what to add.

## 4. Real ARM64

Goal: the same image on a board, not only QEMU.

1. A VM with nested virtualization on an M3 or later Mac (macOS 15 and
   later offer it with GICv3): EL2 under a hypervisor, the same UART and
   timer code, no board bring-up. Verify it on an M4 mini so the gate's
   cluster can run the QEMU-free lane.
2. A board with EL2 at boot and a GICv3: a Jetson Orin (GIC-600) is the
   candidate; the Raspberry Pi 4 and 5 have a GIC-400, so they need a
   GICv2 path (CPU interface over MMIO) or a different board. Per board:
   the UART, the GIC base addresses, the RAM map from the device tree
   into build.sh's linker script, and a boot that the firmware accepts.
3. Multi-core: PSCI `CPU_ON` for the workers, per-core stacks and
   vectors, and the runtime's pool over spinning cores (the pthread
   stubs become real). The model gains a core index; the schedule law
   must say which core a guest may run on.
4. A watchdog as the hard time bound, and the handoff made
   crash-consistent against it (the two-slot record already is).

Done when: run.sh's checks pass on the VM and on one board, and the test
gate has a lane for it.

## 5. GPU

Goal: a `!` program runs on a GPU under the hypervisor's isolation.

The hypervisor stays CPU-only: a separation kernel should carry no driver
stack. The GPU belongs to one guest, a Linux guest, and Bend's Metal or
CUDA lane runs inside it. What that needs, in order:

1. Device passthrough in the model: an `Owner` for MMIO ranges, stage-2
   entries with device attributes, and the law extended to say a device's
   registers belong to one guest.
2. Interrupts to guests: GICv3 SPIs routed as virtual interrupts (the
   list registers, `ICH_*`), so the guest's driver sees its GPU.
3. DMA isolation: the SMMU's stage-2 tables, or the separation law is
   false the moment the GPU writes memory. This is the hard part, and the
   place the axiom must be extended to a device's accesses.
4. A Linux guest: device tree, PSCI for its cores, a virtio console; the
   EL1 system register set the shim saves already covers it.
5. Hardware: a Jetson (NVIDIA GPU, CUDA) is the only ARM64 board that
   fits Bend's GPU lanes; Apple's GPU is not reachable from a guest.

Done when: a Bend program with `!` in the Linux guest prints the same as
on the host, while a second guest runs beside it and the laws still
check. QEMU cannot stand in for any of this.

## Order and dependencies

1 then 2 are the proofs, and 2 waits for 1's model. 3 is independent of
both and can start now; its axiom closes 2's open claim later. 4 follows
1 and 3 loosely, since a board changes nothing in the model. 5 needs 4's
multi-core and interrupt work and is the last. If effort is short, do 1
and 2 in full, start 3's semantics with the differential harness, and
take 4's VM step; 4's board and all of 5 are separable.
