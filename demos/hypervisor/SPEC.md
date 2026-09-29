# Bend Hypervisor: a separation kernel on ARM64

The kernel is a pure Bend function over a machine model (main.bend). The
hardware is reached only through actions, which two drivers consume: a
simulator in Bend, and bare.bend, which applies them through effects at
EL2 on QEMU. Every instance handles a bounded number of exits and hands
its state to the next. LAWS.bend states two isolation laws; PROOF.bend
proves them, and the BendTT kernel confirms the proofs (`--verdict`).

    bend demos/hypervisor/main.bend            the simulator on a trace
    bend demos/hypervisor/PROOF.bend --verdict the laws
    sh demos/hypervisor/run.sh                 the real thing on QEMU
    sh demos/hypervisor/build.sh x.bend x.elf  any program, on the bare lane

## 1. Scope

- Target: ARM64 at EL2 on QEMU virt (cortex-a72, GICv3, 2 GiB), one
  core, stage-2 translation, the EL2 physical timer, a PL011 UART. No
  other devices, no DMA, no PSCI, no secondary cores.
- Guests: N bare-metal guests at EL1 with the MMU off, one vCPU each, a
  static partition of 2 MiB blocks, no shared blocks and no channels.
  They talk to the kernel by hypercall: `hvc #0` yields, `hvc #1` prints
  x0 as a character, `hvc #2` quits; anything else answers x0 = 2^32-1.
- Scheduling: round-robin on a timer slice; a yield or a stop moves the
  core on at once.
- Not in scope: Xen's ABI, Linux guests, device passthrough, dynamic
  memory, verifying the checker, the compiler, clang, or the runtime.

## 2. Trust model

Proved in Bend over the model: the two laws of section 7.

Assumed, as the one hardware axiom: a guest at EL1 under a stage-2 map
and a saved register file changes no block it is not mapped to and no
register outside its own file.

Trusted, not proved: the model's fidelity to ARM64; the C in hv_state.c
and hv.c (about 500 lines: the trap vectors, the context switch, the
tables, the GIC and timer, the handoff slots, the guest images); the boot
and the lane itself: bare.c, boot.c and build.sh; the Bend checker,
compiler, runtime and clang. The kernel has no `@unsafe` def. Liveness is
not proved.

## 3. Machine model

Ownership is modeled per block, not memory contents: isolation needs only
who may touch a block. Sizes are small, so lists serve where arrays would;
Bend has no 64-bit word, so `W64{hi, lo}` holds a register.

```
type Owner   is Data:  Free{}  Hyp{}  Of{g: Nat}
type Regs    is Data:  Regs{x0: W64, x1: W64, x2: W64, x3: W64, pc: W64}
type VCpu    is Data:  VCpu{regs: Regs, live: Bool}
type Machine is Data:  Machine{pages: List<Owner>, vcpus: List<VCpu>, cur: Nat}
```

`Regs` is the hypercall window: the registers the kernel reads and
writes. The rest of a guest's register file (x4..x30, both stacks, SPSR,
17 EL1 system registers) is saved and restored per guest by the trap
shim, and the kernel never sees it.

Three step relations, of which only the second is code:

1. Guest step: `cur` runs at EL1 until an exit. Opaque; bounded by the
   axiom.
2. Exit step: `handle(k, m, e)` answers a `Step`: `Go{k, m, acts}`, whose
   actions end in `Enter`, or `Fin{k, m, acts}`, whose end in `End`.
3. Handoff: the instance ends; the record is written; the next instance
   starts from it (section 6).

## 4. Exits and actions

```
type Exit is Data:
  Timer{regs}  Hvc{imm: U32, regs}  DataAbort{ipa: W64, write: Bool, regs}
  InstAbort{ipa: W64, regs}  Wfi{regs}  Fault{esr: W64, regs}

type Action is Data:
  Commit{g: Nat}          # the stage-2 map of g, from the ownership list
  Arm{us: U32}            # the EL2 timer, this many microseconds out
  Stop{g: Nat}            # g never runs again
  Print{s: String}        # the UART
  Enter{g: Nat, regs: Regs}   # ERET into g with this window; answers an Exit
  End{}                   # no guest is live
```

Every exit carries the window at the exit. `Enter` is always the last
action of a `Go` and answers the next `Exit`; in the simulator the trace
supplies it, on the board the trap shim does. A handler that needs a
transition the model lacks extends `Action` first, so the proofs see it.

## 5. Kernel

```
type Kernel is Data:  Kernel{n: Nat, next: Nat, slice: U32}
def handle(k: Kernel, m: Machine, e: Exit) -> Step
```

`handle` first saves the exit's window into `vcpus[cur]`, then:

- `Timer`, `Wfi`, `Hvc 0`: `sched`, the next live guest from `next` on,
  wrapping: `[Commit{g}, Arm{slice}, Enter{g, regs of g}]`, and `next`
  moves past g; no live guest gives `Fin{.., [End{}]}`.
- `Hvc 1`: `[Print{x0 as a character}, Enter{cur, window with x0 = 0}]`,
  no new slice.
- `Hvc 2`, `DataAbort`, `InstAbort`, `Fault`: `cur` is marked dead, then
  `Stop{cur}` before the actions of `sched`.
- Other `Hvc`: `Enter{cur, window with x0 = 2^32-1}`.

There is no emulation and no lazy mapping: the tables are complete at
the first `Commit` of a guest.

## 6. Instances, fuel, handoff

An instance is one run of `main` in bare.bend: read the newer handoff
slot, decode it (or, on the first boot, build the machine and init the
hardware), then loop: drive the pending decision's actions, take the exit
`Enter` answers, `handle`, until the fuel of 12 exits is spent. Then the
pending decision is settled (its prints and stops run, its `Enter` does
not), the record is stored, and the boot is asked for another instance.
The boot (boot.c) zeroes .bss, runs the init array and calls
`bend_main` again: a fresh runtime heap over the same persist region.
When a decision is `Fin`, main returns without asking, and QEMU exits.

The record is `encode(k, m)`: six header words (n, next, slice, cur, the
two list lengths), one word per block owner, eleven per vCPU (the window
as ten halves, the live bit). It lives in the persist region in two slots
with a generation counter: a store fills the idle slot, then bumps its
generation; a load takes the higher one. Guest registers are saved by the
trap shim on every exit, so a fail-stop mid-instance loses no guest work,
only the handled exits since the last store.

Fuel counts exits, not time. A hard time bound would be a watchdog; none
is wired.

## 7. Laws

Both are stated in LAWS.bend over main.bend and proved in PROOF.bend.

- `masks_disjoint`: for every ownership list and two distinct guests, the
  stage-2 masks the kernel commits share no block. Proved by induction on
  the list, with a soundness lemma for `Nat.is_eq`.
- `handle_frame`: whatever exit the current guest takes, every other
  guest's saved window and live bit are what they were. Proved by a frame
  lemma on the vCPU list and one lemma per branch of `handle`; the
  scheduler and `prepend` are shown to keep every vCPU.

Together with the axiom, these are the unwinding conditions of
noninterference for the exit and guest steps: a guest's registers and
blocks depend on its own steps and on the fixed schedule, never on another
guest's. Not stated as laws, and read from the code instead: `Enter{g, r}`
takes `r` from `vcpus[g]` alone (`sched.at`), and a `Commit{g}` reads only
the ownership list. The record round trip is tested by the simulator, not
proved.

## 8. Drivers and effects

The simulator (`sim` in main.bend) applies actions to the model and takes
each guest step from a trace; its log is the demo's output. The real
driver (bare.bend) applies them through these effects:

| Effect | Does |
|---|---|
| `Hv.init(n)` | loads the guest images, installs the vectors, HCR and VTCR, sets up the GIC |
| `Hv.commit(g, mask)` | writes g's level-2 table from the mask, sets VTTBR (VMID g+1), flushes |
| `Hv.arm(us)` | arms CNTHP_EL2 |
| `Hv.enter(g, window)` | restores g, ERETs, and answers the exit as fifteen words |
| `Hv.load()`, `Hv.store(words)` | the handoff slots |
| `Hv.again()` | asks the boot for one more instance |
| `Hv.instance()` | counts the instances; main's first call, so hv_state.c splices first |

`Print` is `IO.write`. hv_state.c holds the state (in the persist
region), the vector table, the context switch and the GIC setup; hv.c the
guests and the effects. The guest images are assembled by gen_guests.sh
and pasted as words.

## 9. Hardware facts

- Memory (QEMU virt, RAM at 1 GiB): the image at 0x40080000, the runtime
  arena 1 GiB at 0x48000000, the persist region 16 MiB at 0x90000000, the
  term stack 32 MiB below the top of RAM. Block b is 2 MiB at
  0xA0000000 + b·2 MiB; blocks 0..7 are the hypervisor's (never mapped),
  guest g owns blocks 8+8g .. 15+8g and starts at their base.
- Stage 2: VTCR_EL2 0x23560 (32-bit IPA, start at level 1); a level-1
  table of four 1 GiB entries, of which the third points at a level-2
  table of 2 MiB blocks; identity mapping, normal write-back memory.
- HCR_EL2: VM, IMO, FMO, AMO, TWI, TSC, RW. WFI and SMC trap.
- Timer: CNTHP_EL2, PPI 26 through GICv3 (distributor, this core's
  redistributor, the system register interface); the IRQ vector disables
  the timer, EOIs, and answers `Timer`.
- Exit decoding: ESR.EC 0x16 `Hvc` (imm from ISS), 0x24 `DataAbort`
  (IPA from HPFAR and FAR, write from WnR), 0x20 `InstAbort`, 0x01 `Wfi`
  (ELR advances past the WFI), anything else `Fault`.

## 10. The bare lane

`sh demos/hypervisor/build.sh x.bend x.elf` builds any Bend program
without `!` for EL2 on QEMU. The lane lives in the demo: bare.c is the
host the runtime calls in place of an OS (the UART streams, semihosting
exit, a bump heap, the string functions, and the memory and signal calls
as the runtime makes them, so its own pool and corpus code runs unchanged
over the linker's regions); boot.c is the MMU, the default vectors,
`bend_main`, `_start`, and the event loop without descriptors; build.sh
holds the linker script and the clang and lld invocation. The compiler
keeps only a lane hook, some forty lines that know nothing of ARM64:
`-DBEND_LANE='"x.c"'` names a file it includes after its types and again
at its end, and its host-only code (float text, sockets, the descriptor
event loop, the host `main`) is guarded out. Limits: one core; no float
text; a blocking effect runs inline; a descriptor wait fail-stops; the
bump heap frees nothing until the next instance. A deep recursion runs off
the term stack into unbacked space and is reported as such.

## 11. Testing

- `bend demos/hypervisor/main.bend` prints the simulator's log for a trace
  of three guests, the masks, and the record size.
- `bend demos/hypervisor/PROOF.bend --verdict` prints ALL PROOFS CHECK.
- `sh demos/hypervisor/run.sh` builds the ELF, boots it, and checks: A and
  B print three letters, C two, D one and is stopped by its abort; the
  timer preempts C at least once; at least one handoff; every guest stops
  once; a clean halt. Timer counts vary run to run; letters do not.

## 12. Open items

- The model has no clock, so the timer's fairness is not a law.
- A handoff is a full stop of every guest for the restart's duration.
- Multi-core, a watchdog, real hardware, and a guest with its own stage-1
  tables are untested paths through the same design.
- The Bend-in-Bend compiler will change what is trusted in section 2, not
  the model, the laws, or the effect table.
