# Bend Hypervisor: a separation kernel on ARM64

The kernel is a pure Bend function over a machine model (main.bend). The
hardware is reached only through actions, which two drivers consume: a
simulator in Bend, and bare.bend, which applies them through effects at
EL2 on QEMU. Every instance handles a bounded number of exits and hands
its state to the next. LAWS.bend states the isolation laws, among them
noninterference over runs, and the guest-step laws over an ARM64
semantics (Isa.bend) that stand where the hardware axiom stood;
PROOF.bend proves them, and the BendTT kernel confirms the proofs
(`--verdict`). SHIM_LAWS.bend states what the trap shim's assembly does,
over the same semantics; diff.sh checks the semantics against QEMU.

    bend demos/hypervisor/main.bend              the simulator on a trace
    bend demos/hypervisor/PROOF.bend --verdict   the laws
    bend demos/hypervisor/SHIM_PROOF.bend        the shim's laws
    sh demos/hypervisor/run.sh                   the real thing on QEMU
    sh demos/hypervisor/diff.sh                  Isa.bend against QEMU
    sh demos/hypervisor/gate.sh                  all of the above
    sh demos/hypervisor/build.sh x.bend x.elf    any program, on the bare lane

## 1. Scope

- Target: ARM64 at EL2 on QEMU virt (cortex-a72, GICv3, 2 GiB), one
  core, stage-2 translation, the EL2 physical timer, a PL011 UART. No
  other devices, no DMA, no PSCI, no secondary cores.
- Guests: up to four bare-metal guests at EL1 with the MMU off, one vCPU
  each, a static partition of 2 MiB blocks, no shared blocks and no
  channels.
  They talk to the kernel by hypercall: `hvc #0` yields, `hvc #1` prints
  x0 as a character, `hvc #2` quits; anything else answers x0 = 2^32-1.
- Scheduling: round-robin on a timer slice; a yield or a stop moves the
  core on at once.
- Not in scope: Xen's ABI, Linux guests, device passthrough, dynamic
  memory, verifying the checker, the compiler, clang, or the runtime.

## 2. Trust model

Proved in Bend, and confirmed by the BendTT kernel: the laws of section 7
over the model; the three guest-step laws over Isa.bend, which were the
hardware axiom (a guest at EL1, in one step, changes no memory outside
its stage-2 map, no system register but its own and those an exception
entry to EL2 writes, and not its stage-2 map); and the shim's laws of
section 13: the context switch, the save paths and the exit decoding of
hv_state.c, run as words on Isa.bend. The kernel evaluates an open term lazily and without
sharing, and one def may spend only its fuel, so it checks a symbolic
run of about 17 steps and the shim's paths are 68 and 80: each path is
cut into segments that each start from a state written out. Section 14
says what that took.

Trusted, not proved: 

* Isa.bend's fidelity to ARM64, which diff.sh tests against QEMU exit by exit (section 13); 
* the stage-2 map read as the mask (the level-2 descriptors hv_commit_run writes are not modeled); 
* the C of hv_state.c and hv.c outside the shim (about 400 lines: 
* the tables, the GIC and timer, the handoff slots, the guest images);
* the boot and the lane itself: bare.c, boot.c and build.sh; 
* the Bend checker, compiler, runtime and clang. 

The kernel has no `@unsafe` def. Liveness is not proved.

## 3. Machine model

Ownership is modeled per block, not memory contents: isolation needs only
who may touch a block. Bend has no 64-bit word, so `W64{hi, lo}` holds a
register. A guest is its vCPU's slot, a `U32` (the VMID less one).

```
type Owner   is Data:  Free{}  Hyp{}  Of{g: U32}
type Regs    is Data:  Regs{x0: W64, x1: W64, x2: W64, x3: W64, pc: W64}
type VCpu    is Data:  VCpu{regs: Regs, live: Bool}
type Tree<A> is Data:  Leaf{x: A}  Node{lo: Tree<A>, hi: Tree<A>}
type Machine is Type:  Machine{pages: Tree<Owner>, vcpus: Array<VCpu>, cur: U32}
```

The sizes are fixed: 64 blocks (a full tree of depth 6) and four vCPU
slots (an array of depth 2); `Machine.ok` says so, and that every owner
and the core name a slot. The vCPUs change on every exit, so they are an
affine `Array`, updated in place: a set of a get. The partition never
changes and every decision reads it, so it is a Data tree, shared rather
than threaded. Past four guests the laws need Array lemmas for any depth
(an index's bits against the tree), which Base lacks.

`Regs` is the hypercall window: the registers the kernel reads and
writes. The rest of a guest's register file (x4..x30, both stacks, SPSR,
17 EL1 system registers) is saved and restored per guest by the trap
shim, and the kernel never sees it.

Three step relations, of which only the second is code:

1. Guest step: `cur` runs at EL1 until an exit. Isa.bend's `step`; the
   guest-step laws bound it.
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
  Commit{g: U32}          # the stage-2 map of g, from the ownership tree
  Arm{us: U32}            # the EL2 timer, this many microseconds out
  Stop{g: U32}            # g never runs again
  Print{s: String}        # the UART
  Enter{g: U32, regs: Regs}   # ERET into g with this window; answers an Exit
  End{}                   # no guest is live
```

Every exit carries the window at the exit. `Enter` is always the last
action of a `Go` and answers the next `Exit`; in the simulator the trace
supplies it, on the board the trap shim does. A handler that needs a
transition the model lacks extends `Action` first, so the proofs see it.

## 5. Kernel

```
type Kernel is Data:  Kernel{n: U32, next: U32, slice: U32}
def handle(k: Kernel, m: Machine, e: Exit) -> Step
```

`handle` first steps `vcpus[cur]` by `VCpu.step(v, e)`, a function of
the exit and that vCPU alone: the exit's window is saved; a put answers
x0 = 0 and an unknown call x0 = 2^32-1; a quit or a fault clears the live
bit. Then it decides:

- `Timer`, `Wfi`, `Hvc 0`: `sched`, the first live slot of the four from
  `next` on, wrapping: `[Commit{g}, Arm{slice}, Enter{g, regs of g}]`, and
  `next` moves past g; no live guest gives `Fin{.., [End{}]}`.
- `Hvc 1`: `[Print{x0 as a character}, Enter{cur, regs of cur}]`, no new
  slice.
- `Hvc 2`, `DataAbort`, `InstAbort`, `Fault`: `Stop{cur}` before the
  actions of `sched`.
- Other `Hvc`: `Enter{cur, regs of cur}`.

Every `Enter` reads the window from the vCPU it enters.

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

The record is `encode(k, m)`: six header words (n, next, slice, cur, 64,
4), one word per block owner, eleven per vCPU slot (the window as ten
halves, the live bit): 114 words. The decoders read full trees of the
given depths back off the words (structurally, where PLAN.md had
`Array.new` and `Array.set`, so the round trip is a law). It lives in the persist region in two slots
with a generation counter: a store fills the idle slot, then bumps its
generation; a load takes the higher one. Guest registers are saved by the
trap shim on every exit, so a fail-stop mid-instance loses no guest work,
only the handled exits since the last store.

Fuel counts exits, not time. A hard time bound would be a watchdog; none
is wired.

## 7. Laws

Stated in LAWS.bend (drafts by the AI, for the human's review), proved
in PROOF.bend with Lemmas.bend, and confirmed by the kernel. The model's
laws assume `Machine.ok`; the boot machines of the simulator and of
bare.bend are shown to meet it (`boot_ok3`, `boot_ok4`).

- `masks_disjoint`: for every ownership tree and two distinct guests, the
  stage-2 masks share no block.
- `handle_frame`: whatever exit the current guest takes, every other
  slot's vCPU is what it was.
- `handle_own`: the current guest's vCPU becomes `VCpu.step` of its old
  one and the exit.
- `handle_ok`, `handle_pages`: a decision keeps the machine well-formed
  and the partition unchanged.
- `sched_enters_saved`, `handle_enters_saved`: a decision's `Enter` names
  the guest it puts on the core, with the window that guest's vCPU holds.
- `record_roundtrip`: `decode_record(encode(k, m))` is `(k, m)`.
- `run_view`: over any trace of exits and handoffs (`run`, section 8),
  guest a's final vCPU is `VCpu.steps` of the exits a took, from its vCPU
  at boot.
- `noninterference`: two runs in which a starts with the same vCPU and
  takes the same exits end with the same vCPU for a, whatever the other
  guests, the timing, the handoffs, or the traces do.
- `guest_step_memory`, `guest_step_registers`, `guest_step_stage2`: the
  hardware axiom, over Isa.bend (section 2).

What a guest observes is its entries (the entry laws: its own vCPU's
window), its own blocks (the guest-step laws and `masks_disjoint`), and
its own register file (saved and restored by the shim: section 13). The
proofs take the vCPU array apart once into its four leaves (an array is
affine even in a proof) and turn a slot into a literal, after which an
access computes; the partition is Data, so a proof may read it freely.

## 8. Drivers and effects

`run` in main.bend is the semantics the laws speak of: it folds the
kernel over a trace of events, an event being an exit of the guest the
last decision entered, or a handoff (the record is encoded, decoded, and
the next instance schedules afresh, as bare.bend's instances do). Its log
holds, per event, the actions before it and the guest on the core. The
simulator (`sim`) renders a run; its log is the demo's output. The real
driver (bare.bend) applies the actions through these effects:

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
and pasted as words: set 0 for run.sh, set 1 for diff.sh. hv_diff.c adds
the two effects only diff.bend uses: `Hv.select(set)` and `Hv.snap()`,
the file the shim saved at the last exit.

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
- `bend demos/hypervisor/SHIM_PROOF.bend --verdict` prints ALL PROOFS
  CHECK: about 12 s for bend2, and about seven minutes for the kernel,
  which is the whole of Segments.bend.
- `sh demos/hypervisor/diff.sh` prints PASS: every action and every saved
  file of guest set 1 agree between QEMU and the model.
- `sh demos/hypervisor/gate.sh` runs all of the above (the simulator
  against the `#|` lines main.bend ends in), and checks that
  shim_words.bend and the guest words of hv.c and model.bend are what
  gen_shim.sh and gen_guests.sh make of their sources now: about seven
  minutes on one machine, almost all of it the kernel on the shim. The repo's gates run tests/ on the cluster under a 30 s
  cap and do not reach the demo.
- `sh demos/hypervisor/run.sh` builds the ELF, boots it, and checks: A and
  B print three letters, C two, D one and is stopped by its abort; the
  timer preempts C at least once; at least one handoff; every guest stops
  once; a clean halt. Timer counts vary run to run; letters do not.

## 12. Open items

- The model has no clock, so the timer's fairness is not a law.
- A handoff is a full stop of every guest for the restart's duration.
- Multi-core, a watchdog, real hardware, and a guest with its own stage-1
  tables are untested paths through the same design.
- The C effects around the shim that remain (the stage-2 tables and the
  GIC) are neither in assembly nor verified: both are MMIO and
  maintenance, which Isa.bend does not model. The exit decoding was the
  third, and is now the shim's own words (section 13).
- The Bend-in-Bend compiler will change what is trusted in section 2, not
  the model, the laws, or the effect table.

## 13. The ARM64 semantics

Isa.bend is the hardware the laws rest on: a state (x0..x30, the pc,
PSTATE's EL, SP select, NZCV and DAIF, the system registers by encoding,
memory as doublewords at 8-aligned addresses, the hypervisor's text as a
rom, and the stage-2
map of the current VMID as the mask), and `step`: fetch (through stage 2
at EL1: an unmapped pc is an instruction abort), decode, execute. The
forms are the shim's and the test guests': MOVZ, MOVK, ADD/SUB
(immediate and register, with flags), ORR and AND (register), LSL and LSR
(immediate, the two aliases of UBFM), B, BL, B.cond, RET, ERET, HVC, WFI,
NOP and barriers, MRS/MSR, LDR/STR (offset, pre- and post-index,
literal), LDP/STP. An access at EL1 goes through stage 2 word by word; an unmapped
word is a data abort (ISS as QEMU gives it: the valid syndrome for a
single register, WnR, the level). Exception entry to EL2 writes ELR,
SPSR, ESR, and for an abort FAR and HPFAR, and goes to VBAR_EL2 + 0x400
(or + 0x480, an IRQ, which Shim.bend enters directly). What it does not
model is a `Stop`: an unknown form, a system register an EL1 guest may
not touch, an exception to EL1.

diff.sh runs guest set 1 under the kernel on QEMU (diff.bend) and on the
semantics (model.bend, which takes the shim's effect from its laws: an
entry loads the file and ERETs, an exit saves the core), and compares
every action and every saved file, 55 registers at each of 14 exits:
arithmetic and flags, every addressing mode, pairs, the EL1 system
registers, a trapped WFI, stage-2 faults at level 1 (a write) and level
2 (a read), and an instruction fault.

gen_shim.sh assembles hv_state.c's `__asm__` block alone, links it at
0x40100000, and writes its words to shim_words.bend. Shim.bend builds the
states the shim's laws start from, every value a variable, and SHIM_LAWS
states them: `shim_enter` (from hv_enter's call, after 68 steps the core
is at the guest's EL and pc with its whole file loaded, and the host's
registers are on its stack), `shim_exit_sync` and `shim_exit_irq` (from
the vector, after 80 steps the file and the syndrome are in the area, the
host's registers are back, and hv_enter returns the kind), and
`shim_decide_*`, one per exception class: hv_decide takes the ESR, the
FAR, the HPFAR and the area in registers, and answers the exit's kind
and, for a stage-2 abort, the address the guest faulted at, which is the
block HPFAR names with the offset FAR holds. The class arm that traps a
guest's own instruction is the one that writes: it steps the guest's ELR
in its area past the instruction, and so it has a law per guest. Each
law assumes its class, because the run branches on it. SHIM_PROOF proves
all twenty from the segments of Segments.bend, which gen_seg.sh writes
(section 14). Composed with
the guest-step laws, which keep SP_EL2 and TPIDR_EL2 across a guest's
steps, they are the context switch's correctness.

## 14. What a symbolic run costs the kernel

The kernel substitutes without sharing: a term that names its input
twice grows as a power of its steps, and a value forced to its
constructor leaves its fields unforced, so a field built from the field
before it is a chain that every later use reduces again. Isa.bend is
written against both, and the shim's laws went from checking 5 steps to
checking 17 as each was found:

| what the model does | how far the kernel gets |
|---|---|
| names the next state inside its own update | 5 steps; 13 GB, then out of memory |
| takes the state apart once, forces every value it reads, builds it once | 12 steps; 30 MB |
| computes a load's address once rather than three times | 13 steps |
| gives the shim's memory cells addresses that are literal offsets from the base, and the base no multiply | 17 steps |

The last two are the second rule again, applied to an address rather
than to a value. The first row is what a plain model does, and it is
worth writing down because nothing warns of it: `bend` shares, and
checks every shape here in about a second, so only the kernel tells
them apart.

Then the fuel: 400M reductions per def, which about 17 steps spend. So
each path is cut into segments, each starting from a state written out,
and `Chain.bend` adds them back up: a run of m + n steps is a run of m
and then a run of n. The states are symbolic, so they come from bend2
itself, and `gen_seg.sh` writes them: a deliberately false claim about
the state after k steps makes the checker print that state's normal
form, which is Bend source but for the text of the rom and of the cells
the path starts with, which the generator puts back as the calls they
came from. Whatever it writes the checker checks, so an error there is a
proof that fails, not a proof that passes wrongly.

Eight steps is the cut it starts from, and `--kernel` halves a segment
the kernel will not take, which the last few of an exit path need as the
lists the shim has written grow:

| path | steps | segments | one per |
|---|---|---|---|
| enter | 68 | 8, 8, 8, 8, 8, 8, 8, 8, 4 | guest |
| exit, synchronous | 80 | 8, 8, 8, 8, 8, 8, 8, 8, 8, 2, 3, 3 | guest |
| exit, interrupt | 80 | 8, 8, 8, 8, 8, 8, 8, 8, 8, 2, 3, 3 | guest |
| decode, an HVC | 9 | 8, 1 | all |
| decode, a data abort | 17 | 8, 8, 1 | all |
| decode, an instruction abort | 19 | 8, 8, 3 | all |
| decode, any other class | 14 | 8, 6 | all |
| decode, the guest's own | 18 | 8, 8, 2 | guest |

Thirty-three segments a guest for the switch and twenty-two for the
decode: 154 in all, and with the laws that join them 502 defs and
1.31 MB of Bend in `Segments.bend`. Writing it costs about half an hour,
of which fifteen minutes is the kernel checking each segment as it is
cut and the rest is the generator being shell. `bend
Segments.bend` then checks in 11 s, and `bend SHIM_PROOF.bend --verdict`,
which runs the whole of it through the proven kernel, in about seven
minutes. The gate's `shim` check is that run, so a `Segments.bend` stale
against Isa.bend fails there: a segment law is a claim about the very run
that changed.

The decode's runs are short and still want segments, because a symbolic
run's cost is not its length alone: the ESR, the FAR and the HPFAR enter
it as variables, and a mask or a shift over a variable is a term every
later step carries.

The generator is shell, not Bend: Bend's runtime dies with a machine
stack overflow when a program rebuilds a string of more than about twenty
thousand characters, and a printed state is seventeen. gen_seg.sh parses
a state in awk and prints everything else, which is ugly and is the
shape gates/repo.ts allows a demo to have.
