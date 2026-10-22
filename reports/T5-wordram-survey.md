# T5: Word RAM models in upstream Complexitylib (at `8a2d724d`)

Paths: `C/` = `Complexity/Computability/`, `A/` = `Complexity/Algorithms/WordRAM/`.
Line numbers are at `8a2d724d`. "(inferred)" marks a claim I derived and did not read verbatim.

## Framing: is there a "standard RAM model" upstream?

Yes. `C/WordRAM/Defs.lean` is that model.
- Parameters: word size `w` (an argument of `step`/`Executes`, Defs:345, 395) and register
  count `r` (a type index). No memory-size parameter: `mem : ℕ → ℕ` (Defs:218–222). Addresses
  come from `w`-bit registers, so in effect `2^w` cells (inferred).
- Instruction set: `Op` = `const | copy | alu f | load | store` (Defs:176–188) plus `jump`,
  `branch` on `=`/`<`, `halt` (Defs:199–208). The `alu` ops come from a `Basis`:
  `Basis.standard` = add, sub, mul, div, mod, and, or, xor, shl, shr, and `width`
  (Basis:91–161); the smallest named one is `Basis.additive` = {add, sub} (Basis:243).
- Algorithm = flat assembly `Program B r := List (Instr B r)` (Defs:212). Cost:
  `Executes w p s v n` counts every instruction, halt included (Defs:395).
- "Solves X in time T" = `DecidableInTime B A encode time bits` (Time:147): ∃ `r`, ∃ flat
  `p`, for every input `a` and every `w ≥ bits a` with fitting input, `p` answers within
  `time a` (Time:133). Functions: `ComputableInPolyTime` (Function:59), also ∃ flat program.

Every layer above Defs is a convenience that compiles to a flat Defs program with a proved count,
except three (marked *model*):

| Layer | Compiles to flat Defs? Theorem and cost relation |
|---|---|
| `Code` (Structured) | yes: `Exec.runs` exact steps (Compile:135); `Exec.executes` cost n ⇒ flat n+1 (Compile:174); `DecidableInTime.of_code` (Compile:211) |
| Function | yes: `Program.ComputesInTime` is on flat programs (Function:51); `Code.computesInTime_program` (+1) |
| Controller | yes: `Refines.executes` flat run ≤ budget+1 (Controller:144) |
| Dynamic | yes, per call: `ExecOp.executes` flat run, count = `trace.instructions` (Dynamic:105) |
| Allocation | yes: `Code` fragments with `Exec` bounds (`alloc_exec`, Allocation:193), then `Exec.executes` |
| MapOp | yes: `executes_mapOp_iff` same output, same count across a basis map (MapOp:153) |
| Heap, Trace | proof tools only (memory assertions, probe logs); no code of their own |
| Native | *model*: Turing-machine certificate for one scalar op (`checkedAdd_polyTime`, Native:48) |
| GenericRAM | *model*: a superset; exact embedding `executes_toGeneric_iff` (Generic:156) |
| `ToRAM` (RAM.lean) | *model*: Cook–Reckhow RAM, log cost; `executes_compile` (RAM:492) |

Final theorems on flat programs: Element Distinctness `decidesInTime_nodup` (on
`decider.program ans`, `A/ElementDistinctness.lean:287`); Stack controller `computesInTime`
(`A/Stack/Controller.lean:201`); vEB `member_executes` (`A/VanEmdeBoas/Call.lean:112`, but
from any state that holds a tree, not from an input). Stack, Queue, Prefix sums give per-call
`Stateful.Bound`s; each call is a flat run, but building the structure and passing arguments
are not charged (Dynamic:17–23).
Missing for a memory-size parameter: no space measure at all; addresses are bounded only by
`2^w`. ROADMAP:826–828 lists "reusable allocation and deallocation, live/peak space
accounting" as outstanding.

## Models

| Model | State | Word size | Ops | Cost | Programs | Links |
|---|---|---|---|---|---|---|
| `Cslib.WordRAM` (`C/WordRAM/`) | `r` registers + `mem : ℕ → ℕ`, pc | words `< 2^w`, overflow faults (Defs:64–70); `w` given per run, uniform over `w ≥ bits a` | `Basis` (standard: +,−,×,/,%,bitwise,shifts,width) | 1 per instruction incl. halt; input install free | flat `Program`; structured `Code` + `ram[...]` notation | MapOp, GenericRAM embedding, compiler to `Cslib.RAM` (additive ops only) |
| `GenericRAM.Model` (`C/GenericRAM/`) | `r` registers + `mem : Address → Value` | per instance: Signed (`2^w` range), Algebraic (reals / prime field + nat words), Nat | partial ops/tests from a signature | 1 per instruction incl. halt | flat `Program` only | WordRAM embeds exactly; native TM certs for scalar ops and sparse memory only |
| `Cslib.RAM` (`C/RAM/`, Cook–Reckhow) | unbounded registers `URM.Regs`, indirect access | unbounded naturals | const, add, sub, mul, load, store, jpos | unit or log cost (`logCost`, Cost:154) | flat `RAM.Program` | target of `ToRAM.executes_compile`; unit vs log not poly-related (Squaring:197) |

## Algorithms (`A/`, all on `Cslib.WordRAM`, `Basis.standard`)

- Stack: ≤ 12 instructions per op, fixed capacity (`instruction_bound`, Stack:311).
- Stack controller: `max n 1` in ≤ 49 instructions from the input; `positive_polytime`.
- Queue: amortized 14 per op, potential 8·(rear length) (`amortized`, Queue/Dynamic:113).
- Prefix sums (segment tree, 2^h leaves): 13(h+1)+12 per op (`instruction_bound`, PrefixSums/Dynamic:210).
- vEB membership: ≤ 28(d+1)+18 = O(log log U) (`member_executes`); insert/successor uncertified.
- Element Distinctness (entries < n): 16(n+1) at `w ≥ 2(⌊log₂ n⌋+1)`; `linearTime_nodup`.
- Element Distinctness on `Cslib.RAM`: log cost ≤ 2735(n+1)(log₂(n+1)+1) (`haltsWithResultInTime_nodup`).
