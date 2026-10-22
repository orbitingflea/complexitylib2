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
`Stateful.Bound`s; each call is a flat run, but building the structure (except the Queue's
6-instruction init) and passing arguments are not charged (Dynamic:17–23).
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

---

# Full survey

## 1. `Cslib.WordRAM` core: `C/WordRAM/Defs.lean`, `Basis.lean`

Source: adapted from `edemaine/lean-trominoes` @6d5b36c1 (Defs:8; UPSTREAM.md:63–77).

- **State.** `Data r` = `regs : Fin r → ℕ` and `mem : ℕ → ℕ` (Defs:218–222); `State` adds an
  unbounded `pc : ℕ` (Defs:263; doc Defs:87 "a program has constant length").
- **Word size.** `Fits w v := v < 2^w` (Defs:143). Words are unsigned; subtraction truncates;
  `x/0 = 0`, `x%0 = x` (Defs:71–74). Only `const` and `alu` check fit; a too-wide result *faults*
  (no wrap-around) (Defs:64–70, 247, 294–299). Copies, loads and stores do not check, because
  from a fitting input every reachable value is already a word (`Runs.bounded_init`, Defs:596).
  Hence every address is `< 2^w`: "the memory has `2 ^ w` usable cells" (Defs:57).
- **Instructions.** `Op` = `const d v | copy d s | alu f d args | load d a | store a s`
  (Defs:176–188); `Instr` = `op | jump t | branch c t | halt i` with `Cond` = `eq | lt`
  (Defs:167–172, 199–208). `load`/`store` are indirect through a register.
- **Basis.** `Basis` extends a circuit `Signature` with `interp : ℕ → Interpretation` (the
  semantics may depend on `w`) and a `ReadsWidth` flag (Basis:73–84). `BinOp` = add, sub, mul,
  div, mod, and, or, xor, shiftLeft, shiftRight (Basis:91–128). `Basis.standard` = all `BinOp`
  plus `width` (returns `w`) (Basis:131–161). Sub-bases: `Basis.restrict` (Basis:229),
  `Basis.additive` = {add, sub} (Basis:243), `Basis.arithmetic` = {add, sub, mul, div, mod}
  (Basis:250, the trominoes source's set). Basis maps: `Basis.Hom` (Basis:183) with
  `additiveHomArithmetic`, `arithmeticHomStandard`, `additiveHomStandard` (Basis:254–265).
  The doc names Hagerup's restricted / multiplication / AC⁰ RAMs (Basis:16–20); only the
  three bases above are defined (inferred: no other `Basis` value found in `C/WordRAM`).
- **Cost.** `Executes w p s v n`: halts with output `v` after exactly `n` instructions, halt
  included (Defs:395–396). Unit cost for every instruction, including mul/div/shift. No
  space measure. `run` is an executable interpreter with fuel (Defs:400);
  `executes_iff_exists_run_eq` (Defs:480), `Executes.unique` (Defs:485).
- **I/O.** `Data.init input`: all registers 0, `mem 0 = length`, `mem (i+1) = input[i]`, rest 0;
  installing it is free (Defs:504–509). `InputFits w input` = length and every word fit (Defs:523).
  Output = one word, the register named by `halt` (Defs:199–208).
- **Width monotonicity.** `Executes.mono_width` (Defs:689): a program that never reads `w`
  runs the same at every larger `w`.

## 2. Layers on top of the core

Each subsection says whether the layer is a convenience (compiles to a flat `Program` with a
proved count) or a different model.

### 2.1 Structured code: `Structured.lean`, `Compile.lean`, `Notation.lean` (convenience)
- `Code` = `op | seq | branch c pos neg | loop c body` (Structured:80–88). `Exec w c x y n` is a
  big-step relation with exact costs: op 1, branch +1/+2, loop exit 2, loop iteration body+2
  (Structured:126–145); `ExecWithin` = `∃ n ≤ T` (Structured:148). `Code.eval` interpreter
  (Structured:372). "No rule executes a Lean function as one instruction" (Structured:23).
- `Code.assemble` (Compile:63), `Code.program c out = c.assemble 0 ++ [.halt out]` (Compile:81).
  `Exec.runs`: same number of flat steps (Compile:135). `Exec.executes`: `Exec … n` ⇒
  `Executes w (c.program out) ⟨0,x⟩ _ (n+1)` (Compile:174).
- `ram[ … ]` syntax and the `ram_eval` tactic (`C/WordRAM/Notation.lean`) build `Code` terms.

### 2.2 Time classes: `Time.lean` (statement forms on flat programs)
- `Program.Answers p w input b time` (Time:102). `Program.DecidesInTime p encode A time bits`:
  ∀ `a`, ∀ `w ≥ bits a` with `InputFits w (encode a)`, `p` answers `a ∈ A` within `time a`
  (Time:133). `DecidableInTime B A encode time bits` = ∃ `r`, ∃ `p` (Time:147).
  This is the transdichotomous "one program for every large-enough `w`" (Time:22–26).
- `DecidesInTimeAt` / `DecidableInTimeAt` fix one width per input (Time:141, 153); the doc warns
  this admits advice through `width` and is vacuous if nothing fits (Time:39–45).
- `logWidth k n = k(⌊log₂ n⌋+1)` (Time:220). `LinearTime B A encode size` = ∃ c k, time
  `c(size+1)` with threshold `logWidth k size` (Time:237); `PolynomialTime` (Time:245).
  "The threshold is a lower bound, not an input-fit certificate" (Time:50–55).
- `DecidableInTime.of_code` (Compile:211) and `Code.decidesInTime_program` move a structured
  proof to the flat statement (+1 for halt).

### 2.3 Functions: `Function.lean` (convenience)
- `Program.ComputesInTime p encode time bits f` with `f : α → ℕ` (one output word) (Function:51);
  `ComputableInPolyTime B encode size f` = ∃ r p, polynomial `T`, ∃ k, threshold `logWidth k`
  (Function:59). `Code.computesInTime_program` (Function:74, +1), `ComputableInPolyTime.of_code`
  (Function:90). Tagged `@[fun_prop]`; the `polytime` tactic can reuse it (`Complexity/Tactic/WordRAM.lean:62`).

### 2.4 Basis transfer: `MapOp.lean` (convenience)
- `Program.mapOp φ` along a `Basis.Hom` (MapOp:75). `executes_mapOp_iff`: same output, same
  count (MapOp:153); `Exec.mapOp` (MapOp:167); `DecidableInTime.mapOp`, `LinearTime.mapOp`,
  `PolynomialTime.mapOp` (MapOp:220–239). Only along homs into a larger basis; simulating an op
  by a program over a smaller basis is not formalized (MapOp:27–28).

### 2.5 Memory helpers: `Allocation.lean`, `Copy.lean` (convenience)
- `Block` (Allocation:59), `zeroFill` 4k+2 instructions (Allocation:137–142), `alloc` 4k+7 at a
  frontier register that only grows; no free, no reuse (Allocation:12–47, 185–193); `readAt` /
  `writeAt` 2 instructions (Allocation:252–267). All are `Code` with `Exec` bounds.
- `ArrayCopy.program`: n words in ≤ 7n+4 instructions, 7 registers (Copy:85–90).
- Users: Element distinctness allocates and clears its bucket array with `alloc` (charged) and
  uses `readAt`/`writeAt` (ElementDistinctness:10, 103, 111); vEB membership uses `readAt`
  (`VanEmdeBoas/Member.lean:115`). Stack, Queue, Prefix sums use fixed base addresses.

### 2.6 Proof tools: `Heap.lean`, `Trace.lean` (no code)
- `HeapAssertion` with finite footprint, `pointsto`, `array`, `sep`, `frame` (Heap:43–111):
  separation-logic style assertions over the total memory.
- `TraceExec` records `Probe` read/write per step (Trace:44–59); `readCount`, `writeCount`,
  `writes` (Trace:116–149). "Not the full cell-probe model" (Trace doc).

### 2.7 Data structures: `Dynamic.lean` (convenience, per call)
- `DynamicProgram D r`: one `Code .standard r`, an output register, input registers, and
  `encode`/`decode` for the operations of a `Stateful.Spec D` (Dynamic:53–63). Argument encoding
  and delivery and result decoding are free; the halt is charged (Dynamic:17–23).
- `ExecOp` (Dynamic:99): instructions = n+1. `ExecOp.executes`: each call is a flat `Executes`
  of `code.program output` from `⟨0, prepare o x⟩` (Dynamic:105).
- `DynamicCertificate` (rep, bounded, arguments_fit, execute) (Dynamic:141);
  `realization` → `Stateful.Realization` (Dynamic:158); `instruction_bound` → `Stateful.Bound`
  (Dynamic:172); `probe_bound` (Dynamic:182). Fixed to `Basis.standard`.
- Statement form for data structures: `Stateful.Bound` (Foundations/Semantics/Stateful/Resource:50)
  and `Stateful.Amortized` (…/Stateful/Amortized:45) over adaptive clients
  (`PFunctor.FreeM`, …/Stateful/Basic:115). The start state is any state satisfying `rep`.

### 2.8 Controllers: `Controller.lean` (convenience)
- `Refines w pre p post budget code` (Controller:54–58): one `Code` runs a whole adaptive
  client `p` within `budget`. Rules `pure`, `bind`, `branch` (+2), `prepend`, `call` (inline a
  `DynamicCertificate` operation, Controller:155). `Refines.executes`: a flat `Executes` with
  `n ≤ budget + 1` (Controller:144). Unlike `Dynamic`, preparation and control flow are charged.

### 2.9 GenericRAM embedding: `Generic.lean` (exact transfer)
- `Basis.genericModel` (Generic:47), `Program.toGeneric` (Generic:93); `executes_toGeneric_iff`
  is an iff with the same count (Generic:156). Used by vEB `member_executes_generic`.

### 2.10 Native TM certificates: `Native.lean` (different model, scalar only)
- `checkedAdd_polyTime` (Native:48), `checkedAddCertificate` (Native:64): a Turing machine
  computes checked addition, width in unary. Not a simulation of whole RAM runs (Native:17–38;
  ROADMAP:876–878).

### 2.11 Compiler to Cook–Reckhow RAM: `RAM.lean`, `RAMInput.lean` (different model)
- Namespace `Cslib.WordRAM.ToRAM` (RAM:79). Only `Program.IsAdditive` programs: const, copy,
  add, sub, load, store, compare (RAM:61–74); no mul, div, bitwise, shifts or `width`.
- Layout: source register i → target i+1; memory a → target `r+5+a`; 8 target instructions per
  source instruction (RAM:82–123). Forward simulation of successful runs only.
- `executes_compile`: log cost ≤ 8t(bitLength(r+5)+w+1) (RAM:492);
  `haltsWithResultInTime_padded` (RAM:626); with charged input preparation,
  `haltsWithResultInTime_prepared`: ≤ C_r(t+len+1)(w+1) (RAMInput:93).

## 3. `Cslib.GenericRAM` (`C/GenericRAM/`)

- `Model` (Defs:63–92): `Value`, `Address`, `Config` (e.g. `w`), constants, partial operations
  and tests (`Option`), `admissible` (what may be stored), `address` (value → address),
  `validMove`, `validPC`. `Data M r` = `regs : Fin r → Value`, `mem : Address → Value`
  (Defs:100). `Data.init default memory`: the caller picks the input layout (Defs:122).
- Same instruction shape as WordRAM; `Executes` counts every instruction incl. halt (Defs:223).
  Flat `Program` only: no `Code`, no time classes (ROADMAP:878–880 "Generalizing the structured
  program calculus and time-class APIs to arbitrary domains … remain open").
- Instances: `Signed` (two's-complement `Fits`, add/sub/mul/div/mod, lean-trominoes checks)
  (Signed:45–75); `Algebraic.real` (noncomputable) and `Algebraic.primeField`: values
  `ℕ ⊕ K`, only nat words address memory (Algebraic:111–194), after Erickson–van der Hoog–Miltzow
  (UPSTREAM.md:78–98); `BoundedNat` (Native/Nat:48).
- `Native.lean`: `NativeCertificate`, `Model.NativePrimitives` (per-primitive TM certificates).
  `SparseMemory/{Basic,Turing}`: `AList` memory with native TM read/insert in cubic time. Neither
  gives a whole-machine simulation (ROADMAP:876–880; UPSTREAM.md:99–103).

## 4. `Cslib.RAM`, Cook–Reckhow (`C/RAM/`)

- Unbounded natural registers `URM.Regs`; inputs in registers 0,1,…; output register 0; halts
  when pc leaves the program (RAM/Defs doc 16–88).
- `Instr` = `const`, `add`, `sub`, `mul`, `load` (indirect), `store`, `jpos` (RAM/Defs:100–118).
  No division, no bitwise ops.
- Cost: `unitCost` (Cost:144), `logCost` charges operand bit lengths, and both address and value
  for indirect access (Cost:154–162); `time` (Cost:172), `HaltsWithResultInTime` (Cost:310),
  `ComputesInTime` (Cost:320).
- `RAM/Input.lean`: `encode` (5 zero registers, length, words) and a charged `prepare` loop.
- `RAM/Squaring.lean`: repeated squaring shows unit and log cost are not polynomially related
  (`exists_mul_pow_lt_of_computesInTime_logCost`, Squaring:197).

## 5. Algorithms (`A/`)

All use `Cslib.WordRAM` with `Basis.standard`. All files are `-- upstream: candidate`.

| Algorithm | Final theorem | Bound | Main hypotheses | Flat? |
|---|---|---|---|---|
| Stack (`Stack.lean`) | `instruction_bound` (311), `run_client` (363) | ≤ 12 per op; history total ≤ 12·len | `Fits w 2`, `Fits w (base+capacity)`; fixed capacity | per call (`ExecOp`) |
| Stack controller (`Stack/Controller.lean`) | `computesInTime` (201), `positive_polytime` (211) | 49 total | `w ≥ 2`, input fits | yes, from `State.init [n]` |
| Queue (`Queue/Dynamic.lean`) | `amortized` (113), `run_client` (128), `run_initialized` (143) | amortized 14 per op, potential 8·rear | `Fits w 1`, `Fits w (base+2·capacity)`; init 6 instructions (`Queue/Basic:377–383`) | per call |
| Prefix sums (`PrefixSums/Dynamic.lean`) | `instruction_bound` (210), `instruction_bound_log` (220) | 13(h+1)+12 per op, = 13(log₂ len+1)+12 | `Fits w (b+2·2^h)`; 2^h leaves; tree build not charged | per call |
| vEB membership (`VanEmdeBoas/Call.lean`) | `member_executes` (112), `member_executes_log` (138), `member_executes_generic` (123) | ≤ 28(d+1)+18, U = 2^(2^d) | `Rep tree base mem`, `tree.Valid`, `Fits w (base+span d)`, bounded state | yes, from a state holding the tree |
| Element distinctness (`ElementDistinctness.lean`) | `answers` (273), `decidesInTime_nodup` (287), `linearTime_nodup` (296) | 14n+15 (`Code`); 16(n+1) flat | entries < n; `w ≥ logWidth 2 n`; `inputFits` (148) | yes, `DecidesInTime` |
| ED on `Cslib.RAM` (`ElementDistinctnessRAM.lean`) | `haltsWithResultInTime_nodup_padded` (99), `haltsWithResultInTime_nodup` (111) | log cost ≤ 2735(n+1)(log₂(n+1)+1) | `program_isAdditive` (59) | Cook–Reckhow program |

Notes.
- Stack and Queue specs reuse `Cslib.Algorithms.Lean.Queue`; vEB `Tree`, `universeSize`,
  `span` come from `Complexity/Algorithms/Lean/VanEmdeBoas/` (`Layout.lean:54, 75, 83`).
- vEB: one 32-register dispatcher holds insert, member and successor (`Program.lean:240`, 212
  instructions, `program_not_readsWidth` 251); only membership is proved. No initializer, no
  space theorem; `Layout.lean` bounds a record by 10 words per universe element but "this does
  not by itself supply an initialization or implemented-space certificate" (ROADMAP:804–806).
- Element distinctness uses a bucket array (`seen`) at addresses after the input; it needs
  entries `< n` (`Input`, ElementDistinctness:118) and `Fits w (2n+1)` (273).
- Prefix sums is a segment tree in preorder, 2·2^h−1 words (`PrefixSums/Tree.lean`), not Fenwick.

## 6. Comparison

| | Textbook word RAM (CLRS §2.2, transdichotomous) | `Cslib.WordRAM` | `GenericRAM` | `Cslib.RAM` |
|---|---|---|---|---|
| Word | w bits, w ≥ log n | `< 2^w`, uniform over `w ≥ bits a` | per model | unbounded ℕ |
| Overflow | usually wraps mod 2^w | faults | per model | n/a |
| Memory | array of words, size ≈ poly(n) or 2^w | `ℕ → ℕ`, 2^w reachable | `Address → Value` | registers ℕ → ℕ |
| Ops | +,−,×,/, bitwise, shifts | basis; standard = all + `width` | signature | +,−,×, indirect |
| Time | unit cost | unit cost incl. halt | unit cost | unit or log cost |
| Space | cells used | none | none | none |
| Input | n words in memory | `mem 0 = n`, `mem 1..n`, free | caller's choice | registers 0.., or charged `prepare` |
| Output | words in memory / registers | one word (halt register) | one value | register 0 |
| Randomness | sometimes | none | none | none |
| Programs | pseudocode | flat list; `Code` compiles | flat list | flat list |

## 7. Gaps against the textbook word RAM

1. **w ≥ log n.** The threshold `bits a` is a lower bound only; `DecidesInTime` quantifies over
   widths where the input fits, so no theorem says "the input fits at w = c log n" unless a
   separate `InputFits` lemma is given (Time:50–55; ED supplies `inputFits`, ED:148). There is no
   upper bound on w (uniformity over all larger w is stronger than CLRS).
2. **Overflow.** Faults instead of wrap-around; mod-2^w algorithms (hashing by multiplication,
   word tricks) must reduce by hand, "not formalized here" (Defs:64–70).
3. **mul/div.** Unit cost in `Basis.standard`; `Basis.additive` gives a no-mul variant, but no
   AC⁰ basis and no simulation of mul by smaller bases (MapOp:27–28). Division by zero follows
   Lean (Defs:71–74).
4. **Memory and space.** No memory-size parameter, no space measure, no live/peak accounting;
   `alloc` is a bump allocator without free (Allocation:12–47). Outstanding per ROADMAP:826–828.
5. **Initialization.** Free input install (Defs:504–509); data-structure builds are not charged
   (Dynamic:21–22), except the Queue's 6-instruction init, the Stack controller, and ED's
   charged `alloc` of its bucket array.
6. **Argument delivery** for data-structure calls is free (Dynamic:17–20); `Controller` charges
   it only when the client is written as one `Code`.
7. **I/O.** One output word; no output arrays. Input is a list of words with a length header.
8. **Randomness.** None in any RAM model; ROADMAP:826–829 lists "independent model realizations
   for cell probes, caches and randomness" as outstanding.
9. **Other.** No procedures/recursion or call stack (ROADMAP:828 "recursive procedures");
   no doubling arrays (ROADMAP:828); no TM ↔ WordRAM simulation (Defs:26–31); the compiler to
   `Cslib.RAM` covers only the additive fragment (RAM doc 14–52).

## 8. Decide and report

- **Base for new data structures.** `Cslib.WordRAM` over `Basis.standard`: write `Code` with
  `ram[...]`, certify per-call costs with `DynamicCertificate` + `Stateful.Bound`/`Amortized`,
  and whole runs with `Controller`/`DecidableInTime`. Every one of these reduces to flat
  `Executes` with an exact count (`Exec.executes`, `ExecOp.executes`, `Refines.executes`).
- **Most important gap.** No space measure and uncharged initialization (no memory-size
  parameter). Bounds such as vEB's O(U) space and O(U) build cannot be stated; time bounds
  hold from an arbitrary prepared state, not from an input.
- **Unfinished or inconsistent upstream.**
  - Every file in scope is `-- upstream: candidate` (44 markers in `C/WordRAM`, `C/GenericRAM`,
    `C/RAM`, `A/`).
  - Two namespaces for algorithms: Stack and Queue in `Cslib.WordRAM.*`
    (Stack:48, Queue/Basic:40); Prefix sums, vEB, ED in `Cslib.Algorithms.WordRAM.*`.
  - Name overlap: `Cslib.RAM` vs file `C/WordRAM/RAM.lean` (namespace `Cslib.WordRAM.ToRAM`);
    `Native.lean` in both `WordRAM` and `GenericRAM`.
  - Two instruction-set models with the same shape (`WordRAM.Instr`, `GenericRAM.Instr`); WordRAM
    is not re-based on GenericRAM, only embedded (Generic:156).
  - vEB insert/successor code is present but unproved (ROADMAP:815–816).
  - `Dynamic` is fixed to `Basis.standard` (Dynamic:55).
