# The word RAM: a formal abstract (Mean rendering)

This file follows [`WordRAMAbstract.lean`](WordRAMAbstract.lean) from top to bottom. Its prose
is the Lean file's comments, kept as they are. Each Lean declaration is replaced by its
[Mean](https://github.com/edemaine/mean) rendering, whose round trip Mean checked. Text marked
*hand-written, not machine-checked* stands where Mean renders nothing useful. The last section
says how this was made and what Mean did and did not check.

A short, self-contained account of the word RAM with the standard operations, and of what it
means for a problem to be decidable on it in time `T`. It imports only Mathlib.
`ComplexityTests/WordRAMAbstractBridge.lean` proves that it is the library's word RAM.

At word size `w`, a *word* is a number below `2 ^ w`. A machine has `r` registers `R[0]`, …,
`R[r - 1]` and a memory cell `M[a]` at every address `a : ℕ`; all hold natural numbers.
Every instruction takes one unit of time.

## `AluOp`

The binary operations. Subtraction is truncated (`3 - 5 = 0`), `x / 0 = 0`, `x % 0 = x`,
`and`, `or`, `xor` are bitwise, and `shl`, `shr` shift left and right by `y` bits.

*Hand-written, not machine-checked:* `AluOp` has the ten values `add`, `sub`, `mul`, `div`, `mod`, `and`, `or`, `xor`,
`shl`, `shr`.

## `AluOp.eval`

The value of a binary operation, before any check that it is a word.

```lean
Definition:
  AluOp.eval is
    the function mapping an element x of AluOp and a natural number x_1 and a natural number x_2 to
      match x, x_1, x_2 with
      | AluOp.add, x, y => x + y
      | AluOp.sub, x, y => x - y
      | AluOp.mul, x, y => x * y
      | AluOp.div, x, y => x / y
      | AluOp.mod, x, y => x % y
      | AluOp.and, x, y => x &&& y
      | AluOp.or, x, y => x ||| y
      | AluOp.xor, x, y => x ^^^ y
      | AluOp.shl, x, y => x * 2 ^ y
      | AluOp.shr, x, y => x / 2 ^ y.
```

## `Instr`

The instructions over `r` registers. Jump targets are instruction numbers.

*Hand-written, not machine-checked:* an instruction is one of:

- `const d x`: `R[d] := x`;
- `copy d i`: `R[d] := R[i]`;
- `alu f d i j`: `R[d] := f(R[i], R[j])`;
- `width d`: `R[d] := w`, the word size;
- `load d a`: `R[d] := M[R[a]]`;
- `store a i`: `M[R[a]] := R[i]`;
- `jump t`: go to instruction `t`;
- `branchEq i j t`: go to `t` if `R[i] = R[j]`, else to the next one;
- `branchLt i j t`: go to `t` if `R[i] < R[j]`, else to the next one;
- `halt i`: stop with output `R[i]`.

Here `d`, `i`, `j`, `a` are registers (elements of `Fin r`), and `x`, `t` are natural numbers.

## `Program`

A program is a list of instructions, numbered from `0`.

```lean
Abbreviation:
  Program is
    the function mapping a natural number r to
      List (Instr r).
```

## `State`

A state: the number `pc` of the next instruction, the registers and the memory.

*Hand-written, not machine-checked:* a state `State r` has three fields: `pc : ℕ`, `reg : Fin r → ℕ` (so `R[i]` is
`reg i`) and `mem : ℕ → ℕ` (so `M[a]` is `mem a`).

## `Outcome`

One step continues in a new state, halts with an output, or faults.

*Hand-written, not machine-checked:* an outcome is `next s` for a state `s`, `halt v` for a number `v`, or `fault`.

## `step`

One step of program `p` at word size `w`. A constant or operation whose value is not a word
faults (no wrap-around), and so does running off the end of the program. Copies, loads and
stores are not checked: from an input whose length and words fit (`InputFits`), they only ever
move words.

```lean
Definition:
  step is
    the function mapping an implicit natural number r and a natural number w and an element p of Program r and an element s of State r to
      match p[s.pc]? with
      | none => Outcome.fault
      | some (Instr.const d x) =>
        (fun (d : Fin r) (x : ℕ) =>
            if x < 2 ^ w then
              (fun (d : Fin r) (x : ℕ) => Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem }) d x
            else Outcome.fault)
          d x
      | some (Instr.copy d i) =>
        (fun (d : Fin r) (x : ℕ) => Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem }) d
          (s.reg i)
      | some (Instr.alu f d i j) =>
        (fun (d : Fin r) (x : ℕ) =>
            if x < 2 ^ w then
              (fun (d : Fin r) (x : ℕ) => Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem }) d x
            else Outcome.fault)
          d (f.eval (s.reg i) (s.reg j))
      | some (Instr.width d) =>
        (fun (d : Fin r) (x : ℕ) => Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem }) d w
      | some (Instr.load d «a») =>
        (fun (d : Fin r) (x : ℕ) => Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem }) d
          (s.mem (s.reg «a»))
      | some (Instr.store «a» i) =>
        Outcome.next { pc := s.pc + 1, reg := s.reg, mem := Function.update s.mem (s.reg «a») (s.reg i) }
      | some (Instr.jump t) => Outcome.next { pc := t, reg := s.reg, mem := s.mem }
      | some (Instr.branchEq i j t) =>
        Outcome.next { pc := if s.reg i = s.reg j then t else s.pc + 1, reg := s.reg, mem := s.mem }
      | some (Instr.branchLt i j t) =>
        Outcome.next { pc := if s.reg i < s.reg j then t else s.pc + 1, reg := s.reg, mem := s.mem }
      | some (Instr.halt i) => Outcome.halt (s.reg i).
```

*Hand-written, not machine-checked:* Lean's `step` names two helpers, which Mean writes out as functions in each case:

- `fun d x => Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem }`
  is "set `R[d] := x`, then go to the next instruction";
- `fun d x => if x < 2 ^ w then … else Outcome.fault` is the same, but it faults if `x` is not
  a word. `const` and `alu` use this one.

`width` uses the first helper, with no check: `w < 2 ^ w`, so it never faults.

## `Halts`

`Halts w p s v n`: from state `s`, program `p` halts with output `v` after exactly `n`
instructions, the final `halt` included. A run that faults never halts.

```lean
Definition:
  Halts is
    the function mapping an implicit natural number r and a natural number w and an element p of Program r and an element x of State r and a natural number x_1 and a natural number x_2 to
      Nat.brecOn (motive := fun (x : ℕ) => State r → ℕ → Prop) x_2 (Halts._f w p) x x_1.
```

*Hand-written, not machine-checked:* Mean shows only the compiled form of this recursive definition. It means:

- `Halts w p s v 0` is false: halting takes at least one instruction.
- `Halts w p s v (n + 1)` looks at `step w p s`:
  - if it is `next t`, then `Halts w p t v n`;
  - if it is `halt x`, then `x = v` and `n = 0`;
  - if it is `fault`, it is false.

## `init`

The start state on input `x₁, …, xₖ`: instruction `0`, registers `0`, and memory
`k, x₁, …, xₖ` at addresses `0, 1, …, k`, then `0` everywhere.

```lean
Definition:
  init is
    the function : {r : ℕ} → List ℕ → State r mapping an implicit natural number r and a list input of ℕ elements to
      ({ pc := 0, reg := fun (x : Fin r) => 0, mem := fun («a» : ℕ) => (input.length :: input).getD «a» 0 }).
```

## `InputFits`

An input fits word size `w` if its length and all its entries are words.

```lean
Definition:
  InputFits is
    the function mapping a natural number w and a list input of ℕ elements to
      input.length < 2 ^ w and (for every natural number x:
        if x ∈ input then
          x < 2 ^ w).
```

## `Decides`

`p` decides `A ⊆ α` in time `T`, on instances encoded by `encode`: for every instance `a`
and every word size `w ≥ bits a` at which the input fits, `p` halts within `T a` instructions
with output `1` if `a ∈ A` and `0` if not. One program serves every such word size.

```lean
Definition:
  Decides is
    the function mapping an implicit natural number r and an implicit element α of Type u_1 and an element p of Program r and an element A of Set α and a function encode from α to List ℕ and a function T from α to ℕ and a function bits from α to ℕ to
      ∀ («a» : α) (w : ℕ),
        bits «a» ≤ w →
          InputFits w (encode «a») →
            ∃ (v : ℕ) (n : ℕ), Halts w p (init (encode «a»)) v n ∧ n ≤ T «a» ∧ («a» ∈ A → v = 1) ∧ («a» ∉ A → v = 0).
```

## `DecidableInTime`

`A` is decidable in time `T` (from word size `bits` on) if some program, with some number
of registers, decides it.

```lean
Definition:
  DecidableInTime is
    the function mapping an implicit element α of Type u_1 and an element A of Set α and a function encode from α to List ℕ and a function T from α to ℕ and a function bits from α to ℕ to
      there is a natural number r such that
        there is an element p of (Program r) such that
          Decides p A encode T bits.
```

# The bridge: main statements

These come from [`WordRAMAbstractBridge.lean`](WordRAMAbstractBridge.lean). There, the abstract
machine is `WordRAMAbstract`, and the library's word RAM is `WordRAM` (that is,
`Cslib.WordRAM`). Lean checks the proofs; only the statements are shown.

## `OutcomeAgrees`

An abstract outcome and an outcome of `Cslib.WordRAM` *agree* if both continue in the same
state (same next instruction, registers and memory), both halt with the same output, or both
fault.

```lean
Definition:
  OutcomeAgrees is
    the function : {r : ℕ} → WordRAMAbstract.Outcome r → WordRAM.Outcome r → Prop mapping an implicit natural number r and an element x of WordRAMAbstract.Outcome r and an element x_1 of WordRAM.Outcome r to
      match x, x_1 with
      | WordRAMAbstract.Outcome.next s, WordRAM.Outcome.next t => t = { pc := s.pc, data := { regs := s.reg, mem := s.mem } }
      | WordRAMAbstract.Outcome.halt v, WordRAM.Outcome.halt v' => v = v'
      | WordRAMAbstract.Outcome.fault, WordRAM.Outcome.fault => True
      | x, x_2 => False.
```

## `Same`

An abstract program `p` and a program `q` of `Cslib.WordRAM` run alike: from every state
`⟨pc, reg, mem⟩` and at every word size, one step of each has agreeing outcomes, and both halt
with the same output after the same number of instructions.

```lean
Definition:
  Same is
    the function mapping an implicit natural number r and an element p of WordRAMAbstract.Program r and an element q of WordRAM.Program WordRAM.Basis.standard r to
      for all natural numbers w and pc:
        ∀ (reg : Fin r → ℕ) (mem : ℕ → ℕ),
          OutcomeAgrees (WordRAMAbstract.step w p { pc := pc, reg := reg, mem := mem })
              (WordRAM.step w q { pc := pc, data := { regs := reg, mem := mem } }) ∧
            ∀ (v n : ℕ),
              WordRAMAbstract.Halts w p { pc := pc, reg := reg, mem := mem } v n ↔
                WordRAM.Executes w q { pc := pc, data := { regs := reg, mem := mem } } v n.
```

## `runsAgree`

**Same machine.** Each abstract program runs alike with some program of `Cslib.WordRAM`
over `Basis.standard` with the same registers, and conversely.

```lean
Theorem runsAgree:
  for every natural number r:
    (∀ (p : WordRAMAbstract.Program r), ∃ (q : WordRAM.Program WordRAM.Basis.standard r), Same p q) and (∀ (q : WordRAM.Program WordRAM.Basis.standard r), ∃ (p : WordRAMAbstract.Program r), Same p q)
```

## `decidableInTime_iff`

**Same time classes.** A problem is decidable in time `T` on the abstract machine exactly
when it is on `Cslib.WordRAM` over `Basis.standard`, for the same encoding, time bound and
word-size threshold.

```lean
-- Universe parameters: u
Theorem decidableInTime_iff:
  ∀ {α : Type u} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ),
    WordRAMAbstract.DecidableInTime A encode T bits ↔ WordRAM.DecidableInTime WordRAM.Basis.standard A encode T bits
```

# How this was made, and what Mean checked

Mean commit `b142d108aeb2dbba04fb292c0530887031b206f0` (2026-10-15). Mean pins Lean
`v4.35.0`; its three modules compiled unchanged against this repository's Lean `v4.36.0-rc1`
and Mathlib, outside the repository (Mean is not a dependency). With Mean cloned at `$MEAN`
and an empty folder `$OUT`, from the repository root:

```sh
mkdir -p "$OUT/Mean"
for f in Syntax RoundTrip Render; do
  LEAN_PATH="$(lake env printenv LEAN_PATH):$OUT" lake env lean -R "$MEAN" \
    -o "$OUT/Mean/$f.olean" "$MEAN/Mean/$f.lean"
done
lake build ComplexityTests.WordRAMAbstractBridge
LEAN_PATH="$(lake env printenv LEAN_PATH):$OUT" lake env lean RunA.lean
LEAN_PATH="$(lake env printenv LEAN_PATH):$OUT" lake env lean RunB.lean
```

`RunA.lean` imports `Mean.Render` and `ComplexityTests.WordRAMAbstract`, opens
`namespace ComplexityTests.WordRAMAbstract`, and runs `#mean` on `AluOp.eval`, `Program`,
`step`, `Halts`, `init`, `InputFits`, `Decides` and `DecidableInTime`. `RunB.lean` imports
`ComplexityTests.WordRAMAbstractBridge`, opens `namespace ComplexityTests.WordRAMAbstractBridge`
and `open Cslib`, and runs `#mean` on `OutcomeAgrees`, `Same`, `runsAgree` and
`decidableInTime_iff`. Working inside the namespace makes Mean print short names in the
bodies.

- **Checked:** for each of these 12 declarations, Mean parsed its own output back, elaborated
  it, and checked that it gives the same Lean term. All 12 passed. This shows the text means
  the Lean term; it does not show the term says what the prose claims.
- **One edit after Mean:** Mean has no option to shorten the declaration name in its header
  line, so the namespace prefix (`ComplexityTests.WordRAMAbstract.` or
  `ComplexityTests.WordRAMAbstractBridge.`) was removed there. Nothing else in the Mean output
  was changed.
- **Not checked by Mean:** all prose (the Lean comments); the types `AluOp`, `Instr`, `State`
  and `Outcome`, which Mean renders only as `Type`; and the hand-written readings at
  `AluOp`, `Instr`, `State`, `Outcome`, `step` and `Halts`.
