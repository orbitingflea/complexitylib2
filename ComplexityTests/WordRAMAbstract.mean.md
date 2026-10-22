# Mean rendering of the word-RAM abstract

This file shows [`WordRAMAbstract.lean`](WordRAMAbstract.lean) and the main statements of
[`WordRAMAbstractBridge.lean`](WordRAMAbstractBridge.lean) as rendered by
[Mean](https://github.com/edemaine/mean), commit
`b142d108aeb2dbba04fb292c0530887031b206f0` (2026-10-15).

## What Mean checked

- Mean pins Lean `v4.35.0` and Mathlib `v4.35.0`. This repository uses Lean `v4.36.0-rc1`.
  Mean's three modules (`Mean/Syntax.lean`, `Mean/RoundTrip.lean`, `Mean/Render.lean`)
  compiled without change against this repository's toolchain and Mathlib, outside the
  repository. Mean is not a dependency of this repository.
- `#mean` ran on 12 declarations: the 8 definitions of the abstract (`AluOp.eval`,
  `Program`, `step`, `Halts`, `init`, `InputFits`, `Decides`, `DecidableInTime`), and 4 of
  the bridge (`OutcomeAgrees`, `Same`, and the statements of `runsAgree` and
  `decidableInTime_iff`). For each one, Mean parsed its own output back, elaborated it, and
  checked that it gives the same Lean term (its round-trip check). All 12 passed. The output
  below is verbatim.
- The round trip checks only that the text means the same Lean term. Whether that term says
  what the reader wants is still for the reader to judge.

## What Mean did not machine-check

- **The types** `AluOp`, `Instr`, `State` and `Outcome`. Mean renders an inductive type or a
  structure only as `Type`, so their constructors and fields are read from the Lean source.
- **`Halts`.** It is defined by recursion, and Mean renders its compiled form
  (`Nat.brecOn`), which says nothing to a reader. The reading at the end of this file is
  written by hand.
- **All comments** in the Lean files, including the meaning of each instruction.
- Mean's vocabulary is small, so most of the output is still Lean notation (`match`, `∀`,
  `∃`, `→`); only the outer binders and some quantifiers became English.

To reproduce (from the repository root, with Mean cloned at `$MEAN` and an empty
folder `$OUT`):

```sh
mkdir -p "$OUT/Mean"
for f in Syntax RoundTrip Render; do
  LEAN_PATH="$(lake env printenv LEAN_PATH):$OUT" lake env lean -R "$MEAN" \
    -o "$OUT/Mean/$f.olean" "$MEAN/Mean/$f.lean"
done
lake build ComplexityTests.WordRAMAbstractBridge
# Run.lean: `import Mean.Render`, `import ComplexityTests.WordRAMAbstractBridge`,
# then one `#mean <full name>` line per declaration below.
LEAN_PATH="$(lake env printenv LEAN_PATH):$OUT" lake env lean Run.lean
```

## The abstract (machine-checked round trip)

```lean
Definition:
  ComplexityTests.WordRAMAbstract.AluOp.eval is
    the function mapping an element x of ComplexityTests.WordRAMAbstract.AluOp and a natural number x_1 and a natural number x_2 to
      match x, x_1, x_2 with
      | ComplexityTests.WordRAMAbstract.AluOp.add, x, y => x + y
      | ComplexityTests.WordRAMAbstract.AluOp.sub, x, y => x - y
      | ComplexityTests.WordRAMAbstract.AluOp.mul, x, y => x * y
      | ComplexityTests.WordRAMAbstract.AluOp.div, x, y => x / y
      | ComplexityTests.WordRAMAbstract.AluOp.mod, x, y => x % y
      | ComplexityTests.WordRAMAbstract.AluOp.and, x, y => x &&& y
      | ComplexityTests.WordRAMAbstract.AluOp.or, x, y => x ||| y
      | ComplexityTests.WordRAMAbstract.AluOp.xor, x, y => x ^^^ y
      | ComplexityTests.WordRAMAbstract.AluOp.shl, x, y => x * 2 ^ y
      | ComplexityTests.WordRAMAbstract.AluOp.shr, x, y => x / 2 ^ y.
Abbreviation:
  ComplexityTests.WordRAMAbstract.Program is
    the function mapping a natural number r to
      List (ComplexityTests.WordRAMAbstract.Instr r).
Definition:
  ComplexityTests.WordRAMAbstract.step is
    the function mapping an implicit natural number r and a natural number w and an element p of ComplexityTests.WordRAMAbstract.Program r and an element s of ComplexityTests.WordRAMAbstract.State r to
      match p[s.pc]? with
      | none => ComplexityTests.WordRAMAbstract.Outcome.fault
      | some (ComplexityTests.WordRAMAbstract.Instr.const d x) =>
        (fun (d : Fin r) (x : ℕ) =>
            if x < 2 ^ w then
              (fun (d : Fin r) (x : ℕ) =>
                  ComplexityTests.WordRAMAbstract.Outcome.next
                    { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
                d x
            else ComplexityTests.WordRAMAbstract.Outcome.fault)
          d x
      | some (ComplexityTests.WordRAMAbstract.Instr.copy d i) =>
        (fun (d : Fin r) (x : ℕ) =>
            ComplexityTests.WordRAMAbstract.Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
          d (s.reg i)
      | some (ComplexityTests.WordRAMAbstract.Instr.alu f d i j) =>
        (fun (d : Fin r) (x : ℕ) =>
            if x < 2 ^ w then
              (fun (d : Fin r) (x : ℕ) =>
                  ComplexityTests.WordRAMAbstract.Outcome.next
                    { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
                d x
            else ComplexityTests.WordRAMAbstract.Outcome.fault)
          d (f.eval (s.reg i) (s.reg j))
      | some (ComplexityTests.WordRAMAbstract.Instr.width d) =>
        (fun (d : Fin r) (x : ℕ) =>
            ComplexityTests.WordRAMAbstract.Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
          d w
      | some (ComplexityTests.WordRAMAbstract.Instr.load d «a») =>
        (fun (d : Fin r) (x : ℕ) =>
            ComplexityTests.WordRAMAbstract.Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
          d (s.mem (s.reg «a»))
      | some (ComplexityTests.WordRAMAbstract.Instr.store «a» i) =>
        ComplexityTests.WordRAMAbstract.Outcome.next
          { pc := s.pc + 1, reg := s.reg, mem := Function.update s.mem (s.reg «a») (s.reg i) }
      | some (ComplexityTests.WordRAMAbstract.Instr.jump t) =>
        ComplexityTests.WordRAMAbstract.Outcome.next { pc := t, reg := s.reg, mem := s.mem }
      | some (ComplexityTests.WordRAMAbstract.Instr.branchEq i j t) =>
        ComplexityTests.WordRAMAbstract.Outcome.next
          { pc := if s.reg i = s.reg j then t else s.pc + 1, reg := s.reg, mem := s.mem }
      | some (ComplexityTests.WordRAMAbstract.Instr.branchLt i j t) =>
        ComplexityTests.WordRAMAbstract.Outcome.next
          { pc := if s.reg i < s.reg j then t else s.pc + 1, reg := s.reg, mem := s.mem }
      | some (ComplexityTests.WordRAMAbstract.Instr.halt i) => ComplexityTests.WordRAMAbstract.Outcome.halt (s.reg i).
Definition:
  ComplexityTests.WordRAMAbstract.Halts is
    the function mapping an implicit natural number r and a natural number w and an element p of ComplexityTests.WordRAMAbstract.Program r and an element x of ComplexityTests.WordRAMAbstract.State r and a natural number x_1 and a natural number x_2 to
      Nat.brecOn (motive := fun (x : ℕ) => ComplexityTests.WordRAMAbstract.State r → ℕ → Prop) x_2
        (ComplexityTests.WordRAMAbstract.Halts._f w p) x x_1.
Definition:
  ComplexityTests.WordRAMAbstract.init is
    the function : {r : ℕ} → List ℕ → ComplexityTests.WordRAMAbstract.State r mapping an implicit natural number r and a list input of ℕ elements to
      ({ pc := 0, reg := fun (x : Fin r) => 0, mem := fun («a» : ℕ) => (input.length :: input).getD «a» 0 }).
/tmp/t6-ext/mean-run/Run.lean:8:2: warning: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Definition:
  ComplexityTests.WordRAMAbstract.InputFits is
    the function mapping a natural number w and a list input of ℕ elements to
      input.length < 2 ^ w and (for every natural number x:
        if x ∈ input then
          x < 2 ^ w).
Definition:
  ComplexityTests.WordRAMAbstract.Decides is
    the function mapping an implicit natural number r and an implicit element α of Type u_1 and an element p of ComplexityTests.WordRAMAbstract.Program r and an element A of Set α and a function encode from α to List ℕ and a function T from α to ℕ and a function bits from α to ℕ to
      ∀ («a» : α) (w : ℕ),
        bits «a» ≤ w →
          ComplexityTests.WordRAMAbstract.InputFits w (encode «a») →
            ∃ (v : ℕ) (n : ℕ),
              ComplexityTests.WordRAMAbstract.Halts w p (ComplexityTests.WordRAMAbstract.init (encode «a»)) v n ∧
                n ≤ T «a» ∧ («a» ∈ A → v = 1) ∧ («a» ∉ A → v = 0).
Definition:
  ComplexityTests.WordRAMAbstract.DecidableInTime is
    the function mapping an implicit element α of Type u_1 and an element A of Set α and a function encode from α to List ℕ and a function T from α to ℕ and a function bits from α to ℕ to
      there is a natural number r such that
        there is an element p of (ComplexityTests.WordRAMAbstract.Program r) such that
          ComplexityTests.WordRAMAbstract.Decides p A encode T bits.
```

## Main statements of the bridge (machine-checked round trip)

```lean
Definition:
  ComplexityTests.WordRAMAbstractBridge.OutcomeAgrees is
    the function : {r : ℕ} → ComplexityTests.WordRAMAbstract.Outcome r → Cslib.WordRAM.Outcome r → Prop mapping an implicit natural number r and an element x of ComplexityTests.WordRAMAbstract.Outcome r and an element x_1 of Cslib.WordRAM.Outcome r to
      match x, x_1 with
      | ComplexityTests.WordRAMAbstract.Outcome.next s, Cslib.WordRAM.Outcome.next t =>
        t = { pc := s.pc, data := { regs := s.reg, mem := s.mem } }
      | ComplexityTests.WordRAMAbstract.Outcome.halt v, Cslib.WordRAM.Outcome.halt v' => v = v'
      | ComplexityTests.WordRAMAbstract.Outcome.fault, Cslib.WordRAM.Outcome.fault => True
      | x, x_2 => False.
Definition:
  ComplexityTests.WordRAMAbstractBridge.Same is
    the function mapping an implicit natural number r and an element p of ComplexityTests.WordRAMAbstract.Program r and an element q of Cslib.WordRAM.Program Cslib.WordRAM.Basis.standard r to
      for all natural numbers w and pc:
        ∀ (reg : Fin r → ℕ) (mem : ℕ → ℕ),
          ComplexityTests.WordRAMAbstractBridge.OutcomeAgrees
              (ComplexityTests.WordRAMAbstract.step w p { pc := pc, reg := reg, mem := mem })
              (Cslib.WordRAM.step w q { pc := pc, data := { regs := reg, mem := mem } }) ∧
            ∀ (v n : ℕ),
              ComplexityTests.WordRAMAbstract.Halts w p { pc := pc, reg := reg, mem := mem } v n ↔
                Cslib.WordRAM.Executes w q { pc := pc, data := { regs := reg, mem := mem } } v n.
Theorem ComplexityTests.WordRAMAbstractBridge.runsAgree:
  for every natural number r:
    (∀ (p : ComplexityTests.WordRAMAbstract.Program r),
      ∃ (q : Cslib.WordRAM.Program Cslib.WordRAM.Basis.standard r), ComplexityTests.WordRAMAbstractBridge.Same p q) and (∀ (q : Cslib.WordRAM.Program Cslib.WordRAM.Basis.standard r),
      ∃ (p : ComplexityTests.WordRAMAbstract.Program r), ComplexityTests.WordRAMAbstractBridge.Same p q)
-- Universe parameters: u
Theorem ComplexityTests.WordRAMAbstractBridge.decidableInTime_iff:
  ∀ {α : Type u} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ),
    ComplexityTests.WordRAMAbstract.DecidableInTime A encode T bits ↔
      Cslib.WordRAM.DecidableInTime Cslib.WordRAM.Basis.standard A encode T bits
```

## Reading of `Halts` (not machine-checked)

`Halts w p s v n` holds when, started in state `s` at word size `w`, program `p`
halts with output `v` after exactly `n` instructions, the final `halt` included:

- `Halts w p s v 0` is false: halting takes at least one instruction.
- `Halts w p s v (n + 1)` looks at one step from `s`:
  - if the step goes on to state `t`, then `Halts w p t v n`;
  - if the step halts with output `x`, then `x = v` and `n = 0`;
  - if the step faults, it is false.
