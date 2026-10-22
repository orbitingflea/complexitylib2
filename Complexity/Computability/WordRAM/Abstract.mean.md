# Mean rendering of the word-RAM abstract

This file shows the definitions and main statements of
[`Abstract.lean`](Abstract.lean) as rendered by
[Mean](https://github.com/edemaine/mean), commit
`b142d108aeb2dbba04fb292c0530887031b206f0` (2026-10-15).

## What was checked

- Mean pins Lean `v4.35.0` and Mathlib `v4.35.0`. This repository uses Lean `v4.36.0-rc1`.
  Mean's three modules (`Mean/Syntax.lean`, `Mean/RoundTrip.lean`, `Mean/Render.lean`)
  compiled without change against this repository's toolchain and Mathlib, outside the
  repository. Mean is not a dependency of this repository.
- `#mean` ran on the ten declarations below. For each one, Mean parsed its own output
  back, elaborated it, and checked that it gives the same Lean expression (its
  round-trip check). All ten passed. The output below is verbatim.
- Mean's vocabulary is small. Much of the output is still Lean notation (`match`,
  `∀`, `∃`, `→`); only the outer binders and some quantifiers became English.
- `Halts` is defined by recursion. Mean renders its compiled form (`Nat.brecOn`), which
  says nothing to a reader. The reading of `Halts` at the end of this file is written
  by hand and is **not machine-checked**.

To reproduce (from the repository root, with Mean cloned at `$MEAN` and an empty
folder `$OUT`):

```sh
mkdir -p "$OUT/Mean"
for f in Syntax RoundTrip Render; do
  LEAN_PATH="$(lake env printenv LEAN_PATH):$OUT" lake env lean -R "$MEAN" \
    -o "$OUT/Mean/$f.olean" "$MEAN/Mean/$f.lean"
done
lake build Complexity.Computability.WordRAM.Abstract
# Run.lean: `import Mean.Render`, `import Complexity.Computability.WordRAM.Abstract`,
# then one `#mean Cslib.WordRAM.Abstract.<name>` line per declaration below.
LEAN_PATH="$(lake env printenv LEAN_PATH):$OUT" lake env lean Run.lean
```

## Mean output (machine-checked round trip)

```lean
Definition:
  Cslib.WordRAM.Abstract.AluOp.eval is
    the function mapping an element x of Cslib.WordRAM.Abstract.AluOp and a natural number x_1 and a natural number x_2 to
      match x, x_1, x_2 with
      | Cslib.WordRAM.Abstract.AluOp.add, x, y => x + y
      | Cslib.WordRAM.Abstract.AluOp.sub, x, y => x - y
      | Cslib.WordRAM.Abstract.AluOp.mul, x, y => x * y
      | Cslib.WordRAM.Abstract.AluOp.div, x, y => x / y
      | Cslib.WordRAM.Abstract.AluOp.mod, x, y => x % y
      | Cslib.WordRAM.Abstract.AluOp.and, x, y => x &&& y
      | Cslib.WordRAM.Abstract.AluOp.or, x, y => x ||| y
      | Cslib.WordRAM.Abstract.AluOp.xor, x, y => x ^^^ y
      | Cslib.WordRAM.Abstract.AluOp.shl, x, y => x * 2 ^ y
      | Cslib.WordRAM.Abstract.AluOp.shr, x, y => x / 2 ^ y.
Definition:
  Cslib.WordRAM.Abstract.step is
    the function mapping an implicit natural number r and a natural number w and an element p of Cslib.WordRAM.Abstract.Program r and an element s of Cslib.WordRAM.Abstract.State r to
      match p[s.pc]? with
      | none => Cslib.WordRAM.Abstract.Outcome.fault
      | some (Cslib.WordRAM.Abstract.Instr.const d x) =>
        (fun (d : Fin r) (x : ℕ) =>
            if x < 2 ^ w then
              (fun (d : Fin r) (x : ℕ) =>
                  Cslib.WordRAM.Abstract.Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
                d x
            else Cslib.WordRAM.Abstract.Outcome.fault)
          d x
      | some (Cslib.WordRAM.Abstract.Instr.copy d i) =>
        (fun (d : Fin r) (x : ℕ) =>
            Cslib.WordRAM.Abstract.Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
          d (s.reg i)
      | some (Cslib.WordRAM.Abstract.Instr.alu f d i j) =>
        (fun (d : Fin r) (x : ℕ) =>
            if x < 2 ^ w then
              (fun (d : Fin r) (x : ℕ) =>
                  Cslib.WordRAM.Abstract.Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
                d x
            else Cslib.WordRAM.Abstract.Outcome.fault)
          d (f.eval (s.reg i) (s.reg j))
      | some (Cslib.WordRAM.Abstract.Instr.width d) =>
        (fun (d : Fin r) (x : ℕ) =>
            Cslib.WordRAM.Abstract.Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
          d w
      | some (Cslib.WordRAM.Abstract.Instr.load d «a») =>
        (fun (d : Fin r) (x : ℕ) =>
            Cslib.WordRAM.Abstract.Outcome.next { pc := s.pc + 1, reg := Function.update s.reg d x, mem := s.mem })
          d (s.mem (s.reg «a»))
      | some (Cslib.WordRAM.Abstract.Instr.store «a» i) =>
        Cslib.WordRAM.Abstract.Outcome.next
          { pc := s.pc + 1, reg := s.reg, mem := Function.update s.mem (s.reg «a») (s.reg i) }
      | some (Cslib.WordRAM.Abstract.Instr.jump t) =>
        Cslib.WordRAM.Abstract.Outcome.next { pc := t, reg := s.reg, mem := s.mem }
      | some (Cslib.WordRAM.Abstract.Instr.branchEq i j t) =>
        Cslib.WordRAM.Abstract.Outcome.next { pc := if s.reg i = s.reg j then t else s.pc + 1, reg := s.reg, mem := s.mem }
      | some (Cslib.WordRAM.Abstract.Instr.branchLt i j t) =>
        Cslib.WordRAM.Abstract.Outcome.next { pc := if s.reg i < s.reg j then t else s.pc + 1, reg := s.reg, mem := s.mem }
      | some (Cslib.WordRAM.Abstract.Instr.halt i) => Cslib.WordRAM.Abstract.Outcome.halt (s.reg i).
Definition:
  Cslib.WordRAM.Abstract.Halts is
    the function mapping an implicit natural number r and a natural number w and an element p of Cslib.WordRAM.Abstract.Program r and an element x of Cslib.WordRAM.Abstract.State r and a natural number x_1 and a natural number x_2 to
      Nat.brecOn (motive := fun (x : ℕ) => Cslib.WordRAM.Abstract.State r → ℕ → Prop) x_2
        (Cslib.WordRAM.Abstract.Halts._f w p) x x_1.
Definition:
  Cslib.WordRAM.Abstract.init is
    the function : {r : ℕ} → List ℕ → Cslib.WordRAM.Abstract.State r mapping an implicit natural number r and a list input of ℕ elements to
      ({ pc := 0, reg := fun (x : Fin r) => 0, mem := fun («a» : ℕ) => (input.length :: input).getD «a» 0 }).
Definition:
  Cslib.WordRAM.Abstract.InputFits is
    the function mapping a natural number w and a list input of ℕ elements to
      input.length < 2 ^ w and (for every natural number x:
        if x ∈ input then
          x < 2 ^ w).
Definition:
  Cslib.WordRAM.Abstract.Decides is
    the function mapping an implicit natural number r and an implicit element α of Type u and an element p of Cslib.WordRAM.Abstract.Program r and an element A of Set α and a function encode from α to List ℕ and a function T from α to ℕ and a function bits from α to ℕ to
      ∀ («a» : α) (w : ℕ),
        bits «a» ≤ w →
          Cslib.WordRAM.Abstract.InputFits w (encode «a») →
            ∃ (v : ℕ) (n : ℕ),
              Cslib.WordRAM.Abstract.Halts w p (Cslib.WordRAM.Abstract.init (encode «a»)) v n ∧
                n ≤ T «a» ∧ («a» ∈ A → v = 1) ∧ («a» ∉ A → v = 0).
Definition:
  Cslib.WordRAM.Abstract.DecidableInTime is
    the function mapping an implicit element α of Type u and an element A of Set α and a function encode from α to List ℕ and a function T from α to ℕ and a function bits from α to ℕ to
      there is a natural number r such that
        there is an element p of (Cslib.WordRAM.Abstract.Program r) such that
          Cslib.WordRAM.Abstract.Decides p A encode T bits.
Definition:
  Cslib.WordRAM.Abstract.RunsAgree is
    for every natural number r:
      (∀ (p : Cslib.WordRAM.Abstract.Program r),
        ∃ (q : Cslib.WordRAM.Program Cslib.WordRAM.Basis.standard r), Cslib.WordRAM.Abstract.RunsAgree.Same p q) and (∀ (q : Cslib.WordRAM.Program Cslib.WordRAM.Basis.standard r),
        ∃ (p : Cslib.WordRAM.Abstract.Program r), Cslib.WordRAM.Abstract.RunsAgree.Same p q).
Definition:
  Cslib.WordRAM.Abstract.RunsAgree.Same is
    the function mapping an implicit natural number r and an element p of Cslib.WordRAM.Abstract.Program r and an element q of Cslib.WordRAM.Program Cslib.WordRAM.Basis.standard r to
      for all natural numbers w and pc:
        ∀ (reg : Fin r → ℕ) (mem : ℕ → ℕ),
          (Cslib.WordRAM.Abstract.step w p { pc := pc, reg := reg, mem := mem } = Cslib.WordRAM.Abstract.Outcome.fault ↔
              Cslib.WordRAM.step w q { pc := pc, data := { regs := reg, mem := mem } } = Cslib.WordRAM.Outcome.fault) ∧
            ∀ (v n : ℕ),
              Cslib.WordRAM.Abstract.Halts w p { pc := pc, reg := reg, mem := mem } v n ↔
                Cslib.WordRAM.Executes w q { pc := pc, data := { regs := reg, mem := mem } } v n.
Definition:
  Cslib.WordRAM.Abstract.DecidableInTimeAgrees is
    ∀ {α : Type u} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ),
      Cslib.WordRAM.Abstract.DecidableInTime A encode T bits ↔
        Cslib.WordRAM.DecidableInTime Cslib.WordRAM.Basis.standard A encode T bits.
```

## Reading of `Halts` (not machine-checked)

`Halts w p s v n` holds when, started in state `s` at word size `w`, program `p`
halts with output `v` after exactly `n` instructions, the final `halt` included:

- `Halts w p s v 0` is false: halting takes at least one instruction.
- `Halts w p s v (n + 1)` looks at one step from `s`:
  - if the step goes on to state `t`, then `Halts w p t v n`;
  - if the step halts with output `x`, then `x = v` and `n = 0`;
  - if the step faults, it is false.
