def Same (p : Abstract.Program r) (q : Program .standard r) : Prop :=
  ∀ w pc reg mem,
    OutcomeAgrees (Abstract.step w p ⟨pc, reg, mem⟩) (step w q ⟨pc, ⟨reg, mem⟩⟩) ∧
    ∀ v n, Abstract.Halts w p ⟨pc, reg, mem⟩ v n ↔ Executes w q ⟨pc, ⟨reg, mem⟩⟩ v n
