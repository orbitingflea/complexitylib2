def Decides {α : Type*} (p : Program r) (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ) :
    Prop :=
  ∀ a w, bits a ≤ w → InputFits w (encode a) →
    ∃ v n, Halts w p (init (encode a)) v n ∧ n ≤ T a ∧ (a ∈ A → v = 1) ∧ (a ∉ A → v = 0)
