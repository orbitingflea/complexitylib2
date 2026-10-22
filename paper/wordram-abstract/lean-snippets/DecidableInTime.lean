def DecidableInTime {α : Type*} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ) : Prop :=
  ∃ r, ∃ p : Program r, Decides p A encode T bits
