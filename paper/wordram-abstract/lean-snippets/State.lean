structure State (r : ℕ) where
  pc : ℕ
  reg : Fin r → ℕ
  mem : ℕ → ℕ
