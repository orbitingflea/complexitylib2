def Halts (w : ℕ) (p : Program r) : State r → ℕ → ℕ → Prop
  | _, _, 0 => False
  | s, v, n + 1 =>
    match step w p s with
    | .next t => Halts w p t v n
    | .halt x => x = v ∧ n = 0
    | .fault => False
