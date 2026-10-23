inductive Outcome (r : ℕ)
  | next (s : State r)
  | halt (v : ℕ)
  | fault
