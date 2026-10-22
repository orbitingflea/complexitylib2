def AluOp.eval : AluOp → ℕ → ℕ → Option ℕ
  | .add, x, y => some (x + y)
  | .sub, x, y => if y ≤ x then some (x - y) else none
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x / y)
  | .mod, x, y => if y = 0 then none else some (x % y)
  | .and, x, y => some (x &&& y)
  | .or, x, y => some (x ||| y)
  | .xor, x, y => some (x ^^^ y)
  | .shl, x, y => some (x * 2 ^ y)
  | .shr, x, y => some (x / 2 ^ y)
