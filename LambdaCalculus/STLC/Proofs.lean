import LambdaCalculus.STLC.STLC
import LambdaCalculus.STLC.DSL

-- A simple type derivation `· ⊢ (λx:1. x) : 1 → 1`.
example : TypeDerivation List.nil [stlc| λx:One. x] [stlc_type| One → One] := by
  apply TypeDerivation.lambda
  apply TypeDerivation.var
  constructor

-- A simple operational reduction `(λx:1. x)1 → 1`
example : Red [stlc| ( λx:One . x ) ⟨⟩] [stlc| ⟨⟩] := by
  apply Red.app₃
  rfl
