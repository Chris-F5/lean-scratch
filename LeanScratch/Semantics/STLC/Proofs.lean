import LeanScratch.Semantics.STLC.STLC
import LeanScratch.Semantics.STLC.DSL

-- A simple type derivation `· ⊢ (λx:1. x) : 1 → 1`.
example
    : TypeDerivation
        List.nil
        [stlc| λOne→One. λOne. (λOne. 2 ⟨⟩) 0]
        [stlc_type| (One → One) → One → One]
  := by
  repeat apply TypeDerivation.lambda
  -- CR clang: Why does a.a prefix the cases?
  -- CR clang: Why does `apply TypeDerivation.app` require me to
  --           create a Typ? And why is it getting filled automatically.
  apply TypeDerivation.app
  case a.a.left =>
    apply TypeDerivation.lambda
    apply TypeDerivation.app
    case a.left =>
      apply TypeDerivation.var
      constructor
    case a.right =>
      apply TypeDerivation.unit
  case a.a.right =>
    apply TypeDerivation.var
    constructor

-- A simple operational reduction `(λx:1. x)1 → 1`
example : Red [stlc| (λOne.0) ⟨⟩] [stlc| ⟨⟩] := by
  apply Red.app₃
  rfl

-- exchange -> weakening -> substitution

/-
theorem substitution
  (h₁ : TypeDerivation ((x, T') :: Γ) e T)
  (h₂ : TypeDerivation Γ e' T')
    : TypeDerivation Γ (sub e e' x) T
  := by
  -- We proceed by induction on `x:T',Γ ⊢ e : T`,
  -- showing in each case that `Γ ⊢ e[e'/x] : T`
  -- induction h₁ with -- this does not work
  cases h₁ with
  | unit => apply TypeDerivation.unit
  | app =>
    unfold sub
    apply TypeDerivation.app
-/

-- This substitution theorem is slightly weaker than the one shown
-- in the lecture slids. Because we are only substituting one free
-- variable at a time. I think this theorem is strong enough for
-- type preservation though.
theorem substitution
  (x : Nat)
    : Γ[x]? = some T'
    → TypeDerivation Γ e T
    → TypeDerivation Γ e' T'
    → TypeDerivation Γ (sub e e' x) T
  := by
  intros
  cases ‹TypeDerivation Γ e T› with
  | unit =>
    unfold sub
    apply TypeDerivation.unit
  | var =>
    rename Nat => x'
    unfold sub
    by_cases (x = x')
    · simp [‹x = x'›]
      simp [*] at *
      simp [‹T = T'›]
      assumption
    · simp [‹x ≠ x'›]
      exact TypeDerivation.var ‹Γ[x']? = some T›
  | app left right =>
    unfold sub
    apply TypeDerivation.app
    case app.left =>
      -- CR clang: How does lean know that this induction is well-founded?
      exact substitution x ‹Γ[x]? = some T'› left  ‹TypeDerivation Γ e' T'›
    case app.right =>
      exact substitution x ‹Γ[x]? = some T'› right ‹TypeDerivation Γ e' T'›
  | lambda h =>
    unfold sub
    apply TypeDerivation.lambda
    -- CR clang: here I think I'm stuck because I cant apply the theorem
    --           inductivly with substitution variable != 0.
    have := substitution (x + 1) (by sorry) h ‹TypeDerivation Γ e' T'›
