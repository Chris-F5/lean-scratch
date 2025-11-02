-- clang: I am trying to formalise simply typed λ-calculus.

-- STRUCTURES

universe u

inductive Typ where
| one
| zero
| fun : Typ → Typ → Typ

inductive Exp where
| unit : Exp
| var : Nat → Exp
| app : Exp → Exp → Exp
| lambda : Typ → Exp → Exp

-- Context is indexed with De Bruijn indices.
abbrev Ctx := List Typ


-- TYPE DERIVATIONS

inductive TypeDerivation : Ctx → Exp → Typ → Prop where
| unit : TypeDerivation Γ Exp.unit Typ.one
| var : Γ[x]? = some T → TypeDerivation Γ (Exp.var x) T
| app : (left : TypeDerivation Γ e₁ (Typ.fun T₁ T₂))
      → (right : TypeDerivation Γ e₂ T₁)
      → TypeDerivation Γ (Exp.app e₁ e₂) T₂
| lambda : TypeDerivation (T₁::Γ) e T
         → TypeDerivation Γ (Exp.lambda T₁ e) (Typ.fun T₁ T)


-- UTILITY FUNCTIONS

def sub (e : Exp) (e' : Exp) (x : Nat) : Exp := match e with
| Exp.unit => Exp.unit
| Exp.var x' => if x = x' then e' else Exp.var x'
| Exp.app e₁ e₂ => Exp.app (sub e₁ e' x) (sub e₂ e' x)
| Exp.lambda T e_ => Exp.lambda T (sub e_ e' (x + 1))

def value (e : Exp) : Prop := match e with
| Exp.unit | Exp.var _ | Exp.lambda _ _ => true
| Exp.app _ _ => false


-- OPERATIONAL SEMANTICS

-- A β-reduction of the simply typed lambda calculus.
inductive Red : Exp → Exp → Prop where
| app₁ : Red e₁ e₁' → Red (Exp.app e₁ e₂) (Exp.app e₁' e₂)
| app₂ : value e₁ → Red e₂ e₂' → Red (Exp.app e₁ e₂) (Exp.app e₁ e₂')
| app₃ : value e₂ → Red (Exp.app (Exp.lambda T e) e₂) (sub e e₂ 0)
