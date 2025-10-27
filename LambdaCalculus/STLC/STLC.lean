-- clang: I am trying to formalise simply typed λ-calculus.

-- STRUCTURES

universe u

def Var := String deriving DecidableEq

inductive Typ where
| one
| zero
| fun : Typ → Typ → Typ

inductive Exp where
| unit : Exp
| var : Var → Exp
| app : Exp → Exp → Exp
| lambda : Var → Typ → Exp → Exp

def Ctx := List (Var × Typ) deriving Membership


-- TYPE DERIVATIONS

inductive TypeDerivation : Ctx → Exp → Typ → Prop where
| unit : TypeDerivation Γ Exp.unit Typ.one
| var : ((x,T) ∈ Γ) → TypeDerivation Γ (Exp.var x) T
| app : TypeDerivation Γ e₁ (Typ.fun T₁ T₂)
      → TypeDerivation Γ e₂ T₁
      → TypeDerivation Γ (Exp.app e₁ e₂) T₂
| lambda : TypeDerivation ((x,T₁)::Γ) e T
         → TypeDerivation Γ (Exp.lambda x T₁ e) (Typ.fun T₁ T)


-- UTILITY FUNCTIONS

def sub (e : Exp) (e' : Exp) (x' : Var) : Exp := match e with
| Exp.unit => Exp.unit
| Exp.var x => if x = x' then e' else Exp.var x
| Exp.app e₁ e₂ => Exp.app (sub e₁ e' x') (sub e₂ e' x')
| Exp.lambda x t e_ => if x = x'
  then Exp.lambda x t e
  else Exp.lambda x t (sub e_ e' x')

def value (e : Exp) : Prop := match e with
| Exp.unit | Exp.var _ | Exp.lambda _ _ _ => true
| Exp.app _ _ => false


-- OPERATIONAL SEMANTICS

-- A β-reduction of the simply typed lambda calculus.
inductive Red : Exp → Exp → Prop where
| app₁ : Red e₁ e₁' → Red (Exp.app e₁ e₂) (Exp.app e₁' e₂)
| app₂ : value e₁ → Red e₂ e₂' → Red (Exp.app e₁ e₂) (Exp.app e₁ e₂')
| app₃ : value e₂ → Red (Exp.app (Exp.lambda x T e) e₂) (sub e e₂ x)


-- TODO: prove this only generates valid reductions.
/-
def step (e : Exp) : Option (Exp) :=
match e with
| Exp.unit => none
| Exp.var _ => none
| Exp.lambda x t e => none
| Exp.app e₁ e₂ => (match (value e₁), (step e₁), (value e₂), (step e₂) with
  | _,_,false,none => none
  | false,none,_,_ => none
  | _,_,false,some e₂' => Exp.app e₁ e₂'
  | false,some e₁',true,_ => Exp.app e₁' e₂
  | true,_,true,_ => (match e₁ with
    | Exp.lambda x _ e_ => some (sub e_ e₂ x)
    | _ => none
    )
  )
-/
