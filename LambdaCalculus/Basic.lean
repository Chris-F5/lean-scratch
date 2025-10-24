import Lean

-- TRYING TO FORMALISE SIMPLY TYPED λ-CALCULUS

section
  universe u
  
  def α := String deriving Repr, DecidableEq
  
  inductive T where
    | one
    | zero
    | fun : T → T → T
  deriving Repr
  
  inductive E where
    | unit : E
    | var : α → E
    | app : E → E → E
    | lambda : α → T → E → E
  deriving Repr

  -- SYNTAX

  open Lean Elab Meta

  declare_syntax_cat stlc_expr
  declare_syntax_cat stlc_type
  declare_syntax_cat stlc_var
  
  syntax "[stlc|" stlc_expr "]" : term

  syntax:100 "Zero" : stlc_type
  syntax:100 "One" : stlc_type
  syntax:50 stlc_type:51 "→" stlc_type:50 : stlc_type
  
  syntax:100 ident : stlc_expr
  syntax:100 "<>" : stlc_expr
  syntax:90 stlc_expr:90 stlc_expr:91 : stlc_expr
  syntax:80 "λ" ident ":" stlc_type "." stlc_expr : stlc_expr
  
  partial def elab_stlc_type : Syntax → MetaM Expr
    | `(stlc_type| Zero) => mkAppM ``T.zero #[]
    | `(stlc_type| One) => mkAppM ``T.one #[]
    | `(stlc_type| $T₁:stlc_type → $T₂:stlc_type) => do
      let T₁ ← elab_stlc_type T₁
      let T₂ ← elab_stlc_type T₂
      mkAppM ``T.fun #[T₁, T₂]
    | _ => throwUnsupportedSyntax

  partial def elab_stlc_expr : Syntax → MetaM Expr
    | `(stlc_expr| $x:ident) => do
      let x : Expr := mkStrLit x.getId.toString
      mkAppM ``E.var #[x] -- CR clang: I can probably get rid of this application.
    | `(stlc_expr| <>) => mkAppM ``E.unit #[]
    | `(stlc_expr| $e₁:stlc_expr $e₂:stlc_expr) => do
      let e₁ ← elab_stlc_expr e₁
      let e₂ ← elab_stlc_expr e₂
      mkAppM ``E.app #[e₁, e₂]
    | `(stlc_expr| λ $x:ident : $T:stlc_type . $e:stlc_expr) => do
      let x : Expr := mkStrLit x.getId.toString
      let T ← elab_stlc_type T
      let e ← elab_stlc_expr e
      mkAppM ``E.lambda #[x, T, e]
    | _ => throwUnsupportedSyntax

  elab "[stlc_type|" T:stlc_type "]" : term => elab_stlc_type T
  elab "[stlc|" e:stlc_expr "]" : term => elab_stlc_expr e

  #check [stlc_type| One → One ]
  #check [stlc| λ x:One→One→One. λ y:One. x y y ]

  -- OPERATIONAL SEMANTICS

  def sub (e : E) (e' : E) (x' : α) : E :=
    match e with
    | E.unit => E.unit
    | E.var x => if x = x' then e' else E.var x
    | E.app e₁ e₂ => E.app (sub e₁ e' x') (sub e₂ e' x')
    | E.lambda x t e_ => if x = x'
      then E.lambda x t e
      else E.lambda x t (sub e_ e' x')


  def value (e : E) : Bool := match e with
  | E.unit => true
  | E.var _ => true
  | E.app e₁ e₂ =>
    (value e₂) && (match e₁ with | E.lambda _ _ _ => false | _ => value e₁)
  | E.lambda _ _ e => value e

  def step (e : E) : Option (E) :=
    match e with
    | E.unit => none
    | E.var _ => none
    | E.lambda x t e =>
      (match (step e) with | some e' => E.lambda x t e' | none => none )
    | E.app e₁ e₂ => (match (value e₁), (step e₁), (value e₂), (step e₂) with
      | _,_,false,none => none
      | false,none,_,_ => none
      | _,_,false,some e₂' => E.app e₁ e₂'
      | false,some e₁',true,_ => E.app e₁' e₂
      | true,_,true,_ => (match e₁ with
        | E.lambda x _ e_ => some (sub e_ e₂ x)
        | _ => none
        )
      )

  #eval step (E.app (E.lambda "x" T.one (E.var "x")) E.unit)
end
