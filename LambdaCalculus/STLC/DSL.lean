import Lean
import LambdaCalculus.STLC.STLC

-- SYNTAX

open Lean Elab Meta

declare_syntax_cat stlc_expr
declare_syntax_cat stlc_type
declare_syntax_cat stlc_var

syntax "[stlc_type|" stlc_type "]" : term
syntax "[stlc|" stlc_expr "]" : term

syntax:100 "Zero" : stlc_type
syntax:100 "One" : stlc_type
syntax:50 stlc_type:51 "→" stlc_type:50 : stlc_type

syntax:100 ident : stlc_expr
syntax:100 "⟨⟩" : stlc_expr
syntax:99 "(" stlc_expr ")" : stlc_expr
syntax:90 stlc_expr:90 stlc_expr:91 : stlc_expr
syntax:80 "λ" ident ":" stlc_type "." stlc_expr : stlc_expr

partial def elab_stlc_type : Syntax → MetaM Expr
| `(stlc_type| Zero) => mkAppM ``Typ.zero #[]
| `(stlc_type| One) => mkAppM ``Typ.one #[]
| `(stlc_type| $T₁:stlc_type → $T₂:stlc_type) => do
  let T₁ ← elab_stlc_type T₁
  let T₂ ← elab_stlc_type T₂
  mkAppM ``Typ.fun #[T₁, T₂]
| _ => throwUnsupportedSyntax

partial def elab_stlc_expr : Syntax → MetaM Expr
| `(stlc_expr| $x:ident) => do
  let x : Expr := mkStrLit x.getId.toString
  mkAppM ``Exp.var #[x] -- CR clang: I can probably get rid of this application.
| `(stlc_expr| ⟨⟩) => mkAppM ``Exp.unit #[]
| `(stlc_expr| ( $e:stlc_expr )) => elab_stlc_expr e
| `(stlc_expr| $e₁:stlc_expr $e₂:stlc_expr) => do
  let e₁ ← elab_stlc_expr e₁
  let e₂ ← elab_stlc_expr e₂
  mkAppM ``Exp.app #[e₁, e₂]
| `(stlc_expr| λ $x:ident : $T:stlc_type . $e:stlc_expr) => do
  let x : Expr := mkStrLit x.getId.toString
  let T ← elab_stlc_type T
  let e ← elab_stlc_expr e
  mkAppM ``Exp.lambda #[x, T, e]
| _ => throwUnsupportedSyntax

elab "[stlc_type|" T:stlc_type "]" : term => elab_stlc_type T
elab "[stlc|" e:stlc_expr "]" : term => elab_stlc_expr e

#check [stlc_type| One → One ]
#check [stlc| λ x:One→One→One. λ y:One. x y y ]
