def hello := "world"

variable (p q : Prop)

theorem t1 : p ∧ q -> p ∨ q :=
  fun h1 : p ∧ q => And.elim (fun (a : p) (_b : q) => Or.intro_left q a) h1

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q => Or.elim h (fun hp : p => Or.intro_right _ hp) (fun hq : q => Or.intro_left _ hq))
    (fun h : q ∨ p => Or.elim h (fun hq : q => Or.intro_right _ hq) (fun hp : p => Or.intro_left _ hp))

#check Nat

#check Prop
#check True
#check True.intro

example : ∀ n : Nat , 0 ≤ n :=
  fun n : Nat =>
    have : n + 0 = n := Nat.add_zero n
    have : 0 + n = n + 0 := Nat.add_comm 0 n
    have : 0 + n = n  := Eq.trans ‹ 0 + n = n + 0 › ‹ n + 0 = n ›
    Nat.le.intro this

example : ∀ n : Nat , 0 ≤ n :=
  fun n : Nat =>
    calc
      0 ≤ n := by simp []

example : ∃ n : Nat , 20 ≤ n :=
  have : 20 ≤ 25 := by simp []
  Exists.intro 25 ‹ 20 ≤ 25 ›

#check Exists

example : ∃ n : Nat , 20 ≤ n :=
  have : 20 ≤ 25 := by simp []
  ⟨ 25, ‹ 20 ≤ 25 › ⟩

#check Nat × Nat
#check ( 1 , 2 )

-- #check Σ n : Nat,
#check ∃ n : Nat , n > 10
#check Sigma.mk
#check Exists.intro

#check Σ t : Type , t × t

-- 4.6. Exercises
section
  variable (α : Type) (p q : α → Prop)
  
  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    Iff.intro
      (fun h : ∀ x, p x ∧ q x =>
        And.intro
          (fun x => And.left (h x))
          (fun x => And.right (h x))
      )
      (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
        (fun x =>
          And.intro
            (h.left x)
            (h.right x)
        )
      )

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    fun (h1 : ∀ x, p x → q x) (h2 : ∀ x, p x) x => 
      (h1 x) (h2 x)

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    fun (h : (∀ x, p x) ∨ (∀ x, q x)) x =>
      Or.elim h
        (fun h1 : ∀ x, p x => Or.intro_left _ (h1 x))
        (fun h1 : ∀ x, q x => Or.intro_right _ (h1 x))

end

-- §5. Tactics

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := And.intro hp (And.intro hq hp)

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
  
example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · exact And.intro hq hp

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
  
example (α : Type) : ∀ x : α, x = x := by
  intros
  rfl
  
example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => 
    show ∃ x, q x ∨ p x
    exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩
  
example (x : Nat) : x = x := by
  revert x
  intro y
  rfl
  
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  intro h₁
  apply Eq.symm
  assumption
  
--example (x y : Nat) (h : x = y) : y = x := by
--  revert x
--  sorry

#check 3

example : 3 = 3 := by
  generalize 3 = x
  revert x
  exact Eq.refl

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  rw [← h]

example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp
  
example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((0 + y * 1 + z * 0) * (x + 0)) := by
  simp
  rw [Nat.mul_comm]
  assumption
  
open List

example (xs : List Nat) (ys : List Nat) (h : xs = ys)
    : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse ys := by
  simp
  exact h

example (xs ys : List α)
    : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp
  rw [Nat.add_comm]

section
  attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
  attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
  
  example (w x y z : Nat) (p : Nat → Prop)
          (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
    simp at *; assumption
  
  example (x y z : Nat) (p : Nat → Prop)
          (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
          : p (y + 0 + x) ∧ p (z * x) := by
    simp at * <;> constructor <;> assumption
end section

section
  variable (k : Nat) (f : Nat → Nat)
  example (h₁ : f 0 = 0) (h₂ : 0 = k) : f k = 0 := by
    simp [←h₂, h₁]
end section

section
  def f (x y z : Nat) : Nat :=
    match x, y, z with
    | 5, _, _ => y
    | _, 5, _ => y
    | _, _, 5 => y
    | _, _, _ => 1
    
  example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
    intros
    simp [f]
    split <;> first | contradiction | rfl
end section

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply And.intro | apply Or.intro_left; exact hp | apply Or.intro_right | exact hp)

/--
error: Type mismatch
  "Not a number"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in
def x : Nat := "Not a number"

inductive Color where
  | red : Color
  | blue : Color
  | green : Color
  
#check Color
#check Color.red
#check Color.rec
#check Color.casesOn

example (c : Color) : c = Color.red ∨ c = Color.blue ∨ c = Color.green := by
  cases c <;> simp

#eval Color.red

structure Pair where
  x : Nat
  y : Nat

structure Monoid where
  S : Type u
  op : S -> S -> S
  op_assoc : ∀a b c, op (op a b) c = op (op a b) c

#check Pair

-- CONTINUE: §7.4. Defining the Natural Numbers

inductive Mat where
  | zero : Mat
  | succ : Mat → Mat

namespace Mat
  def add (x y : Mat) : Mat := match x with
    | zero => y
    | succ n => succ (add n y)
end Mat

#eval Mat.add (Mat.succ Mat.zero) (Mat.succ (Mat.succ (Mat.zero)))

example (n : Mat)
    : Mat.add Mat.zero n = n :=
  Mat.rec
    (motive := fun x : Mat => Mat.add Mat.zero x = x)
    (zero := by
      simp [Mat.add]
    )
    (succ := by
      intro a h
      rw [Mat.add]
    )
    n

-- INDUCTION ON MY LIST CONSTRUCTION

universe u

inductive MyList {α : Type u} where
| empty : MyList
| cons : α → MyList → MyList

def my_len {α : Type u} (l : @MyList α) : Nat :=
  match l with
  | .empty => 0
  | .cons _ xs => 1 + my_len (xs)

def my_cat {α : Type u} (l₁ : @MyList α) (l₂ : @MyList α) : @MyList α :=
  match l₁ with
  | .empty => l₂
  | .cons x xs => MyList.cons x (my_cat xs l₂)

#eval my_len (MyList.cons 1 (MyList.cons 2 MyList.empty))
#eval my_cat (MyList.cons 1 (MyList.cons 2 MyList.empty)) (MyList.cons 3 MyList.empty)

theorem my_list_cons_len (α : Type u) (l₁ l₂ : @MyList α)
    : (my_len l₁) + (my_len l₂) = my_len (my_cat l₁ l₂)
  := by
  cases l₁ with
  | empty =>
    simp [my_cat, my_len]
  | cons x xs =>
    -- CR clang: how does lean know this is well-founded?
    -- unfold my_cat
    have := my_list_cons_len α xs l₂
    rw [my_cat, my_len, my_len, Nat.add_assoc, this]

example (α : Type u) (l₁ l₂ : @MyList α)
    : (my_len l₁) + (my_len l₂) = my_len (my_cat l₁ l₂)
  := by
  induction l₁ with
  | empty => simp [my_cat, my_len]
  | cons x xs =>
    simp [my_cat, my_len, Nat.add_assoc]
    assumption

-- rw [my_cat, my_len, my_len, Nat.add_assoc] ; simp ; assumption

example : (a : List k) → List k := fun a : List k => a

-- §7.3. INDUCTIVLY DEFINED PROPOSITIONS

inductive MyExists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : MyExists p

-- §7.7. INDUCTIVE FAMILIES

inductive EvenDerivation : Nat → Prop where
  | zero_even : EvenDerivation 0
  | next_even : EvenDerivation n → EvenDerivation (n + 2)

example : EvenDerivation 10 := by
  have := EvenDerivation.zero_even
  repeat (first | assumption | apply EvenDerivation.next_even)

inductive MyVec (α : Type u) : Nat → Type u where
  | nil : MyVec α 0
  | cons : α → {n : Nat} → MyVec α n → MyVec α (n + 1)

#check MyVec.nil
#check MyVec.cons 1 MyVec.nil

inductive MyTest (n : Nat) : Prop where
  | nil : MyTest n
inductive MyCounter : Nat → Prop where
  | nil : MyCounter 0

#check MyTest 1
#check MyCounter 0   -- a proposition
#check MyCounter.nil -- a proof of the `MyCounter 0` proposition

inductive MultipleDerivation (m : Nat) : Nat → Prop where
  | zero : MultipleDerivation m 0
  | next : MultipleDerivation m n → MultipleDerivation m (n + m)

example : MultipleDerivation 3 9 := by
  apply MultipleDerivation.next
  repeat (first | apply MultipleDerivation.zero | apply MultipleDerivation.next)

inductive MyExiststential (α : Type u) (f : α → Prop) : Prop where
  | witness (w : α) : (f w) → MyExiststential α f

#check MyExiststential.rec

example : MyExiststential Nat (· * 2 = 8) :=
  MyExiststential.witness 4 (by simp)

inductive MyTripple : Nat → Prop where
  | zero : MyTripple 0
  | next : MyTripple n → MyTripple (n+3)

#check MyTripple.next

inductive MyEq {α : Sort u} (a : α) : α → Prop where
  | refl : MyEq a a

#check MyEq.refl
#check MyEq.rec

-- PATTERN MATCHING

def f_match : @MyList Nat → Nat
  | .empty => 0
  | .cons _ xs => 1 + (f_match xs)

#eval f_match (MyList.cons 1 (MyList.cons 2 MyList.empty))

-- INDUCTIVE TYPE EXERCISE 3

inductive Expr where
| const : Nat → Expr
| var : Nat → Expr
| plus : Expr → Expr → Expr
| times : Expr → Expr → Expr

def eval (store : Nat → Option Nat) (e : Expr) : Option Nat :=
  match e with
  | .const n => some n
  | .var x => store x
  | .plus e₁ e₂ => (match (eval store e₁, eval store e₂) with
    | (some n₁, some n₂) => some (n₁ + n₂)
    | _ => none)
  | .times e₁ e₂ => (match (eval store e₁, eval store e₂) with
    | (some n₁, some n₂) => some (n₁ * n₂)
    | _ => none)


-- §8. INDUCTION AND RECURSION

def foo : Nat → Nat → Bool
  | 0, 0 => true
  | n+1, m+1 => foo n m
  | _, _ => false

theorem succ_add : ∀ n m : Nat, foo n m → foo (n + 1) (m + 1)
  | 0, 0, _ => rfl
  | n+1, m+1, h => succ_add n m h

theorem zero_add : ∀ n , n + 0 = n
  | 0 => rfl
  | _+1 => rfl
