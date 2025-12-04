--import Mathlib.Tactic
--import Mathlib.Order.Defs.Unbundled


/- let's declare some variables to represent logical propositions -/
variable (P Q R : Prop)

/- From our point-of-view, a proposition represents a mathematical
statement, which may or may not have a proof.

From a computer-language point of view, `P` and `Q` and `R` are *types*.
And a *term* `p` of type `P` -- indicated with the syntax `p:P` --
should represent a *proof* of the proposition `P`.
-/

/- Logical And and Or -/

-- if we have a proof of `P` and a proof of `Q`, then we have a proof of `P ∧ Q`
example (p : P) (q : Q) : P ∧ Q := ⟨ p,q ⟩

-- if we have a proof of `P`, then we have a proof of `P ∨ Q`
example (p : P) : P ∨ Q := Or.inl p


-- if we have a proof of `Q`, then we have a proof of `P ∨ Q`
example (q : Q) : P ∨ Q := Or.inr q


/- We know that the logical statement `P is true` toegether with
`P implies Q` should imply that `Q is true`.

This is a logical assertion which goes by the name *modus ponens*.

Let's prove that *modus ponens* holds, using Lean. -/

theorem modus_ponens : P ∧ (P → Q) → Q := by
sorry

/- It may seem a bit strange, but we view the type `P` as representing
`(all) proofs of P`.

So a function `P → Q` is then a function from `proofs of P`
to `proofs of Q`.

From this point of view, for `P Q : Prop` the function type `P → Q`
is the same thing as logical implication.
-/

/- Logical negation

How to define the proposition `not P`??

Need the type `False`.

`False` is a type with no terms.
-/

#check False

/- anything follows from `False`! -/

example : ∀ P:Prop, False → P := by
  intro P
  apply False.rec

/- Proving the negation of the proposition `P` -- i.e. proving that
`P` is not true -- amounts to proving  that `P implies False` --
i.e. exhibiting a term of type `P → False`.

The syntax `¬ P` is shorthand for `P → False`. -/

example (hnp : ¬ P) : ¬ (P ∧ Q) := by
  sorry

example (hnp : ¬ P) (hnq : ¬ Q) : ¬ (P ∨ Q) := by
  sorry

/- Let's *prove* that contraposition is valid.

  Thus we show that `P → Q` if and only if `¬ Q → ¬ P`.

-/

theorem contraposition : (P → Q) <-> (¬ Q → ¬ P) := by
  constructor
  · intro hpq nq p
    exact nq (hpq p)
  · intro hnqnp
    by_cases hq : Q
    · intro _
      exact hq
    · intro p
      exfalso
      exact hnqnp hq p


/- Other types.

`Prop` is not the only type in Lean.

`Ty:Type` means that `Ty` is some sort of data-carrying type.

For example `Nat : Type` -- i.e. the natural numbers form a type.

Simlarly `Int : Type` is the type of integers.

In some sense, one might think of a `Type` as an analogue of a `Set`.
-/

#check Nat
#check Int

#check -2^151
#eval (-2)^151

/- some other types 

  `Bool` is the type of Boolean values (`True` or `False`)
  
  `String` is the type of alphanumeric strings

  Given a type `α`, `List α` denotes the type of lists of terms of type `α`
  
-/

#check True -- Prop
#check true -- Bool

example : List Nat := [ 0,2,4,6,8 ]

def list_multiples (m n : Nat) : List Nat :=
  match n with
  | 0 => []
  | Nat.succ n => m*n :: (list_multiples m n)

#eval list_multiples 9 20

def isEvenBool (n : Nat) : Bool := Nat.mod n 2 == 0

#eval List.map isEvenBool (list_multiples 9 20)

#eval List.filter isEvenBool (list_multiples 9 20)


/-   Given `α β : Type`, we can form new types. 
   
    *Product type*:
    
    `α × β` is the type of ordered pairs `⟨x,y⟩` with `x:α` and `y:β`.
 
    *Sum type*: 
    
    `α ⊕ β` is the type of terms which can be *either* of type `α` *or* of type `β`.
    
   -/

example : String ⊕ Nat := Sum.inl "foo"

def half (n : Nat) : String ⊕ Nat :=
  if isEvenBool n then 
    Sum.inr (Nat.div n 2) 
  else 
    Sum.inl s!"Error: {n} not even"

#eval half 248
#eval half 247


/- Function types.

   For types `α β : Type`, we can consider functions from
   `α` to `β`; the type of all such functions is written
   `α → β`.  Thus, the syntax `f:α → β`  indicates that `f` is a function 
   which takes argumnets of type `α` and returns values of type `β`. -/
   
def f : Nat → Nat := fun x => x^3 + 2*x^2 + 1

def ev : Nat → Bool := fun x => if Nat.mod x 2 == 0 then True else False  

#eval f 301

#eval ev 2025

#eval ev 2026

-- more subtle

def Pev : Nat → Prop := fun x => Nat.mod x 2 = 0

-- we can find a proof that `Pev 24` is true:

example : Pev 24 := by
  unfold Pev
  rfl -- Lean computes that `Nat.mod 24` is 2, so that `Nat.mod 24 = 2` is replaced by `2 = 2` 
      -- which is then proved using the "reflexive property of equality"

-- but there is no proof that `Pev 3` is true. In fact, we can prove `¬ Pev 3`.

example : ¬ Pev 3 := by
  unfold Pev
  apply Nat.succ_ne_self

#eval Nat.mod 3 2

/- Given a type `α`, a predicate on `α` is just a term `p : α → Prop`.
   Thus given a term `a : α`, `p a` is the proposition that `p` holds at `a`.
   Of course, `p a` may or may not be true.
-/

/- we can quantify predicates.

   Universal quantifier: ∀
     thus `∀ x:α, p x` is the statement that the proposition `p x` is true for all x.

   existential quantifier: ∃
     thus `∃ x:α, p x` is the statement that there is some term `x:α` such that
     `p x` is true.

-/

example (P : Nat → Prop) : (∀ n, P n) → P 3 := by
  intro hP
  exact hP 3

example (P : Int → Prop) : (forall n, P (2*n + 1)) → ∃ n, P n := by
  intro hP
  apply Exists.intro 1  -- or: use 1
  exact hP 0

example (α : Type) (P : α → Prop) : (∃ a, ¬ P a) → ¬ ∀ a, P a := by
  intro he hu
  match he with
  | ⟨ a, ha ⟩ => exact ha (hu a)

