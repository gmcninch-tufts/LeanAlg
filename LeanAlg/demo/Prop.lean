--import Mathlib.Tactic
import Mathlib.Order.Defs.Unbundled


/- let's declare some variables to represent logical propositions -/
variable (P Q R : Prop)

/- From our point-of-view, a proposition represents a mathematical
statement, which may or may not have a proof.

From a computer-language point of view, `P` and `Q` and `R` are *types*.
And a *term* `p` of type `P` -- indicated with the syntax `p:P` --
should represent a *proof* of the proposition `P`.
-/

/- Logical And and Or -/

example (p:P) (q:Q) : P ∧ Q := ⟨ p,q ⟩

example (p:P) : P ∨ Q := Or.inl p

example (q:Q) : P ∨ Q := Or.inr q


/- We know that the logical statement `P is true` toegether with
`P implies Q` should imply that `Q is true`.

This is a logical assertion which goes by the name *modus ponens*.

Let's check this in Lean. -/

theorem modus_ponens : P ∧ (P -> Q) -> Q := by
  sorry

/- It may seem strange, but we view the type `P` as representing
`all proofs of P`.

So a function `P -> Q` is then a function from `proofs of P`
to `proofs of Q`.

From this point of view, for `P Q : Prop` the function type `P -> Q`
is the same thing as logical implication.
-/

/- Logical negation

How to define the proposition `not P`??

Need the type `False`.

`False` is a type with no terms.
-/

#check False

/- anything follows from `False`! -/

example : ∀ P:Prop, False -> P := by
  intro P
  apply False.rec

/- To prove the negation of the proposition `P` -- i.e. to prove that
`P` is not true -- amounts to proving  that `P implies False`
i.e. to exhibiting a term of type `P -> False`.

The syntax `¬ P` is shorthand for `P -> False`. -/

example (hnp : ¬ P) : ¬ (P ∧ Q) := by
  sorry

example (hnp : ¬ P) (hnq : ¬ Q) : ¬ (P ∨ Q) := by
  sorry


theorem contraposition : (P -> Q) <-> (¬ Q -> ¬ P) := by
  constructor
  · intro hpq
    intro nq
    intro p
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

/- Given a type `α`, a predicate on `α` is just a term `p : α -> Prop`.
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

example (P : Nat -> Prop) : (∀ n, P n) -> P 3 := by
  intro hP
  exact hP 3

example (P : Int -> Prop) : (forall n, P (2*n + 1)) -> ∃ n, P n := by
  intro hP
  apply Exists.intro 1  -- or: use 1
  exact hP 0

example (α : Type) (P : alpha -> Prop) : (∃ a, ¬ P a) -> ¬ ∀ a, P a := by
  intro he hu
  match he with
  | ⟨ a, ha ⟩ => exact ha (hu a)

@[simp]
def myrel {α : Type} : (α × α) →  (α × α) ->  Prop
  | (a,b), (c,d) => (a,b) = (c,d) ∨ (a,b) = (d,c)

instance (α:Type): IsEquiv (α × α) myrel where
  refl := by
    intro (a,b)
    apply Or.inl
    rfl
  symm := by
    intro ⟨a,b⟩ ⟨c,d⟩
    unfold myrel
    intro h
    apply Or.elim h
