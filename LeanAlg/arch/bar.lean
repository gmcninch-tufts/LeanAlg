import Mathlib.Tactic

inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday

--#check Weekday.casesOn

namespace Other

#check Weekday.casesOn

def f (d : String) : ℤ :=
  match d with
  | "foo" => 1
  | "bar" => 2
  | _ => 3


def g : ℤ → ℤ → ℤ := 
  fun x y => x + y

#eval f ""

#check g 

end Other

--------------------------------------------------------------------------------
namespace George

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  · apply hgb

#eval (fun (x:ℝ) ↦ x^20) (3)

#check fun x => x^2

end George
--------------------------------------------------------------------------------

open Pi
theorem foo {I : Type u} {α : Type u_1} {β : Type u_2} [Monoid α] [AddMonoid β] 
     [DistribMulAction α β] [DecidableEq I] (i : I) (r : α) (x : β) :
   single i (r • x) = r • single i x := by sorry
