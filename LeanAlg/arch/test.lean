import Mathlib.Tactic

variable (a b : ℝ)

variable (p q r : Prop)

example : (p → (q → r)) ↔ (p ∧ q → r) :=  by
  apply Iff.intro 

  case  mp =>
    intro h
    rintro ⟨hp, hq⟩
    exact h hp hq

  case mpr =>
    intro g
    rintro hp hq
    exact g $ And.intro hp hq
  


 

example : min a b = min b a := by
  have lem : { x y : ℝ } -> min x y ≤ min y x := by
    intro x y 
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm 
  repeat
    apply lem 


variable ( x y z w : ℤ)

example : x ∣ y * x * z := by
  use y*z
  ring

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · use y*z
      ring
    · use x
      ring
  · rw [ pow_two ]
    rcases h with ⟨z,zh⟩
    rw [zh]
    use x*z^2
    ring

--    exact Dvd.dvd.mul_right h _
--h w
    


example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption

theorem thm₁ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _
