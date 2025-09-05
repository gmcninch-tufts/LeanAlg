import Mathlib.Tactic

variable {G : Type} [Group G]

def leftCoset {G : Type} [Group G] (H : Subgroup G) (x:G): Set G := 
  { y:G | ∃ h ∈ H , y = x*h }    

lemma contain {H : Subgroup G} {x y : G} :
  leftCoset H x = leftCoset H y → x ∈ leftCoset H y := by 
    intro h
    have hx : x ∈ leftCoset H x := by
      use 1
      constructor
      · exact Subgroup.one_mem _
      · group
    rw [h] at hx
    assumption


example (A : Prop) : A → A ∧ A := by
  intro h
  constructor
  · exact h
  · exact h
