
import Mathlib.Tactic

variable {G : Type} [Group G]

def leftCoset {G : Type} [Group G] (H : Subgroup G) (x:G): Set G := 
  { y:G | ∃ h ∈ H , y = x*h }

lemma eq_symm { H : Subgroup G} {x y : G} : y⁻¹ * x ∈ H ↔ x⁻¹ * y ∈ H := by
   --constructor
  apply Iff.intro
  case mp => 
    intro h
    have hh : (y⁻¹ * x)⁻¹ = x⁻¹ * y := by
      group
    have ho : (y⁻¹*x)⁻¹ ∈ H := by
      apply Subgroup.inv_mem H
      assumption
    rw [ ← hh] 
    assumption
  case mpr =>
    intro h
    have hh : (x⁻¹ * y)⁻¹ = y⁻¹ * x := by
      group
    have ho : (x⁻¹*y)⁻¹ ∈ H := by
      apply Subgroup.inv_mem H
      assumption
    rw [ ←hh] 
    assumption
    

lemma contain {H : Subgroup G} {x y : G} : leftCoset H x = leftCoset H y → x ∈ leftCoset H y := by 
  intro h
  have hx : x ∈ leftCoset H x := by
    use 1
    constructor
    · exact Subgroup.one_mem _
    · group
  rw [h] at hx
  assumption

lemma elem_coset {H : Subgroup G} {x y : G} : x ∈ leftCoset H y ↔ y⁻¹ * x ∈ H := by
  constructor
  · intro h
    have hz : ∃ z ∈ H, x = y * z := by
        apply h
    rcases hz with ⟨z,helem,heq⟩
    have hf : z = y⁻¹*x := by
       rw [ heq]
       group
    rw [hf] at helem 
    exact helem     
  · intro h
    use y⁻¹ * x
    constructor
    · apply h
    · group
      

lemma equiv_contain (H : Subgroup G) (x y: G) : y⁻¹ * x ∈ H → leftCoset H x ⊆ leftCoset H y :=  by 
  intro h1 
  intro z hz
  have hxz : x⁻¹ * z ∈ H := by 
    apply elem_coset.mp
    assumption
  have heyz : y⁻¹ * z = (y⁻¹ * x) * (x⁻¹ * z) := by
    group
  have hyz : y⁻¹ * z ∈ H := by
     rw [heyz]
     apply Subgroup.mul_mem
     repeat assumption
  apply elem_coset.mpr 
  assumption

theorem cosetEq (H : Subgroup G) (x y : G) :
  (leftCoset H x = leftCoset H y) ↔ (y⁻¹ * x) ∈ H := by    
  constructor
  · rintro h 
    have hx : x ∈ leftCoset H y := by 
      apply contain
      exact h
    apply elem_coset.mp
    assumption
  · rintro hh
    ext z
    constructor 
    · apply equiv_contain H 
      assumption
    · apply equiv_contain H
      rw [eq_symm]
      assumption
      

         
        

theorem cosetDisjoint (H:Subgroup G) (x y: G) :
  leftCoset H x ∩ leftCoset H y = ∅ ↔ ¬ (x⁻¹ * y ∈ H.carrier) := by sorry
