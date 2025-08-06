import Mathlib.Tactic

variable {G : Type} [AddCommGroup G]
variable {H : AddSubgroup G}

example : G → Prop := fun g => g ∈ H

example (x y : G) ( _ : x ∈ H) ( _ : y ∈ H) : Prop := x + y ∈ H


example (x y : G) : G := y - x

def cong {G : Type} [AddCommGroup G] ( H : AddSubgroup G ) : G → G → Prop := 
  fun x y => y - x ∈ H

lemma cong_symm {G : Type} [AddCommGroup G] { x y : G } { H : AddSubgroup G} : cong H x y → cong H y x := 
   fun h => (AddSubgroup.sub_mem_comm_iff H).mp h

lemma cong_trans { x y z : G} {H:AddSubgroup G} : cong H x y → cong H y z → cong H x z := by
  intro h k
  unfold  cong
  have : z - x = (z - y) + (y - x ) := by simp
  rw [ this ] 
  exact H.add_mem k h  



