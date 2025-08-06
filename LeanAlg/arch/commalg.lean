import Mathlib.Tactic
import Init
import Mathlib.Algebra.GroupWithZero.Defs
  
variable {α : Type} [CommRing α] [IsDomain α] [IsPrincipalIdealRing α]

#check mul_left_cancel₀

#check α

variable ( a b c d : α )



def divides (a b : α) : Prop := ∃ (x : α), b = a*x 

theorem divides_reflexive (a:α) : divides a a := by
  use 1
  simp

theorem divides_reflexive_pt (a:α) : divides a a :=
  Exists.intro 1 (by ring)

theorem divides_transitive  (a b c : α) : (hab : divides a b) 
        → (hbc : divides b c) 
        → divides a c := by 
  intro hab hbc
  rcases hab  with ⟨x,hx⟩ 
  rcases hbc with ⟨y,hy⟩
  use x * y
  rw [← mul_assoc a x y]
  rw [←hx,←hy]
  

theorem divides_sum2 (a b c : α) (hb : divides a b) (hc : divides a c): divides a (b+c) := by
  rcases hb with ⟨x,hx⟩
  rcases hc with ⟨y,hy⟩
  use x + y
  simp [left_distrib]
  rw [ hx,hy]


def sum_list : List α → α := 
  fun ll =>
    match ll with
    | [] => 0
    | List.cons a as => a + (sum_list as)



structure divides_dat (a b : α) where
  q : α
  hq : b= a * q

def sum_dd { a b c : α} (hab:divides_dat a b) (hac:divides_dat a c) : divides_dat a (b+c) := by
  have pf : b + c = a * (hab.q + hac.q) := by 
    simp only [hab.hq,hac.hq]
    ring
  exact divides_dat.mk (hab.q + hac.q) pf                              


variable (ty:α → Type)
variable (pr:α → Prop)

#check (a:α) × ty a
#check (a:α) × pr a

def divides_sum (a:α) (ll:List ((b:α) × divides_dat a b)) : (c:α) × divides_dat a c := by
  match ll with
  | [] => exact ⟨ 0, divides_dat.mk 0 (by ring) ⟩
  | List.cons ⟨val,dv⟩ bs => 
      have ⟨ prev, pprev ⟩ := divides_sum a bs 
      exact ⟨ val + prev , sum_dd dv pprev ⟩

  
  
  

-- theorem divides_sum (a:α) { S : Type } (f : S →₀ α) 
--                     (hf : (x:S) → divides a (f x)) : divides a (∑ x ∈ (f.support), f x) := by 
--   have g : ( gg:S →₀ α) * ((y:S) → a * gg y = f y) := 
--     fun x => by sorry
--  --     rcases (hf x) ⟨ y, hy ⟩
      
