import Mathlib.Tactic

variable { k : Type } 
variable [Field k]
variable { V W : Type } 
variable [AddCommGroup V] [AddCommGroup W]
variable [Module k V] [Module k W]
variable [BEq V] [BEq W]


def r (k:Type) [Field k] ( V:Type) [AddCommGroup V] [Module k V]: V → V → Prop := 
  fun v w => ∃ α:k, α ≠ 0 ∧ v = α • w

def r_is_equiv  : Equivalence (r k V)  where
  refl x := by 
    use 1
    apply And.intro
    · norm_num
    · simp

  symm := fun h => by
    unfold r at h
    rcases h with ⟨t,htnz,htmul⟩
    use t⁻¹
    apply And.intro
    · exact inv_ne_zero htnz
    · exact (eq_inv_smul_iff₀ htnz).mpr (id (Eq.symm htmul)) 

  trans := fun h k => by
    unfold r
    unfold r at h
    unfold r at k
    rcases h with ⟨t,htnz,htmul⟩
    rcases k with ⟨s,hsnz,hsmul⟩
    use t*s
    apply And.intro
    · exact (mul_ne_zero_iff_right hsnz).mpr htnz 
    · rw [mul_smul t s, htmul, hsmul ]


structure ProjSpace  where
  carrier : Quotient V r

#check Setoid

def PP : Type := ProjSpace k V

structure Point {k:Type} [Field k]  where
  x : k
  y : k
  xnez : x ≠ 0

#eval Point.mk (0:ℚ) 0 _


def dual  ( k V: Type) [Field k] [AddCommGroup V] [Module k V] : Type := 
  V →ₗ[k] k

variable (φ : dual k V)

variable (v:V)

example : Type := Submodule.span k { v }

#check Submodule.span k { v }


instance : AddCommGroup (dual k V) := by
  simp [dual]
  exact inferInstance

instance : Module k (dual k V) := by
  simp [dual]
  exact inferInstance


example : Type := Submodule.span k { φ }


example (X:Type) [BEq X] (ls : List X) (x:X) : Prop  := 
   (List.elem x ls) = true

def  A : Type := ℤ

#check A

example : A = ℤ := by
  unfold A
  rfl

def α : AddCommGroup A := by
  simp [A]
  exact inferInstance 

def b : AddCommGroup ℤ := inferInstance 

example (a b : A) : A := a.add b 

#check α.add

