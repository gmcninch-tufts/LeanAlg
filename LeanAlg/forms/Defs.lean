import Mathlib
--import Mathlib.LinearAlgebra.BilinearForm.Properties

variable {k V W : Type} [Field k]
  [AddCommGroup V] [AddCommGroup W]
  [Module k V] [Module k W]

open Module          
open LinearMap
open LinearMap (BilinForm)


def DualPairing (k V : Type) [Field k] [AddCommGroup V] [Module k V] :   
  V →ₗ[k] (V →ₗ[k] k) →ₗ[k] k := LinearMap.applyₗ

  
/-- The ε-hyperbolic bilinear form `β` on the space `V × (V →ₗ[k] k)`
given by the rule
`β (v,φ) (v',φ') = (φ' v) + ε * (φ v')`
-/
@[simp]
def HyperbolicForm (k V : Type) [Field k] [AddCommGroup V] [Module k V] (ε : k)
  : BilinForm k (V × (V →ₗ[k] k)) := 
  let β₁ : BilinForm k (V × (V →ₗ[k] k)) :=
  -- β₁ is the mapping `(v,φ) (v',φ') => φ' v`
      LinearMap.compl₁₂  
        LinearMap.applyₗ
        (LinearMap.fst k V _) 
        (LinearMap.snd  k _ (V →ₗ[k] k))
  let β₂ : BilinForm k (V × (V →ₗ[k] k)) :=
  -- β₂ is the mapping `(v,φ) (v',φ') => φ v'`  
      LinearMap.compl₁₂  
        (LinearMap.flip LinearMap.applyₗ)
        (LinearMap.snd k  _ (V →ₗ[k] k)) 
        (LinearMap.fst  k V _)

  β₁ + ε•β₂
  
theorem hyperbolic_form_apply (v v' : V) (φ φ' : V →ₗ[k] k) (ε : k) :
  (HyperbolicForm k V ε) ⟨v,φ⟩ ⟨v',φ'⟩ = (φ' v) + ε*(φ v') := by 
  simp

/-- The `HyperbolicForm` on `V × (V →ₗ[k] k)` is symmetric when `ε = 1`.
-/
theorem hyperbolic_is_symm_of_1 (k V : Type) [Field k] [AddCommGroup V] [Module k V] :
  (HyperbolicForm k V 1).IsSymm := by
  rw [ BilinForm.isSymm_def ]
  intro ⟨v,φ⟩ ⟨v₁,φ₁⟩
  simp_all 
  ring

/-- The `HyperbolicForm` on `V × (V →ₗ[k] k)` is alternating when `ε = -1`.
-/
theorem hyperbolic_is_alt_of_minus1 (k V : Type) [Field k] [AddCommGroup V] [Module k V] :
  (HyperbolicForm k V (-1:k)).IsAlt := by
  intro ⟨v,φ⟩ 
  simp


lemma exists_functional_nezero (k V : Type) [Field k] [AddCommGroup V] [Module k V]
    (v : V) (hv : v ≠ 0) :
    ∃ ψ:V →ₗ[k] k, ψ v ≠ 0 := by
  contrapose hv
  push_neg at *
  have l : v = 0 := (Module.forall_dual_apply_eq_zero_iff k v).mp hv
  assumption
 
/-- Suppose `ε ≠ 0`. Given a non-zero vector `x` in `V × (V →ₗ[k] k)`, there
is a vector `y` in `V × (V →ₗ[k] k)` for which 
`HyperbolicForm k V ε x y ≠ 0`
-/
lemma non_zero_pair (x : V × (V →ₗ[k] k)) (ε : k) (hε : ε ≠ 0) (h : x ≠ 0) :
    ∃ y, (HyperbolicForm k V ε) x y ≠ 0 := by 
  rcases x with ⟨v,φ⟩
  by_cases hv : v = 0
  case pos => 
    have : φ ≠ 0 := by aesop
    obtain ⟨w,hw⟩ : ∃w, φ w ≠ 0 := by
      contrapose this
      push_neg at *
      ext v
      apply this    
    use ⟨w,0⟩
    simp
    exact ⟨hε,hw⟩     
  case neg =>
    rcases (exists_functional_nezero k V v hv) with ⟨ψ,hψ⟩
    use ⟨0,ψ⟩
    simp; assumption
          
/-- The `DualPairing` `V × (V →ₗ[k] k) → k` is nondegenerate.
-/
theorem dual_pairing_nondeg (k V : Type) [Field k] [AddCommGroup V]
  [Module k V] : (DualPairing k V).Nondegenerate := by 
  constructor
  case left => 
    intro v hv
    contrapose hv
    push_neg
    rcases (exists_functional_nezero k V v hv) with ⟨ψ,hψ⟩ 
    use ψ
    exact hψ
  case right => 
    intro φ hφ
    ext v
    apply hφ v
          
/-- If `ε ≠ 0`, the `HyperbolicForm k V ε` on `(V × (V →ₗ[k] k))` is non-degenerate.
-/
theorem hyperbolic_nondeg (k V : Type) [Field k] [AddCommGroup V]
  [Module k V] (ε : k) (hε : ε ≠ 0) :
  (HyperbolicForm k V ε).Nondegenerate := by
  intro ⟨v,φ⟩ h
  by_contra l
  have : ∃y, (HyperbolicForm k V ε) ⟨v,φ⟩ y ≠ 0 := non_zero_pair ⟨v,φ⟩ ε hε l
  rcases this with ⟨y,hy⟩
  exact hy (h y)


/-- A hyperbolic basis of a vector space `V` with a bilinear form `β` is a basis `b`
indexed by a type `ι ⊕ ι` with the properties 
- `β (b (Sum.inl i)) (b (Sum.inl j)) = 0` for every `i j`
- `β (b (Sum.inr i)) (b (Sum.inr j)) = 0` for every `i j`
- `β (b (Sum.inl i)) (b (Sum.inr j)) = δ_{i,j}` for every `i j`
- `β (b (Sum.inl i)) (b (Sum.inr j)) = ε * δ_{i,j}` for every `i j`
-/
structure HyperbolicBasis (k W : Type) [Field k] [AddCommGroup W] [Module k W]
  (ε : k) (β : BilinForm k W) (ι : Type) [DecidableEq ι] where
  carrier : Basis (ι ⊕ ι) k W
  cond_ll : ∀ i j, β (carrier (Sum.inl i)) (carrier (Sum.inl j)) = 0
  cond_rr : ∀ i j, β (carrier (Sum.inr i)) (carrier (Sum.inr j)) = 0
  cond_lr : ∀ i j, β (carrier (Sum.inl i)) (carrier (Sum.inr j)) = if i=j then 1 else 0
  cond_rl : ∀ i j, β (carrier (Sum.inr i)) (carrier (Sum.inl j)) = if j=i then ε else 0


/-- Construction of a hyperbolic basis for `V × (V →ₗ[k] k)` equipped
with `HyperbolicForm k V ε`.
-/
noncomputable
def HyperbolicBasisOfHyperbolicForm (ε : k)
   (ι : Type) [Finite ι] [DecidableEq ι] (b : Basis ι k V) :
  HyperbolicBasis k (V × (V →ₗ[k] k)) ε (HyperbolicForm k V ε) ι where
    carrier := Basis.prod b (Basis.dualBasis b)
    cond_ll := by simp
    cond_rr := by simp
    cond_lr := by aesop
    cond_rl := by aesop

