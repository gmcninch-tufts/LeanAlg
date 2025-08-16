import Mathlib

variable {k V V₁ V₂ : Type} [Field k]
         [AddCommGroup V] [AddCommGroup V₁] [AddCommGroup V₂]
         [Module k V] [Module k V₁] [Module k V₂]


open LinearMap
open LinearMap (BilinForm)



--------------------------------------------------------------------------------
section DirSumBilinForm

open DirectSum
open BigOperators

variable {ι : Type} [DecidableEq ι]

variable {W : ι → Type}
         [(i : ι) → AddCommGroup (W i)]
         [(i : ι) → Module k (W i)]


@[simp]
def DirSumBilinForm (φ : (i : ι) → BilinForm k (W i)) :
  BilinForm k (⨁ i, W i) := 
  let γ (j : ι) : W j →ₗ[k] (⨁ i, W i) →ₗ[k] k :=
    LinearMap.compl₁₂ 
      (φ j)
      id
      (component k ι W j)
  DirectSum.toModule k ι ((⨁ i, W i) →ₗ[k] k) γ

example (s : Finset ι) (v : (i : s) → W i) : (⨁ i, W i) := DirectSum.mk W s v
  
theorem dirsum_bilin_form_apply_single (φ : (i : ι) → BilinForm k (W i))
    (s : Finset ι) (i j : ↑s) (v : W i) (w : W j) :
  DirSumBilinForm φ (DirectSum.lof k ι W i v)
                    (DirectSum.lof k ι W j w)
  = if h : i = j  then (φ i) v (Eq.recOn h.symm w) else 0 := by   
    by_cases hh : ↑i = ↑j
    case pos => 
      subst hh
      simp_all only [DirSumBilinForm, toModule_lof, compl₁₂_apply, id_coe, id_eq, 
        component.lof_self, ↓reduceDIte]
    case neg => 
      simp [ DirectSum.component.of ]
      simp_all only [ ↓reduceDIte ]
      obtain ⟨vi, hi⟩ := i
      obtain ⟨vj, hj⟩ := j
      simp_all only [Subtype.mk.injEq]
      split
      case mk.mk.isTrue => 
        next h =>
        subst h
        simp_all only [not_true_eq_false]
      case mk.mk.isFalse =>
        next h => simp_all only [map_zero]
    
theorem dirsum_bilin_form_apply [(i : ι) → (x : W i) → Decidable (x ≠ 0)]
    (φ : (i : ι) → BilinForm k (W i))
    (v w : ⨁ i, W i) :
  DirSumBilinForm φ v w = 
  ∑ i ∈ (DFinsupp.support v) ⊓ (DFinsupp.support w), 
  (φ i) (DirectSum.component k ι W i v) (DirectSum.component k ι W i w) := by 
  induction v using DirectSum.induction_on with
  | zero => simp 
  | of i x => 
      --rw [ DirectSum.support_of  ]
      -- simp only [ Finset.inf_eq_inter ]     
      -- have : {i} ∩ DFinsupp.support w ⊆ {i} := fun j => by simp_all
      rw [ Finset.sum_eq_single i ]
      case of.h₁ => simp
    
      sorry
  | add => sorry

  

