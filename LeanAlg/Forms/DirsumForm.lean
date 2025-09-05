import Mathlib

variable {R V V₁ V₂ : Type} [Field R]
         [AddCommGroup V] [AddCommGroup V₁] [AddCommGroup V₂]
         [Module R V] [Module R V₁] [Module R V₂]


open LinearMap
open LinearMap (BilinForm)

--------------------------------------------------------------------------------
section DirSumBilinForm

open DirectSum
open BigOperators

variable {ι : Type} [DecidableEq ι]

variable {R : Type} [CommRing R]
variable {W : ι → Type}
         [(i : ι) → AddCommGroup (W i)]
         [(i : ι) → Module R (W i)]

open DirectSum

set_option linter.unusedSectionVars false in
@[simp]
def DirectSum.pairing (φ : (i : ι) → BilinForm R (W i)) (j : ι) : 
    W j →ₗ[R] (⨁ i, W i) →ₗ[R] R :=
  LinearMap.compl₁₂
    (φ j)                        -- (W j) →ₗ[R] (W j) →ₗ[R] R
    id                           -- (W j) →ₗ[R] (W j)
    (component R ι W j)          -- (⨁ i, W i) →ₗ[R] W j 

set_option linter.unusedSectionVars false in
lemma pairing_apply (φ : (i : ι) → BilinForm R (W i)) (j : ι) (w : W j)
    (x : ⨁ i, W i) :
    pairing φ j w x =  (φ j) w ((component R ι W j) x) :=  by 
  simp_all only [pairing, compl₁₂_apply, id_coe, id_eq]


lemma pairing_single (φ : (i : ι) → BilinForm R (W i)) (i j : ι) (w : W j)
    (x : W i) : pairing φ j w (lof R ι W i x) = 
    if h : i = j then  (φ j) w (Eq.recOn h x) else 0 := by 
  by_cases hh : i  = j 
  case pos => 
    have (x : W j) : ((pairing φ j) w) (lof R ι W i) = ((pairing φ j) w) (lof R ι W j) := by
      rw [hh]
    rw [ pairing_apply φ ]
    rw [ component.lof_self R i x]
    simp
    sorry
  case neg => sorry


@[simp]
def DirectSum.BilinForm (φ : (i : ι) → BilinForm R (W i)) :
    BilinForm R (⨁ i, W i) :=
  DirectSum.toModule R ι ((⨁ i, W i) →ₗ[R] R) (pairing φ)


theorem dirsum_bilin_form_apply_single (φ : (i : ι) → BilinForm R (W i))
    (s : Finset ι) (i j : ↑s) (v : W i) (w : W j) :
    DirectSum.BilinForm φ (DirectSum.lof R ι W i v)
                (DirectSum.lof R ι W j w)
    = if h : i = j  then (φ i) v (Eq.recOn h.symm w) else 0 := by
  by_cases hh : ↑i = ↑j
  case pos =>
    subst hh
    simp_all only [DirectSum.BilinForm, DirectSum.pairing, toModule_lof, 
      compl₁₂_apply, id_coe, id_eq,
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


theorem dirsum_bilin_form_apply_lof_right [(i : ι) → (x : W i) → Decidable (x ≠ 0)]
    (φ : (i : ι) → BilinForm R (W i)) (v : ⨁ i, W i) (j : ι) (wj : W j) :
    DirSumBilinForm φ v (lof R ι W j wj) = (φ j) (v j) wj := by
  
  
  --simp_all only [DirSumBilinForm, toModule, LinearMap.id, component, DFinsupp.lapply ]
  
  sorry

theorem dirsum_bilin_form_apply_lof_left [(i : ι) → (x : W i) → Decidable (x ≠ 0)]
    (φ : (i : ι) → BilinForm R (W i)) (w : ⨁ i, W i) (j : ι) (vj : W j) :
    DirSumBilinForm φ (lof R ι W j vj) w = (φ j) vj (w j)  := by
  simp_all only [DirSumBilinForm]
  sorry          

theorem dirsum_bilin_form_apply_support_left [(i : ι) → (x : W i) → Decidable (x ≠ 0)]
    (φ : (i : ι) → BilinForm R (W i))
    (v w : ⨁ i, W i):
  DirSumBilinForm φ v w =
  ∑ i ∈ (DFinsupp.support v),
  (φ i) (DirectSum.component R ι W i v) (DirectSum.component R ι W i w) := by sorry


theorem dirsum_bilin_form_apply_support_left [(i : ι) → (x : W i) → Decidable (x ≠ 0)]
    (φ : (i : ι) → BilinForm R (W i))
    (v w : ⨁ i, W i):
  DirSumBilinForm φ v w =
  ∑ i ∈ (DFinsupp.support v),
  (φ i) (DirectSum.component R ι W i v) (DirectSum.component R ι W i w) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of j x =>
      rw [ ← DirectSum.lof_eq_of R ι W j ]
      rw [ Finset.sum_eq_single j ]
      · rw [ DirectSum.component.of R _ j]
        simp
      · intro i hi hij
        rw [DirectSum.component.of R i j ]
        simp_all only [Finset.inf_eq_inter, Finset.mem_inter, DFinsupp.mem_support_toFun, ne_eq]
        obtain ⟨left, right⟩ := hi
        split
        next h => exfalso; exact hij h.symm
        next h => simp_all only [map_zero, LinearMap.zero_apply]
        
      · intro hj
        rw [ DirectSum.component.of R j j]
        split
        next h =>
          contrapose hj
          push_neg
          suffices : j ∈ DFinsupp.support w by
            sorry

        next h => exfalso; exact h rfl
        sorry
  | add => sorry



