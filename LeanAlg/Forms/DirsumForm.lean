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

variable {R : Type} [Commking R]
variable {W : ι → Type}
         [(i : ι) → AddCommGroup (W i)]
         [(i : ι) → Module R (W i)]
--         [(i : ι) → DecidableEq (W i)]

@[simp]
def DirSumBilinForm (φ : (i : ι) → BilinForm R (W i)) :
  BilinForm R (⨁ i, W i) :=
  let γ (j : ι) : W j →ₗ[R] (⨁ i, W i) →ₗ[R] R :=
    LinearMap.compl₁₂
      (φ j)
      id
      (component R ι W j)
  DirectSum.toModule R ι ((⨁ i, W i) →ₗ[R] R) γ

theorem DirSumBilinForm.finsupp_left (φ : (i : ι) → BilinForm R (W i))
  (v : ⨁ i, W i) : Finsupp

example (s : Finset ι) (v : (i : s) → W i) : (⨁ i, W i) := DirectSum.mk W s v

theorem dirsum_bilin_form_apply_single (φ : (i : ι) → BilinForm R (W i))
    (s : Finset ι) (i j : ↑s) (v : W i) (w : W j) :
  DirSumBilinForm φ (DirectSum.lof R ι W i v)
                    (DirectSum.lof R ι W j w)
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
    (v w : ⨁ i, W i):
  DirSumBilinForm φ v w =
  ∑ i ∈ (DFinsupp.support v) ⊓ (DFinsupp.support w),
  (φ i) (DirectSum.component k ι W i v) (DirectSum.component k ι W i w) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of j x =>
      rw [ ← DirectSum.lof_eq_of k ι W j ]
      rw [ Finset.sum_eq_single j ]
      · rw [ DirectSum.component.of k _ j]
        simp
      · intro i hi hij
        rw [DirectSum.component.of k i j ]
        simp_all only [Finset.inf_eq_inter, Finset.mem_inter, DFinsupp.mem_support_toFun, ne_eq]
        obtain ⟨left, right⟩ := hi
        split
        next h => exfalso; exact hij h.symm
        next h => simp_all only [map_zero, LinearMap.zero_apply]
      · intro hj
        rw [ DirectSum.component.of k j j]
        split
        next h =>
          contrapose hj
          push_neg
          suffices : j ∈ DFinsupp.support w by
            sorry

        next h => exfalso; exact h rfl
  | add => sorry


example (X : Type) (S T : Set X) (x : X) (h : x ∉ S ∩ T) : x ∉ S ∨ x ∉ T := by
  contrapose h
  push_neg at *
  assumption
