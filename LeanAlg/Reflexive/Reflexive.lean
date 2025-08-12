import Mathlib

open LinearMap.BilinForm
open LinearMap (BilinForm)


variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

#check isSymm_def 

lemma proptwopointsix {β : BilinForm k V}
    (h : ∀ (u v w : V), (β u) v * (β w) u = (β v) u * (β u) w) : 
    β.IsAlt ∨ β.IsSymm := by
  have h₁ (v w: V): (β v) v * ((β w) v - (β v) w) = 0 := by
    rw[mul_sub_left_distrib]
    refine sub_eq_zero_of_eq ?_
    rw [h]
  have id₁ (v w : V) : (β v v)*(β w v) = (β v v)*(β v w)  :=  h v v w
  by_contra j
  push_neg at j
  unfold BilinForm.IsAlt LinearMap.IsAlt  at j
  rw [isSymm_def] at j
  simp at j
  rcases j with ⟨⟨e, lj⟩, ⟨f, g, rj⟩⟩
  have h₂ : (β g) g = 0 := by
    have i₂ : β g g * (β f g - β g f) = 0 := by
      exact h₁ g f
    rw[mul_sub_left_distrib] at i₂
    apply eq_of_sub_eq_zero at i₂
    rw[mul_eq_mul_left_iff] at i₂
    aesop
  have h₃ : (β f) f = 0 := by
    have i₃ : β f f * (β g f - β f g) = 0 := by
      exact h₁ f g
    rw[mul_sub_left_distrib] at i₃
    apply eq_of_sub_eq_zero at i₃
    rw[mul_eq_mul_left_iff] at i₃
    aesop
  have h₄ : (β f) e = (β e) f := by
    have i₄ : β e e * (β f e - β e f) = 0 := by
      exact h₁ e f
    rw[mul_sub_left_distrib] at i₄
    apply eq_of_sub_eq_zero at i₄
    rw[mul_eq_mul_left_iff] at i₄
    aesop
  have h₅ : (β g) e = (β e) g := by
    have i₅ : β e e * (β g e - β e g) = 0 := by
      exact h₁ e g
    rw[mul_sub_left_distrib] at i₅
    apply eq_of_sub_eq_zero at i₅
    rw[mul_eq_mul_left_iff] at i₅
    aesop
  have h₆ : (β e) f = 0 := by
    have i₆ : ((β f) e) * ((β g) f) = ((β e) f) * ((β f) g) := by
      exact h f e g
    rw[← h₄] at i₆
    rw[mul_eq_mul_left_iff] at i₆
    aesop
  have h₇ : (β e) g = 0 := by
    have i₇ : ((β g) e) * ((β f) g) = ((β e) g) * ((β g) f) := by
      exact h g e f
    rw[← h₅] at i₇
    rw[mul_eq_mul_left_iff] at i₇
    aesop
  have h₈ : (β f) (e + g) = (β f) g := by
    aesop
  have h₉ : (β (e + g)) f = (β g) f := by
    aesop
  have h₁₀ : (β (e + g)) (e + g) = 0 := by
    have i₁₀ : (β (e + g)) (e + g) * ((β f (e + g)) - (β (e + g) f)) = 0 := by
      exact h₁ (e + g) f
    rw[h₈, h₉, mul_sub_left_distrib] at i₁₀
    apply eq_of_sub_eq_zero at i₁₀
    rw[mul_eq_mul_left_iff] at i₁₀
    aesop
  have h₁₁ : (β (e + g)) (e + g) = (β e) e := by
    simp
    rw[h₇]
    rw[← h₅] at h₇
    rw[h₇, h₂]
    simp
  rw[h₁₀] at h₁₁
  exact lj (_root_.id (Eq.symm h₁₁))


theorem refl_is_alt_or_symm {β: BilinForm k V} (h: β.IsRefl):
    β.IsAlt  ∨ β.IsSymm := by
    let x (u v w : V) := ((β u) v) • w - (((β u) w) •  v)
    have h₀ (u v w : V):  (β u) (x u v w) = (((β u) v) * ((β u) w)) - (((β u) w) * ((β u) v)) := by
      aesop
    have h₁ (u v w : V) : (((β u) v) * ((β u) w)) - (((β u) w) * ((β u) v)) = 0 := by
      rw[mul_comm]
      simp
    simp_rw[h₁] at h₀
    have h₂ (u v w: V) :(β (x u v w)) u =  0:= by
      exact h u (x u v w) (h (x u v w) u (h u (x u v w) (h₀ u v w)))
    have h₃ (u v w : V): β (x u v w) u = β u v * β w u - (β v u) * (β u w) := by
      have h₃₀ (u v w: V): (β (x u v w)) u = (β (((β u v) • w) - (β u w) • v)) u := by
        aesop
      simp at h₃₀
      simp_rw[h₃₀]
      rw[mul_comm (β u w)  (β v u)]
    have h₄ : ∀ (u v w : V), (((β u) v) * ((β w) u)) = (((β v) u) * ((β u) w)) := by
      intro u v w
      have h₄₀ : (β u) v * (β w) u = (β v) u * (β u) w ↔ (((β u) v) * ((β w) u)) - (((β v) u) * ((β u) w)) = 0 := by
        constructor
        · aesop
        · intro g
          apply eq_of_sub_eq_zero at g
          exact g
      rw[h₄₀]
      apply eq_of_sub_eq_zero
      simp
      simp_rw[h₂] at h₃
      exact (AddSemiconjBy.eq_zero_iff 0 (congrFun (congrArg HAdd.hAdd (h₃ u v w)) 0)).mp rfl
    apply proptwopointsix (k := k) (V := V)
    · exact h₄

theorem refl_iff_alt_or_symm {β : BilinForm k V} : β.IsRefl ↔ (β.IsAlt ∨ β.IsSymm) := by
  constructor
  · intro h
    exact refl_is_alt_or_symm h
  · intro h
    cases h with
    | inl h₁ => exact IsAlt.isRefl h₁
    | inr h₂ => exact IsSymm.isRefl h₂
