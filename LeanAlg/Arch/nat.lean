import Mathlib.Tactic



#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h


example {m n :ℕ} (h:m^2 = 2*n) : 2 ∣ m^2 := by
  use n

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    apply even_of_even_sqr
    use n^2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := by
    have : 2 ≠ 0 := by norm_num
    apply (mul_right_inj' this).mp
    assumption
  have : 2 ∣ n := by
    apply even_of_even_sqr
    use k ^ 2
    rw [this]  
  have : 2 ∣ m.gcd n := by
    apply dvd_gcd 
    <;> assumption
  have : 2 ∣ 1 := by
    rw [ coprime_mn ] at this
    assumption
  norm_num at this

#check Prime.dvd_mul

theorem p_dvd_of_p_dvd_sqr  { m p : ℕ } {hp: Prime p} (h: p ∣ m^2) : p ∣ m := by
  rw [pow_two, Prime.dvd_mul hp] at h
  cases h <;> assumption

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : Prime p) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have : p ∣ m := by
    apply p_dvd_of_p_dvd_sqr
    · assumption
    · use n^2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := by
    have : p ≠ 0 := Prime.ne_zero prime_p
    apply (mul_right_inj' this).mp 
    assumption
  have : p ∣ n := by
    apply p_dvd_of_p_dvd_sqr
    · exact prime_p
    · use k ^ 2
      rw [this]  
  have : p ∣ m.gcd n := by
    apply dvd_gcd 
    <;> assumption
  have : p ∣ 1 := by
    rw [ coprime_mn ] at this
    assumption
  apply Prime.not_dvd_one prime_p this


#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList



--------------------------------------------------------------------------------

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem np_factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp


#check Nat.Prime.factorization

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw [ factorization_pow' ]
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [ factorization_mul' (Nat.Prime.ne_zero prime_p) nsqr_nez] 
    rw [ factorization_pow', np_factorization' prime_p  ]
    ring
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this


example ( p:ℕ) (hp:p.Prime) : p ≠ 0 := by
   apply Nat.Prime.ne_zero 
   assumption




def  fac : ℕ → ℕ
  | 0 => 1
  | n+1 => (n+1)*fac n

theorem fac_pos (n:ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    --exact zero_lt_one
    linarith
  · rw [fac]
    apply mul_pos
    · apply Nat.succ_pos       
    · apply ih

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  rfl--  Finset.sum_range_zero f


example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n :=
  Finset.sum_range_succ f n


example (n:ℕ) : fac n = ∏ i ∈ range n, (i+1) := by
  induction' n with n ih
  simp [fac]
  simp [fac, ih, Finset.prod_range_succ, mul_comm ]



example (r:α) [Field α] ( h: r ≠ 1 ) (n : ℕ) : (∑ x in range n, r^x) = (r^(n+1) - 1)/(r-1) := by 
  have : r-1 ≠ 0 := by exact sub_ne_zero_of_ne h
  have : r*(∑ x in range n, r^x) = ∑ x in range 1 (n+1), r^x := by simp


