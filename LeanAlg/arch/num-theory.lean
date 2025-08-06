
import Mathlib.Tactic


#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  apply h

example : Nat.Coprime 41 338 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num


#check Nat.Prime

#check Nat.prime_def_lt

section rings

variable (R:Type) [EuclideanDomain R]

example : (p:R) → (Prime p) → R := 
  λ p _ ↦ p
  

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {p m n : R} {hp:Prime p} (h : p ∣ m*n) : p ∣m ∨ p ∣ n := by
  exact Prime.dvd_or_dvd hp h

-- theorem p_of_p_sqr {m p: R} {hp:Prime p}  (h : p ∣ m ^ 2) : p ∣ m := by
--   rw [pow_dvd_pow_iff ] at h
--   done
  -- rw [pow_two, Nat.prime_two.dvd_mul] at h
  -- cases h <;> assumption



#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

end rings

