
import Mathlib.Tactic

section
variable (α:Type) [CommRing α]

variable (t:α)

example : {t:ℕ} → t ∣ t ^ 2  := by
  intro t 
  apply dvd_mul_left 

example : {t:α} → {n:ℕ} → n ≠ 0 →  t ∣ t ^ n := by
  intro t n h
  apply dvd_pow
  apply dvd_rfl 
  exact h

end



