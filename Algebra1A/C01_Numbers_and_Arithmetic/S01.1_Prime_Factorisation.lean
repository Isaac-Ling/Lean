import Mathlib.Data.Int.Basic
import Mathlib.Tactic

section Prime_Factorisation

def divides (a b : ℤ) : Prop :=
  ∃ n : ℤ, b = n * a

infix:50 " | " => divides

def prime (p : ℕ) :=
  p ≥ 2 ∧ ∀ a : ℕ, ((a | p) → (a = 1 ∨ a = p))

lemma one_two {a b m : ℤ} (adivb : a | b) (bdiva : b | a) : (a = b) ∨ (a = -b) := by
  obtain ⟨n, h1⟩ := adivb
  obtain ⟨m, h2⟩ := bdiva

  rw [h2, ← mul_assoc] at h1

  have h3 : b - n * m * b = 0 := by
    rw [← sub_self (n * m * b), sub_left_inj]
    exact h1

  rw [mul_comm, ← mul_one b, mul_assoc, ← mul_sub_left_distrib b 1, one_mul] at h3

  rw [mul_eq_zero] at h3



end Prime_Factorisation
