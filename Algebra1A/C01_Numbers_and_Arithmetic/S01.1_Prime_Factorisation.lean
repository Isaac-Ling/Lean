import Mathlib.Data.Int.Basic
import Mathlib.Tactic

section Prime_Factorisation

def divides (a b : ℤ) : Prop :=
  ∃ n : ℤ, b = n * a

-- a | b ↔ a divides b
infix:50 " | " => divides

def prime (p : ℕ) :=
  p ≥ 2 ∧ ∀ a : ℕ, ((a | p) → (a = 1 ∨ a = p))

lemma divides_both_ways {a b : ℤ} (a_div_b : a | b) (b_div_a : b | a) : (a = b) ∨ (a = -b) := by
  -- Obtain the factorisations of a and b from the assumptions
  obtain ⟨n, b_factorise⟩ := a_div_b
  obtain ⟨m, a_factorise⟩ := b_div_a

  -- Substitute the factorisation of a into the factorisation of b
  rw [a_factorise, ← mul_assoc] at b_factorise

  -- Minus nmb from both sides
  have b_minus_b : b - n * m * b = 0 := by
    rw [← sub_self (n * m * b), sub_left_inj]
    exact b_factorise

  -- Factorise out b
  rw [mul_comm, ← mul_one b, mul_assoc, ← mul_sub_left_distrib b 1, one_mul] at b_minus_b

  -- Split into cases
  cases (mul_eq_zero.mp b_minus_b)

  -- If b = 0
  · rename_i b_is_zero
    -- Substitute into a = m * b
    rw [b_is_zero, mul_zero, ← b_is_zero] at a_factorise
    apply Or.inl a_factorise

  -- If 1 - nm = 0
  · rename_i one_minus_nm_is_zero
    -- Add nm to both sides
    have nm_is_one : n * m = 1 := by
      exact Eq.symm (sub_eq_zero.mp one_minus_nm_is_zero)

    -- Consider all combinations of n and m
    cases Int.mul_eq_one_iff_eq_one_or_neg_one.mp nm_is_one

    -- If n = 1 ∧ m = 1
    · rename_i n_m_eq_one
      rw [n_m_eq_one.right, one_mul] at a_factorise
      exact Or.inl a_factorise

    -- If n = -1 ∧ m = -1
    · rename_i n_m_eq_neg_one
      rw [n_m_eq_neg_one.right, neg_one_mul] at a_factorise
      exact Or.inr a_factorise

lemma divides_two_nums {m a b : ℤ} (m_div_a : m | a) (m_div_b : m | b) : ∀ α β : ℤ, m | (α * a + β * b) := by
  -- Obtain the factorisations of m from the assumptions
  obtain ⟨γ, a_factors_m⟩ := m_div_a
  obtain ⟨δ, b_factors_m⟩ := m_div_b

  intro α β

  -- Rearrange α * a + β * b as (γ * α + δ * β) * m
  have m_factors_linear_comb : α * a + β * b = (α * γ + β * δ) * m :=
    calc
      α * a + β * b = α * (γ * m) + β * (δ * m) := by rw [a_factors_m, b_factors_m]
      _             = (α * γ) * m + (β * δ) * m := by rw [mul_assoc, mul_assoc]
      _             = (α * γ + β * δ) * m       := by rw [← add_mul]

  -- Then m divides α * a + β * b
  exact Exists.intro (α * γ + β * δ) m_factors_linear_comb

-- Product of primes
theorem prime_factorisation {m : ℤ} (m_gt_two : m > 2) : ∃ factorisation : List ℕ, List.prod factorisation = m ∧ (∀ n ∈ factorisation, prime n) := by
  sorry

end Prime_Factorisation
