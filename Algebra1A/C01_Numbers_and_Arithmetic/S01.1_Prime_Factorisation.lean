import Mathlib.Data.Int.Basic
import Mathlib.Tactic

section Prime_Factorisation

/-! Definition 1.1. -/

def divides (a b : ℤ) : Prop :=
  ∃ n : ℤ, b = n * a

-- a | b ↔ a divides b
infix:50 " | " => divides

def prime (p : ℕ) : Prop :=
  p ≥ 2 ∧ ∀ a : ℕ, ((a | p) → (a = 1 ∨ a = p))

/-! Lemma 1.3. -/

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

/-! Proposition 1.4. -/

-- Product of primes
theorem prime_factorisation {m : ℕ} (gt_two : m > 2) : ∃ factorisation : List ℕ, List.prod factorisation = m ∧ (∀ p ∈ factorisation, prime p) := by
  -- Induct on n ≥ 2
  induction' m using Nat.strong_induction_on with n ih

  -- Either n is prime or it isn't
  cases Classical.em (prime n)

  · rename_i n_prime
    -- If n is prime then it's factorisation is just itself
    use [n]
    constructor
    -- The product of the factorisation is trivially n
    apply List.prod_singleton

    intro p p_is_n
    rw [List.eq_of_mem_singleton p_is_n]
    -- n is prime by assumption
    assumption

  · rename_i n_composite
    -- Factorising n
    unfold prime at n_composite
    push_neg at n_composite
    specialize n_composite (le_of_lt gt_two)
    obtain ⟨a, a_conditions⟩ := n_composite
    obtain ⟨a_div_n, a_non_trivial⟩ := a_conditions
    obtain ⟨b, a_factors_n⟩ := a_div_n
    rw [mul_comm] at a_factors_n

    -- Obtaining the prime factorisations of the factors of n
    sorry

/-! Definition 1.6. -/

def common_multiple (a m n : ℕ) : Prop :=
  m | a ∧ n | a

def is_lcm (l m n : ℕ) : Prop := common_multiple l m n ∧ ∀ q : ℕ, (common_multiple q m n → q ≥ l)

def common_divisor (a m n : ℕ) : Prop :=
  a | m ∧ a | n

def is_gcd (g m n : ℕ) : Prop := common_multiple g m n ∧ ∀ q : ℕ, (common_multiple q m n → q ≤ g)

def coprime (m n : ℕ) : Prop :=
  is_gcd 1 m n

/-! Remark 1.7. -/

lemma div_by_gcd_coprime {m n g : ℕ} (g_gcd : is_gcd g m n) : coprime (m / g) (n / g) := by
  sorry

end Prime_Factorisation
