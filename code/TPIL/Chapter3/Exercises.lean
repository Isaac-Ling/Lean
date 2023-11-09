section chapter_3
  variable (p q r : Prop)

  -- TODO: Change variable name conventions

  -- commutativity of ∧
  example : p ∧ q ↔ q ∧ p :=
    Iff.intro
      -- (=>)
      (λ (h : p ∧ q) => show q ∧ p from And.intro h.right h.left)
      -- (<=)
      (λ (h : q ∧ p) => show p ∧ q from And.intro h.right h.left)

  -- commutativity of ∨
  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
      -- (=>)
      (λ (h : p ∨ q) =>
        h.elim
          -- p => q ∨ p
          (λ (hp : p) => show q ∨ p from Or.inr hp)
          -- q => q ∨ p
          (λ (hq : q) => show q ∨ p from Or.inl hq))
      -- (<=)
      (λ (h : q ∨ p) =>
        h.elim
          -- q => p ∨ q
          (λ (hq : q) => show p ∨ q from Or.inr hq)
          -- p => p ∨ q
          (λ (hp : p) => show p ∨ q from Or.inl hp))

  -- associativity of ∧
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
      -- (=>)
      (λ (h : (p ∧ q) ∧ r) =>
        And.intro
          (h.left.left)
          (And.intro h.left.right h.right))
      -- (<=)
      (λ (h : p ∧ (q ∧ r)) =>
        And.intro
          (And.intro h.left h.right.left)
          (h.right.right))

  -- TODO: Use have's and shows here and onwards.
  -- associativity of ∧
  /- example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
      -- (=>)
      (λ (h : (p ∧ q) ∧ r) =>
        have h₁ : p := h.left.left
        have h₂ : q ∧ r := (And.intro h.left.right h.right)
        show p ∧ (q ∧ r) from (And.intro  hqr))
      -- (<=)
      (λ (h : p ∧ (q ∧ r)) =>
        And.intro
          (And.intro h.left h.right.left)
          (h.right.right)) -/

  -- associativity of ∨
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
      -- (=>)
      (λ (h : ((p ∨ q) ∨ r)) =>
        h.elim
          -- p ∨ q => p ∨ (q ∨ r)
          (λ (hpq : p ∨ q) =>
            hpq.elim
              -- p => p ∨ (q ∨ r)
              (λ (hp : p) => show p ∨ (q ∨ r) from Or.inl hp)
              -- q => p ∨ (q ∨ r)
              (λ (hq : q) => show p ∨ (q ∨ r) from Or.inr (Or.inl hq)))
          -- r => p ∨ (q ∨ r)
          (λ (hr : r) => Or.inr (Or.inr hr)))
      -- (<=)
      (λ (h : (p ∨ (q ∨ r))) =>
        h.elim
          -- p => (p ∨ q) ∨ r
          (λ (hp : p) => Or.inl (Or.inl hp))
          -- q ∨ r => (p ∨ q) ∨ r
          (λ (hqr : q ∨ r) =>
            hqr.elim
              -- q => (p ∨ q) ∨ r
              (λ (hq : q) => Or.inl (Or.inr hq))
              -- r => (p ∨ q) ∨ r
              (λ (hr : r) => (Or.inr hr))))

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
      -- (=>)
      (sorry)
      -- (<=)
      (sorry)

  -- distributivity
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) := sorry
  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ False ↔ p := sorry
  example : p ∧ False ↔ False := sorry
  example : (p → q) → (¬q → ¬p) := sorry
end chapter_3
