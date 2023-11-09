section chapter_3

variable (p q r : Prop)

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
        (λ (hp : p) => show q ∨ p from Or.inr hp)
        (λ (hq : q) => show q ∨ p from Or.inl hq))
    -- (<=)
    (λ (h : q ∨ p) =>
      h.elim
        (λ (hq : q) => show p ∨ q from Or.inr hq)
        (λ (hp : p) => show p ∨ q from Or.inl hp))

-- associativity of ∧
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    -- (=>)
    (λ (h : (p ∧ q) ∧ r) =>
      And.intro
        (show p from h.left.left)
        (show q ∧ r from (And.intro h.left.right h.right)))
    -- (<=)
    (λ (h : p ∧ (q ∧ r)) =>
      And.intro
        (show p ∧ q from And.intro h.left h.right.left)
        (show r from h.right.right))

-- associativity of ∨
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    -- (=>)
    (λ (h : ((p ∨ q) ∨ r)) =>
      h.elim
        -- p ∨ q => p ∨ (q ∨ r)
        (λ (hpq : p ∨ q) =>
          hpq.elim
            (λ (hp : p) => show p ∨ (q ∨ r) from Or.inl hp)
            (λ (hq : q) => show p ∨ (q ∨ r) from Or.inr (Or.inl hq)))
        (λ (hr : r) => show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))
    -- (<=)
    (λ (h : (p ∨ (q ∨ r))) =>
      h.elim
        (λ (hp : p) => show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
        -- q ∨ r => (p ∨ q) ∨ r
        (λ (hqr : q ∨ r) =>
          hqr.elim
            (λ (hq : q) => show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
            (λ (hr : r) => show (p ∨ q) ∨ r from (Or.inr hr))))

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
