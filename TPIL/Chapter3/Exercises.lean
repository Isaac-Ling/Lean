section chapter_3

variable (p q r : Prop)

-- commutativity of ∧
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    -- (=>)
    (fun (h : p ∧ q) => show q ∧ p from And.intro h.right h.left)
    -- (<=)
    (fun (h : q ∧ p) => show p ∧ q from And.intro h.right h.left)

-- commutativity of ∨
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    -- (=>)
    (fun (h : p ∨ q) =>
      h.elim
        (fun (hp : p) => show q ∨ p from Or.inr hp)
        (fun (hq : q) => show q ∨ p from Or.inl hq))
    -- (<=)
    (fun (h : q ∨ p) =>
      h.elim
        (fun (hq : q) => show p ∨ q from Or.inr hq)
        (fun (hp : p) => show p ∨ q from Or.inl hp))

-- associativity of ∧
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    -- (=>)
    (fun (h : (p ∧ q) ∧ r) =>
      And.intro
        (show p from h.left.left)
        (show q ∧ r from (And.intro h.left.right h.right)))
    -- (<=)
    (fun (h : p ∧ (q ∧ r)) =>
      And.intro
        (show p ∧ q from And.intro h.left h.right.left)
        (show r from h.right.right))

-- associativity of ∨
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    -- (=>)
    (fun (h : ((p ∨ q) ∨ r)) =>
      h.elim
        -- p ∨ q => p ∨ (q ∨ r)
        (fun (hpq : p ∨ q) =>
          hpq.elim
            (fun (hp : p) => show p ∨ (q ∨ r) from Or.inl hp)
            (fun (hq : q) => show p ∨ (q ∨ r) from Or.inr (Or.inl hq)))
        (fun (hr : r) => show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))
    -- (<=)
    (fun (h : (p ∨ (q ∨ r))) =>
      h.elim
        (fun (hp : p) => show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
        -- q ∨ r => (p ∨ q) ∨ r
        (fun (hqr : q ∨ r) =>
          hqr.elim
            (fun (hq : q) => show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
            (fun (hr : r) => show (p ∨ q) ∨ r from (Or.inr hr))))

-- distributivity of ∧
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    -- (=>)
    (fun (h : p ∧ (q ∨ r)) =>
      have hp : p := h.left
      h.right.elim
        (fun (hq : q) => show (p ∧ q) ∨ (p ∧ r) from Or.inl (And.intro hp hq))
        (fun (hr : r) => show (p ∧ q) ∨ (p ∧ r) from Or.inr (And.intro hp hr)))
    -- (<=)
    (fun (h : (p ∧ q) ∨ (p ∧ r)) =>
      have hp : p :=
        h.elim
          (fun (hpq : p ∧ q) => show p from hpq.left)
          (fun (hpr : p ∧ r) => show p from hpr.left)
      have hqr : q ∨ r :=
        h.elim
          (fun (hpq : p ∧ q) => Or.inl hpq.right)
          (fun (hpr : p ∧ r) => Or.inr hpr.right)
      And.intro hp hqr)

-- distributivity of ¬
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    -- (=>)
    (λ (nhpq : ¬(p ∨ q)) =>
      And.intro
        (λ (hp : p) => show False from nhpq (show p ∨ q from Or.inl hp))
        (λ (hq : q) => show False from nhpq (show p ∨ q from Or.inr hq)))
    -- (<=)
    (λ (hnpnq : ¬p ∧ ¬q) =>
      λ (hpq : p ∨ q) =>
        show False from sorry)

-- TODO
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

end chapter_3
