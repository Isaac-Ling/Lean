section chapter_4

-- 1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun (h : ∀ x, p x ∧ q x) =>
      And.intro
        (show ∀ x, p x from (fun hx => (h hx).left))
        (show ∀ x, q x from (fun hx =>  (h hx).right)))
    (fun (h : (∀ x, p x) ∧ (∀ x, q x)) =>
      fun x =>
        And.intro
          (show p x from (h.left x))
          (show q x from (h.right x)))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun (h : ∀ x, p x → q x) =>
    fun (hx : ∀ x, p x) =>
      fun x =>
        h x (hx x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun (h : (∀ x, p x) ∨ (∀ x, q x)) =>
    fun x =>
      h.elim
        (fun (hpx : ∀ x, p x) => show p x ∨ q x from Or.inl (hpx x))
        (fun (hqx : ∀ x, q x) => show p x ∨ q x from Or.inr (hqx x))

-- 2
open Classical

variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun x =>
    Iff.intro
      (fun (h : ∀ x, r) => show r from h x)
      (fun (hr : r) => show ∀ x, r from (fun x => hr))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

-- 3
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  (em (shaves barber barber)).elim
    (show shaves barber barber → False from
      fun (hs : shaves barber barber) => ((h barber).mp hs hs))
    (show ¬ shaves barber barber → False from
      fun (hns : ¬ shaves barber barber) =>
        absurd
          ((h barber).mpr hns)
          (hns))

-- 4
def even (n : Nat) : Prop :=
  ∃ m : Nat, n = 2 * m

-- Purely term-style proof that n * m is even if n is even
example (n : Nat) (m : Nat) : even n → even (n * m) :=
  fun (h : even n) =>
    -- Write n = 2k, k ∈ ℕ
    let ⟨k, (hk : n = 2 * k)⟩ := h
    show even (n * m) from
      Exists.intro
        (k * m)
        (calc
          n * m = n * m       := rfl
          _     = (2 * k) * m := congrArg (· * m) hk
          _     = 2 * (k * m) := Nat.mul_assoc 2 k m)

def prime (n : Nat) : Prop :=
  n > 1 ∧ ¬ (∃m : Nat, (m ≠ n ∧ m ≠ 1) ∧ (∃l : Nat, n = m * l))

def infinitely_many_primes : Prop :=
  (∀ n : Nat, ∃m : Nat, m > n ∧ prime m)

def Fermat_prime (n : Nat) : Prop := sorry
def infinitely_many_Fermat_primes : Prop := sorry
def goldbach_conjecture : Prop := sorry
def Goldbach's_weak_conjecture : Prop := sorry
def Fermat's_last_theorem : Prop := sorry

end chapter_4
