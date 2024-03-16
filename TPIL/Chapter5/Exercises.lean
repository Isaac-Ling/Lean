section chapter_5

theorem term_style (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  And.intro
    hp
    (And.intro hq hp)

theorem tactic_style (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  apply And.intro hq hp



end chapter_5
