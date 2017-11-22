/-
Seems like this should be in the standard library.
-/

lemma demorgan (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
(assume h : ¬(p ∨ q),
  show ¬p ∧ ¬q, from
  and.intro
    (assume hp : p, absurd (or.intro_left q hp) h)
    (assume hq : q, absurd (or.intro_right p hq) h))
(assume h : ¬p ∧ ¬q,
  show ¬(p ∨ q), from
  assume h1 : p ∨ q, 
  or.elim h1
    (assume hp : p, absurd hp (and.left h))
    (assume hq : q, absurd hq (and.right h)))