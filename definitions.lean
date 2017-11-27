namespace number_theory

/-
Basic abstract number-theoretic definitions
-/

def composite (n : ℕ) : Prop := n ≠ 0 ∧ ∃ a : ℕ, ∃ b : ℕ, a ≠ 1 ∧ b ≠ 1 ∧ n = a*b
def irreducible (p : ℕ) : Prop := p ≠ 0 ∧ p ≠ 1 ∧ ∀ k : ℕ, (k ∣ p) → (k = 1 ∨ k = p)
def prime (p : ℕ) : Prop := p ≠ 0 ∧ p ≠ 1 ∧ ∀ m n, (p ∣ m*n) → ((p ∣ m) ∨ (p ∣ n))

/-
Concrete definitions of the concepts above
-/

def zero_test : ℕ → bool
| 0  := tt
| _  := ff

def is_composite_aux (n : ℕ) : ℕ → bool
| 0 := ff
| 1 := ff
| (nat.succ m) := bor (zero_test $ n % (nat.succ m)) (is_composite_aux m)

def is_composite : ℕ → bool
| 0 := ff
| (nat.succ n) := is_composite_aux (nat.succ n) n

-- note we use 'is_prime' instead of 'is_irreducible';
-- this makes sense once we prove Euclid's lemma
def is_prime : ℕ → bool
| 0 := ff
| 1 := ff
| n := is_composite n = ff

end number_theory

/-
A bunch of stuff about lists of primes that we will need to state FTA
-/

def product : list ℕ → ℕ
| []       := 1
| (h :: t) := h * (product t)

-- helpful to work with max instead of min: what is min of []?
def lmax : list ℕ → ℕ
| []        := 0
| (h :: t)  := max h (lmax t)

def sorted : list ℕ → bool
| []        := tt
| (h :: t)  := (max h (lmax t) = h) ∧ sorted t

def plist : list ℕ → Prop
| []       := tt
| (h :: t) := number_theory.irreducible h ∧ plist t

namespace list

/-
The following definitions for permutations and insertion sort are ripped from
mathlib. But I wrote my own proofs about these objects (in list_extra.lean)
because I didn't like the ones in mathlib (they generally seemed a bit obscure
and they rope in a lot of machinery e.g. set theory that I don't want to
talk about).
-/

inductive perm {α : Type} : list α → list α → Prop
| nil   : perm [] []
| skip  : Π (x : α) {l₁ l₂ : list α}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : Π (x y : α) (l : list α), perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

infix ~ := perm

@[simp] def ordered_insert (a : ℕ) : list ℕ → list ℕ
| []       := [a]
| (b :: l) := if b ≤ a then a :: b :: l else b :: ordered_insert l

@[simp] def insertion_sort : list ℕ → list ℕ
| []       := []
| (b :: l) := ordered_insert b (insertion_sort l)

end list