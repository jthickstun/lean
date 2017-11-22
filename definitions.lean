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

def lmax : list ℕ → ℕ
| []       := 0
| (h :: t) := max h (lmax t)

def sorted : list ℕ → bool
| []       := tt
| (h :: t) := (max h (lmax t) = h) ∧ sorted t

def plist : list ℕ → Prop
| []       := tt
| (h :: t) := number_theory.irreducible h ∧ plist t