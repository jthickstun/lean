import .definitions

namespace nt

/- 
We've committed a minor sin here. We use a computational definition of gcd
(Euclid's algorithm) but we never actually prove that it computes the gcd;
we just state enough properties of it to ram through the proof of Euclid's
lemma.

This is fine from a formal perspective, but the pedagogy leaves something to
be desired. One question is whether we need to talk about Euclid's algorithm
at all? Is it possible to give a conceptual definition of gcd, get these 5
facts and proceed from there to Euclid's lemma? Are there going to be
decidability issues that force us to write down the computational definition
anyway if we go this route? 
-/

-- ripped from mathlib
lemma gcd_dvd (m n : ℕ) : (nat.gcd m n ∣ m) ∧ (nat.gcd m n ∣ n) :=
nat.gcd.induction m n
  (λn, by rw nat.gcd_zero_left; exact ⟨dvd_zero n, dvd_refl n⟩)
  (λm n npos, by rw ←nat.gcd_rec; exact λ ⟨IH₁, IH₂⟩, ⟨IH₂, (nat.dvd_mod_iff IH₂).1 IH₁⟩)

-- ripped from mathlib
lemma dvd_gcd {m n k : ℕ} : k ∣ m → k ∣ n → k ∣ nat.gcd m n :=
nat.gcd.induction m n (λn _ kn, by rw nat.gcd_zero_left; exact kn)
  (λn m mpos IH H1 H2, by rw nat.gcd_rec; exact IH ((nat.dvd_mod_iff H1).2 H2) H1)

-- ripped from mathlib
lemma gcd_mul_left (m n k : ℕ) : nat.gcd (m * n) (m * k) = m * nat.gcd n k :=
nat.gcd.induction n k
  (λk, by repeat {rw nat.mul_zero <|> rw nat.gcd_zero_left})
  (λk n H IH, by rwa [←nat.mul_mod_mul_left, ←nat.gcd_rec, ←nat.gcd_rec] at IH)

-- ripped from mathlib
lemma gcd_mul_right (m n k : ℕ) : nat.gcd (m * n) (k * n) = nat.gcd m k * n :=
by rw [mul_comm m n, mul_comm k n, mul_comm (nat.gcd m k) n, gcd_mul_left]

lemma p_not_dvd_coprime {p n : ℕ} :
  ¬ p ∣ n → irreducible p → nat.gcd p n = 1 :=
begin
  intros, simp [irreducible] at a_1,
  have hdiv : (nat.gcd p n ∣ p) ∧ (nat.gcd p n ∣ n), from gcd_dvd p n,
  have : nat.gcd p n ∣ p, from hdiv.left,
  have h : nat.gcd p n = p ∨ nat.gcd p n = 1, from
    a_1.right.right (nat.gcd p n) this,
  cases h,
  { have : p ∣ n, by simp [a_2] at hdiv; exact hdiv, contradiction },
  { assumption }
end

end nt