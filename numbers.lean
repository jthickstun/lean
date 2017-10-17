import .distance

namespace number_theory

/-
Propositional logic is decidable; is there a tactic that will just do these for me?
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

/-
Basic results
-/

lemma lt_one_zero (n : ℕ) : n < 1 → n = 0 :=
assume h : n < 1,
have h1 : n+1 ≤ 0+1, from h,
nat.eq_zero_of_le_zero (le_of_add_le_add_right h1)

lemma zero_ne_one : 0 ≠ 1 := by simp [(nat.succ_ne_zero 0)]

lemma foil (m n : ℕ) : (nat.succ m)*(nat.succ n) = 1 + m + n + m*n := 
calc (nat.succ m)*(nat.succ n) = (1+m)*(1+n) : by rw [←nat.one_add m, ←nat.one_add n]
           ... = 1 * 1 + m * 1 + (1 + m) * n : by rw [left_distrib, right_distrib]
           ... = 1 + m + n + m*n             : by rw [one_mul, mul_one, right_distrib]; simp

-- I worked pretty hard for this; is there an easier way?
lemma unique_unit (m n : ℕ) (H : m*n = 1) : m = 1 ∧ n = 1 :=
begin
induction m,
case nat.zero { 
  induction n,
  case nat.zero { from absurd H zero_ne_one },
  case nat.succ n {
    have h: 0 = 1, from zero_mul (nat.succ n) ▸ H,
    show _, from absurd h zero_ne_one 
  }
 },
case nat.succ m ih {
  induction n,
  case nat.zero { from absurd H zero_ne_one },
  case nat.succ n {
    have h : 1 + 0 = 1 + (m + n + m*n), from
    calc 1 + 0 = 1                 : rfl
           ... = 1 + m + n + m*n   : by rw [←foil, H]
           ... = 1 + (m + n + m*n) : by simp,
    have hz : m + (n + m*n) = 0, by simp [nat.add_left_cancel h],
    show _, from and.intro
      (have hmz: m = 0, from nat.eq_zero_of_add_eq_zero_right hz,
       show nat.succ m = 1, by rw [hmz])
      (have hmnz: n + m * n = 0, from nat.eq_zero_of_add_eq_zero_left hz,
       have hnz: n = 0, from nat.eq_zero_of_add_eq_zero_right hmnz,
       show nat.succ n = 1, by rw [hnz])
   }
}
end

lemma no_zero_divisors (m n : ℕ) : m*n ≠ 0 → m ≠ 0 ∧ n ≠ 0 :=
assume hmn : m*n ≠ 0,
have (m = 0 ∨ n = 0) → m*n = 0, from
  assume h : m = 0 ∨ n = 0, or.elim h
    (assume hm : m = 0, (eq.symm hm) ▸ zero_mul n)
    (assume hn : n = 0, (eq.symm hn) ▸ mul_zero m),
have ¬(m = 0 ∨ n = 0), from (mt this) hmn,
(iff.elim_left (demorgan (m=0) (n=0))) this

/- 
This lemma is fundamental.

Uniqueness is subtle as always. Most proofs of this I saw come in one of two flavors:
  (i) Assume two different (distinct) pairs and derive a contradiction
  (ii) Show that -1 < difference < 1 and conclude that there is no difference
       (because the numbers in question must be integers)
I chose the second approach here, but I wanted to avoid talking about integers (this
would require pulling in the whole ℤ library and setting up some possibly messy
correspondences between ℕ and ℤ). So instead, I modified approach (ii) to use
distances instead of differences; the whole argument goes through and we completely
avoid talking about negative numbers. The tradeoff is that we need to develop some
theory about the distance function (see .distance).
-/
lemma division (m n : ℕ) (h: m > 0) : ∃!k : ℕ, ∃!r : ℕ, n = m*k + r ∧ r < m :=
exists_unique.intro (n/m) 
  (exists_unique.intro (n%m)
    (and.intro
      (by simp [nat.mod_add_div n m]) 
      (nat.mod_lt n h))
    (assume r' : ℕ, assume hr' : n = m*(n/m) + r' ∧ r' < m, 
    have m*(n/m) + (n%m) = m*(n/m) + r', from
    calc m*(n/m) + (n%m) = n             : by simp [nat.mod_add_div n m]
                    ...  = m*(n/m) + r'  : by rw [←(and.left hr')],
    show r' = n%m, by simp [add_left_cancel this])) 
  (assume k' : ℕ, assume he: ∃! (r : ℕ), n = m * k' + r ∧ r < m,
  exists_unique.elim he 
    (assume r' : ℕ, assume hnrk : n = m*k' + r' ∧ r' < m,
    assume ha : ∀ (y : ℕ), n = m*k' + y ∧ y < m → y = r',
    have hdiv : m*(n/m) + (n%m) = n, by simp [nat.mod_add_div n m],

    -- why did I need to write this out where the hnrk rearrangement just works below?
    have hrearrange : n - (n%m) = m*(n/m), from 
    calc n - (n%m) = m*(n/m) + (n%m) - (n%m) : by rw [hdiv]
               ... = m*(n/m)                 : by simp only [nat.add_sub_cancel],

    -- again, why is hdiv more of a pain to deal with than hnrk?
    have hrln : r' ≤ n, from
      have r' + m*k' = n, by simp [hnrk.left],
      nat.le.intro (this),
    have hnmln : n%m ≤ n, from
      have m*(n/m) + n%m = n, by simp [hdiv],
      have n%m + m*(n/m) = n, by rw [nat.add_comm, this],
      nat.le.intro (this),

    have dist (m*k') (m*(n/m)) < 1*m, from
    calc dist (m*k') (m*(n/m)) = dist (n - r') (m*(n/m))   : by rw [hnrk.left]; simp only [nat.add_sub_cancel]
                           ... = dist (n - r') (n - (n%m)) : by rw [hrearrange]
                           ... = dist r' (n%m)             : dist_cancel_sub 
                                                               (hrln)
                                                               (hnmln)
                           ... < m                         : bounded_dist 
                                                               (hnrk.right)
                                                               (nat.mod_lt n h)
                           ... = 1*m                       : eq.symm (one_mul m),

    have hbound : (dist (m*k') (m*(n/m)))/m < 1, from 
      (iff.elim_right (nat.div_lt_iff_lt_mul (dist (m*k') (m*(n/m))) 1 h)) this,

    have hmul : dist (m*k') (m*(n/m)) = m * dist k' (n/m), 
      by repeat { rw [mul_comm m] }; from dist_mul k' (n/m) m,

    have dist k' (n/m) < 1, from 
    calc dist k' (n/m) = (m * dist k' (n/m)) / m     : by rw [nat.mul_div_right (dist k' (n/m)) h]
                   ... = (dist (m*k') (m*(n/m))) / m : by rw [hmul]
                   ... < 1                           : hbound,

    have dist k' (n/m) = 0, from lt_one_zero (dist k' (n/m)) this,
    show k' = n/m, from (dist_iden k' (n/m)).elim_left this))

/-
Divisors
-/

-- see dvd for commutative semiring (same definition; I should use the built-in stuff)
def divides (m n : ℕ) : Prop := ∃ k : ℕ, k*m = n
infix ` || ` := divides

def irreducible (p : ℕ) : Prop := p ≠ 0 ∧ p ≠ 1 ∧ ∀ k : ℕ, (k || p) → (k = 1 ∨ k = p)
def prime (p : ℕ) : Prop := p ≠ 0 ∧ p ≠ 1 ∧ ∀ m n, (p || m*n) → ((p || m) ∨ (p || n))

/-
This is actually the opposite direction of the lemma attributed to Euclid.
The other direction (irreducible p → prime p) seems much harder; it typically
runs through Bezout's identity, which requires some claims about integers,
greatest common divisors, and the Euclidean algorithm.

Euclid's lemma p → irreducible p is used as a lemma to prove the fundamental
theorem of arithmetic in the traditional development. However, there appears to
be a very slick direct proof of FTA by induction. Euclid's classic result would 
then become a corollary of FTA and this might be the most efficient way to develop
basic number theory.

I wrote this proof before I figured out how to use tactics; can it be made more
elegant? Most of the book-keeping seems to come from chasing down quantifiers and
propositonal connectives, so it's not clear whether tactics can help all that much.
-/
lemma euclid (p : ℕ) : prime p → irreducible p  := 
(assume hprime : p ≠ 0 ∧ p ≠ 1 ∧ ∀ m n, (p || m*n) → ((p || m) ∨ (p || n)),
have h : ∀ m n, (p || m*n) → ((p || m) ∨ (p || n)), from and.elim_right (and.elim_right hprime),
and.intro (and.elim_left hprime) (and.intro (and.elim_left (and.elim_right hprime)) 
(assume k, assume hkp : k || p, 
exists.elim hkp (
(assume r, assume hrkp : r*k = p,
  have nzrk : r ≠ 0 ∧ k ≠ 0, from no_zero_divisors r k ((eq.symm hrkp) ▸ (and.left hprime)),
  have hrgz : r > 0, from nat.pos_of_ne_zero (and.left nzrk),
  have hkgz : k > 0, from nat.pos_of_ne_zero (and.right nzrk),
  have p || r*k, from exists.intro 1 (eq.symm (nat.one_mul p) ▸ (eq.symm hrkp)),
  or.elim (h r k this)
    (assume hpr : p || r, exists.elim hpr (assume s, assume hspr : s*p = r,
    have 1*r = (s*k)*r, from
    calc 1*r = r           : one_mul r
     ...     = s*(r*k)     : eq.symm hrkp ▸ eq.symm hspr
     ...     = s*(k*r)     : (nat.mul_comm k r) ▸ (eq.refl (s*(k*r)))
     ...     = (s*k)*r     : eq.symm (nat.mul_assoc s k r),
    have s*k = 1, from nat.eq_of_mul_eq_mul_right hrgz (eq.symm this),
    or.intro_left _ (and.right (unique_unit s k this))))
    (assume hpk : p || k, exists.elim hpk (assume s, assume hspk : s*p = k,
    have 1*k = (s*r)*k, from 
    calc 1*k = k           : one_mul k
     ...     = s*p         : eq.symm hspk ▸ (eq.refl k)
     ...     = s*(r*k)     : eq.symm hrkp ▸ (eq.refl (s*p))
     ...     = (s*r)*k     : eq.symm (nat.mul_assoc s r k),
    have 1 = s*r, from nat.eq_of_mul_eq_mul_right hkgz this,
    have s = 1, from and.left (unique_unit s r (eq.symm this)),
    have 1*p = k, from (this ▸ hspk),
    or.intro_right _ (eq.symm (this ▸ eq.symm (nat.one_mul p))))))))))

/-
Warm-up to FTA
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
| (h :: t) := irreducible h ∧ plist t

lemma product_concat (l1 l2 : list ℕ) : product (l1 ++ l2) = (product l1) * (product l2) :=
begin
induction l1,
{ by simp [product] },
{ by simp [product, ih_1] }
end

lemma plist_concat (l1 l2 : list ℕ) : plist l1 → plist l2 → plist (l1 ++ l2) :=
begin
induction l1,
{ from λ h1 : plist [], λ h2 : plist l2, by simp [h2] },
{ from λ h1 : plist (a :: a_1), λ h2 : plist l2, and.intro 
    (and.elim_left h1) 
    (ih_1 (and.elim_right h1) h2)
}
end

-- First we prove existence
lemma prime_factorization (n : ℕ) : n ≠ 0 → ∃ l : list ℕ, plist l ∧ product l = n :=
begin
induction n,
case nat.zero n {
  from assume h : 0 ≠ 0, absurd (eq.refl 0) h
},
case nat.succ n ih { 
  let m := nat.succ n,
  from assume h : nat.succ n ≠ 0,
  have one_or_more : m = 1 ∨ (m ≠ 0 ∧ m ≠ 1), by {
    cases n, exact or.inl rfl, exact or.inr (and.intro h 
      (λ k, nat.no_confusion k (λ k, nat.no_confusion k)))
  },
  or.elim one_or_more
    (assume h1: m = 1, exists.intro [] 
      (and.intro 
        (show plist [], from rfl)
        (show product [] = m, by simp [h1, product])))
    (assume hg1: m ≠ 0 ∧ m ≠ 1,
    -- do I need LEM for this??
    have h : irreducible m ∨ (∃ a : ℕ, ∃ b : ℕ, m = a*b), by {
      from sorry
    },
    or.elim h 
      (assume hm : irreducible m, exists.intro [m] 
        (and.intro 
          (show plist [m], by simp [plist]; from and.intro (hm) (rfl))
          (show product [m] = m, by simp [product])))
      (assume hab : ∃ a : ℕ, ∃ b : ℕ, m = a*b,
      -- is there a more elegant way to handle multiple existential quantifiers?
      -- I couldn't get ∃ a b, m = a*b to work...
      exists.elim hab (assume a, assume hab1 : ∃ b : ℕ, m = a*b,
      exists.elim hab1 (assume b, assume hprod : m = a*b,
      -- need strong induction for these
      -- also can I induction on whole numbers instead of naturals?
      have hrl : ∃ rl, plist rl ∧ product rl = a, from sorry,
      have hsl : ∃ sl, plist sl ∧ product sl = b, from sorry,
      exists.elim hrl (assume rl : list ℕ, assume hrla: plist rl ∧ product rl = a,
      exists.elim hsl (assume sl : list ℕ, assume hslb: plist sl ∧ product sl = b,
      exists.intro (rl ++ sl)
        (and.intro 
          (show plist (rl ++ sl), from plist_concat rl sl (and.left hrla) (and.left hslb))
          (show product (rl ++ sl) = m, 
            by rw [product_concat rl sl, and.right hrla, and.right hslb, hprod]))))))))
}
end

end number_theory