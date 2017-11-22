import .distance
import .definitions
import .gcd
import .nat_extra
import .list_extra
import .decidable_relations

namespace number_theory

/-
Basic results
-/

lemma foil (m n : ℕ) : (nat.succ m)*(nat.succ n) = 1 + m + n + m*n := 
calc (nat.succ m)*(nat.succ n) = (1+m)*(1+n) : by rw [←nat.one_add m, ←nat.one_add n]
           ... = 1 * 1 + m * 1 + (1 + m) * n : by rw [left_distrib, right_distrib]
           ... = 1 + m + n + m*n             : by rw [one_mul, mul_one, right_distrib]; simp

lemma unique_unit (m n : ℕ) (H : m*n = 1) : m = 1 ∧ n = 1 :=
begin revert m, induction n with n ih,
{ intros; contradiction },
{intro m, intro H; cases m with m,
  { have h01 : 0 = 1, by rw [←H]; simp, contradiction },
  { have h : 1 + 0 = 1 + (m + n + m*n), from
    calc 1 + 0 = 1                            : rfl
           ... = (nat.succ m) * (nat.succ n)  : by rw [←H]
           ... = 1 + (m + n + m*n)            : by rw [foil]; simp,
    have hz : m + (n + m*n) = 0, by simp [nat.add_left_cancel h],
    from and.intro
      (have hmz: m = 0, from nat.eq_zero_of_add_eq_zero_right hz,
       show nat.succ m = 1, by rw [hmz])
      (have hmnz: n + m * n = 0, from nat.eq_zero_of_add_eq_zero_left hz,
       have hnz: n = 0, from nat.eq_zero_of_add_eq_zero_right hmnz,
       show nat.succ n = 1, by rw [hnz])
  }
}
end

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

    have dist k' (n/m) = 0, from nat.lt_one_zero (dist k' (n/m)) this,
    show k' = n/m, from (dist_iden k' (n/m)).elim_left this))

/-
Euclid's lemma irreducible p → prime p is used as a lemma to prove the 
fundamental theorem of arithmetic in the traditional development. The
other direction also holds.

I wrote the proof of the converse before I figured out how to use tactics;
can it be made more elegant? Most of the book-keeping seems to come from
chasing down quantifiers and propositonal connectives, so it's not clear
whether tactics can help all that much, although at least it would kill
off a lots of irritating stupid parentheses.
-/
lemma euclid (p : ℕ) : irreducible p ↔ prime p :=
iff.intro (
begin
intro h,
have hi : irreducible p, from h,
simp [irreducible] at h, simp [prime],
by_cases (p = 0) with h0,
{ have : ¬p = 0, from h.right.left, contradiction },
{ by_cases (p = 1) with h1,
  { have : ¬p = 1, from h.left, contradiction },
  { apply and.intro, exact h1, apply and.intro, exact h0,
    have ha : ∀ (k : ℕ), k ∣ p → k = p ∨ k = 1, from h.right.right,
    intros, by_cases (m % p = 0) with hmp,
    { have : p ∣ m, by simp [nat.dvd_iff_mod_eq_zero]; exact hmp,
      apply or.intro_left, exact this
    },
    { have : ¬ p ∣ m, by simp [nat.dvd_iff_mod_eq_zero]; exact hmp,
      have hpdiv : p ∣ nat.gcd (p*n) (m*n), by simp [dvd_gcd nat.m_dvd_mn a],
      apply or.intro_right,
      have : nat.gcd (p*n) (m*n) = n, from calc
             nat.gcd (p*n) (m*n) = n * nat.gcd p m  : by simp [gcd_mul_right p n m]
                             ... = n                : by simp [p_not_dvd_coprime this hi],
      from this ▸ hpdiv
    }
  }
}
end)
(assume hprime : p ≠ 0 ∧ p ≠ 1 ∧ ∀ m n, (p ∣ m*n) → ((p ∣ m) ∨ (p ∣ n)),
have h : ∀ m n, (p ∣ m*n) → ((p ∣ m) ∨ (p ∣ n)), from and.elim_right (and.elim_right hprime),
and.intro (and.elim_left hprime) (and.intro (and.elim_left (and.elim_right hprime)) 
(assume k, assume hkp : k ∣ p, 
dvd.elim hkp (
(assume r, assume hrkp : p = k*r,
  have r*k ≠ 0, by simp only [nat.mul_comm]; rw [←hrkp]; apply (and.left hprime),
  have nzrk : r ≠ 0 ∧ k ≠ 0, from nat.no_zero_divisors this,
  have hrgz : r > 0, from nat.pos_of_ne_zero (and.left nzrk),
  have hkgz : k > 0, from nat.pos_of_ne_zero (and.right nzrk),
  have p ∣ r*k, from exists.intro 1 (by simp [hrkp]),
  or.elim (h r k this)
    (assume hpr : p ∣ r, dvd.elim hpr (assume s, assume hspr : r = p*s,
    have 1*r = (s*k)*r, from
    calc 1*r = r           : one_mul r
     ...     = s*p         : by simp [hspr,nat.mul_comm]
     ...     = s*(k*r)     : by simp [hrkp,nat.mul_comm]
     ...     = (s*k)*r     : eq.symm (nat.mul_assoc s k r),
    have s*k = 1, from nat.eq_of_mul_eq_mul_right hrgz (eq.symm this),
    or.intro_left _ (and.right (unique_unit s k this))))
    (assume hpk : p ∣ k, dvd.elim hpk (assume s, assume hspk : k = p*s,
    have 1*k = (s*r)*k, from 
    calc 1*k = k           : one_mul k
     ...     = s*p         : by rw [hspk]; simp
     ...     = s*(r*k)     : by simp [hrkp]
     ...     = (s*r)*k     : eq.symm (nat.mul_assoc s r k),
    have 1 = s*r, from nat.eq_of_mul_eq_mul_right hkgz this,
    have s = 1, from and.left (unique_unit s r (eq.symm this)),
    have 1*p = k, by simp [this,hspk],
    or.intro_right _ (eq.symm (this ▸ eq.symm (nat.one_mul p))))))))))

/-
Warm-up to FTA: existence of prime factorizations
-/

-- First we prove existence
lemma prime_factorization (n : ℕ) : n ≠ 0 → ∃ l : list ℕ, plist l ∧ product l = n :=
begin
induction n using nat.case_strong_induction_on with n ih,
{
  intros; contradiction
},
{
  -- this is a kind of messy way to handle induction from 1
  let m := nat.succ n,
  from assume hmz : m ≠ 0,
  have one_or_more : m = 1 ∨ (m ≠ 0 ∧ m ≠ 1), by {
    cases n, exact or.inl rfl, exact or.inr (and.intro hmz 
      (λ k, nat.no_confusion k (λ k, nat.no_confusion k)))
  },
  or.elim one_or_more
    (assume h1: m = 1, exists.intro [] 
      (and.intro 
        (show plist [], from rfl)
        (show product [] = m, by simp [h1, product])))
    (assume hg1: m ≠ 0 ∧ m ≠ 1,
    -- this is the big excluded middle claim!
    -- we did all that legwork in .decidable_relations for this
    have h : irreducible m ∨ composite m, by {
      by_cases (is_composite m = tt) with hicm,
      { simp [computable_composite] at hicm, 
        apply or.intro_right, assumption
      },
      { simp [computable_composite] at hicm, 
        apply or.intro_left, exact (not_composite hg1).1 hicm 
      }
    },
    or.elim h 
      (assume hm : irreducible m, exists.intro [m]
        (and.intro 
          (show plist [m], by simp [plist]; from and.intro (hm) (rfl))
          (show product [m] = m, by simp [product])))
      (assume hm' : composite m,
      have hab : ∃ a : ℕ, ∃ b : ℕ, a ≠ 1 ∧ b ≠ 1 ∧ m = a*b, by
        delta composite at hm'; exact hm'.right,
      -- is there a more elegant way to handle multiple existential quantifiers?
      -- I couldn't get ∃ a b, m = a*b to work...
      exists.elim hab (assume a, assume hab1 : ∃ b : ℕ, a ≠ 1 ∧ b ≠ 1 ∧ m = a*b,
      exists.elim hab1 (assume b, assume hprod : a ≠ 1 ∧ b ≠ 1 ∧ m = a*b,
      have hrl : ∃ rl, plist rl ∧ product rl = a, from 
        have han : a ≤ n, by {
          have : a ∣ m, from dvd.intro b (eq.symm hprod.right.right),
          have haltm : a ≤ m, from nat.le_of_dvd (nat.pos_of_ne_zero hmz) this,
          have hanm : a ≠ m, by {
            -- can we abstract this logic out as a lemma?
            -- it appears again below and in not_composite
            by_cases (a = m) with ham,
            { have : m = m*b, by rw [ham] at hprod; exact hprod.right.right,
              have : m*1 = m*b, by simp; exact this,
              have : 1 = b, from nat.eq_of_mul_eq_mul_left (nat.pos_of_ne_zero hmz) this,
              from absurd (eq.symm this) hprod.right.left
            },
            { assumption }
          },
          from nat.le_ne_succ haltm hanm
        },
        have hanz : a ≠ 0, by { 
          have : a*b = m, from eq.symm hprod.right.right,
          have : a*b ≠ 0, by rw [←this] at hmz; assumption,
          apply (nat.no_zero_divisors this).left
        },
        ih a han hanz,
      have hsl : ∃ sl, plist sl ∧ product sl = b, from
        -- this whole argument is almost copy-pasted from case above
        have hbn : b ≤ n, by {
          have hmba : m = b*a, by simp [nat.mul_comm, hprod.right.right],
          have : b ∣ m, from dvd.intro a (eq.symm hmba),
          have haltm : b ≤ m, from nat.le_of_dvd (nat.pos_of_ne_zero hmz) this,
          have hanm : b ≠ m, by {
            by_cases (b = m) with hbm,
            { have : m = m*a, by rw [hbm] at hmba; exact hmba,
              have : m*1 = m*a, by simp; exact this,
              have : 1 = a, from nat.eq_of_mul_eq_mul_left (nat.pos_of_ne_zero hmz) this,
              from absurd (eq.symm this) hprod.left
            },
            { assumption }
          },
          from nat.le_ne_succ haltm hanm
        },
        have hbnz : b ≠ 0, by {
          have : a*b = m, from eq.symm hprod.right.right,
          have : a*b ≠ 0, by rw [←this] at hmz; assumption,
          apply (nat.no_zero_divisors this).right
        },
        ih b hbn hbnz,
      exists.elim hrl (assume rl : list ℕ, assume hrla: plist rl ∧ product rl = a,
      exists.elim hsl (assume sl : list ℕ, assume hslb: plist sl ∧ product sl = b,
      exists.intro (rl ++ sl)
        (and.intro 
          (show plist (rl ++ sl), from list.plist_concat rl sl (and.left hrla) (and.left hslb))
          (show product (rl ++ sl) = m,
            by rw [list.product_concat rl sl,
                   and.right hrla,
                   and.right hslb,
                   hprod.right.right]))))))))
}
end

/-
Fundamental Theorem of Arithmetic (very incomplete!)
To finish we need to prove a bunch of stuff about sorted lists of primes.
At the moment I don't see any way to avoid defining a sort function to do this.
-/

theorem prime_uniqueness (n : ℕ) : n ≠ 0 → ∃! l : list ℕ,
  plist l ∧ sorted l ∧ product l = n :=
begin
intro hn, apply exists_unique.intro,
{ have : ∃ l : list ℕ, plist l ∧ product l = n, from prime_factorization n hn,
  admit
},
{ admit },
{ exact [n] } -- why is this here?
end

end number_theory