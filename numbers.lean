import .distance
import .definitions
import .gcd
import .nat_extra
import .list_extra
import .decidable_relations

namespace nt

/-
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
begin
apply exists_unique.intro (n/m),
{ apply exists_unique.intro (n%m),
  { apply and.intro,
    { simp [nat.mod_add_div n m] },
    { exact nat.mod_lt n h }
  },
  { intro r', intro hr',
    have : m*(n/m) + (n%m) = m*(n/m) + r', from
    calc m*(n/m) + (n%m) = n             : by simp [nat.mod_add_div n m]
                    ...  = m*(n/m) + r'  : by rw [←(and.left hr')],
    show r' = n%m, by simp [add_left_cancel this]
  }
},
{ 
  intro k', intro he, apply exists_unique.elim he,
  intro r', intro hnrk, intro ha,
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

  have : dist (m*k') (m*(n/m)) < 1*m, from
  calc dist (m*k') (m*(n/m)) = dist (n - r') (m*(n/m))   : by rw [hnrk.left]; simp only [nat.add_sub_cancel]
                         ... = dist (n - r') (n - (n%m)) : by rw [hrearrange]
                         ... = dist r' (n%m)             : dist_cancel_sub hrln hnmln
                         ... < m                         : bounded_dist hnrk.right (nat.mod_lt n h)
                         ... = 1*m                       : eq.symm (one_mul m),

    have hbound : (dist (m*k') (m*(n/m)))/m < 1, from 
      (iff.elim_right (nat.div_lt_iff_lt_mul (dist (m*k') (m*(n/m))) 1 h)) this,

    have hmul : dist (m*k') (m*(n/m)) = m * dist k' (n/m), 
      by repeat { rw [mul_comm m] }; from dist_mul k' (n/m) m,

    have : dist k' (n/m) < 1, from 
    calc dist k' (n/m) = (m * dist k' (n/m)) / m     : by rw [nat.mul_div_right (dist k' (n/m)) h]
                   ... = (dist (m*k') (m*(n/m))) / m : by rw [hmul]
                   ... < 1                           : hbound,

    have : dist k' (n/m) = 0, from nat.lt_one_zero (dist k' (n/m)) this,
    exact (dist_iden k' (n/m)).elim_left this
}
end

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
begin
apply iff.intro,
{ intro h,
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
},
{ intro hprime,
  have h : ∀ m n, (p ∣ m*n) → ((p ∣ m) ∨ (p ∣ n)), from and.elim_right (and.elim_right hprime),
  apply and.intro,
  { exact and.elim_left hprime },
  { apply and.intro,
    { exact and.elim_left (and.elim_right hprime) },
    { intro k, intro hkp, apply dvd.elim hkp,
      intro r, intro hrkp,
      have : r*k ≠ 0, by simp only [nat.mul_comm]; rw [←hrkp]; apply (and.left hprime),
      have nzrk : r ≠ 0 ∧ k ≠ 0, from nat.no_zero_divisors this,
      have hrgz : r > 0, from nat.pos_of_ne_zero (and.left nzrk),
      have hkgz : k > 0, from nat.pos_of_ne_zero (and.right nzrk),
      have : p ∣ r*k, from exists.intro 1 (by simp [hrkp]),
      apply or.elim (h r k this),
      { intro hpr, apply dvd.elim hpr, intro s, intro hspr,
        have : 1*r = (s*k)*r, from
        calc 1*r = r           : one_mul r
        ...     = s*p         : by simp [hspr,nat.mul_comm]
        ...     = s*(k*r)     : by simp [hrkp,nat.mul_comm]
        ...     = (s*k)*r     : eq.symm (nat.mul_assoc s k r),
        have : s*k = 1, from nat.eq_of_mul_eq_mul_right hrgz (eq.symm this),
        apply or.intro_left, exact and.right (nat.unique_unit this)
      },
      { intro hpk, apply dvd.elim hpk, intro s, intro hspk,
        have : 1*k = (s*r)*k, from 
        calc 1*k = k           : one_mul k
        ...     = s*p         : by rw [hspk]; simp
        ...     = s*(r*k)     : by simp [hrkp]
        ...     = (s*r)*k     : eq.symm (nat.mul_assoc s r k),
        have : 1 = s*r, from nat.eq_of_mul_eq_mul_right hkgz this,
        have : s = 1, from and.left (nat.unique_unit (eq.symm this)),
        have : 1*p = k, by simp [this,hspk],
        apply or.intro_right, exact eq.symm (this ▸ eq.symm (nat.one_mul p))
      }
    }
  }
}
end

/-
Warm-up to FTA: existence of prime factorizations
-/

-- First we prove existence
lemma prime_factorization (n : ℕ) : n ≠ 0 → ∃ l : list ℕ, plist l = tt ∧ product l = n :=
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
          (show plist [m] = tt, by simp [plist,computable_irreducible]; exact to_bool_true hm)
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
The Fundamental Theorem of Arithmetic
-/

-- the statement of this lemma is a bit obscure, the idea is that:
--   (1) if (prime) p divides a product of primes then it divides a term in that product (euclid for list)
--   (2) if the term in (1) is a prime, then p equals that term
--   (3) if the terms are sorted, then p must be no larger than the first term
lemma plist_lte
  {p q : ℕ} 
  {t : list ℕ}
  (hp : irreducible p)
  (hq : irreducible q)
  (hd : p ∣ product (q :: t))
  (hl : plist t  = tt ∧ sorted (q :: t) = tt)
: p ≤ q :=
begin
  have pn1 : p ≠ 1, from hp.right.left,
  revert q, induction t with q' t' ih,
  { intro q, intro hq, intro hd, intro hl,
    simp [product] at hd, simp [irreducible] at hp,
    have : p = 1 ∨ p = q, from hq.right.right p hd,
    cases this,
    { contradiction },
    { exact nat.le_of_eq a }
  },
  { intro q, intro hq, intro hd, intro hl,
    have hd : p ∣ q * (q' * product t'), by simp [nat.mul_comm]; simp [product] at hd; exact hd,
    have hpp : prime p, by simp [euclid] at hp; exact hp,
    have : p ∣ q ∨ p ∣ q' * product t', by exact hpp.right.right q (q' * product t') hd,
    cases this,
    { have : p = 1 ∨ p = q, from hq.right.right p a,
      cases this,
      { contradiction },
      { exact nat.le_of_eq a_1 }
    },
    { have hqq' : q' ≤ q, from list.lmax_head hl.right,
      have hiq' : irreducible q', by simp [plist, computable_irreducible] at hl; exact of_to_bool_true hl.right.left,
      have hd' : p ∣ product (q' :: t'), by simp [product]; exact a,
      have hl' : plist t' = tt ∧ sorted (q' :: t') = tt,
      begin
        apply and.intro,
        { simp [plist] at hl, exact hl.left },
        { rw [sorted] at hl, simp at hl, exact hl.right.left }
      end,
      have : p ≤ q', from ih hiq' hd' hl',
      exact nat.le_trans this hqq'
    }
  }
end

theorem prime_uniqueness (n : ℕ) : n ≠ 0 → ∃! l : list ℕ,
  plist l = tt ∧ sorted l = tt ∧ product l = n :=
begin
intro hn,
have : ∃ l : list ℕ, plist l ∧ product l = n, from prime_factorization n hn,
apply exists.elim this, intro l, intro hl, 
apply exists_unique.intro (list.insertion_sort l),
{ have : l ~ list.insertion_sort l, by symmetry; exact list.perm_insertion_sort l,
  apply and.intro,
  { exact list.perm_plist this hl.left },
  { apply and.intro,
    { exact list.sorted_insertion_sort l },
    { symmetry, rw [←hl.right], apply list.perm_product this }
  }
},
{
  revert l, induction n using nat.case_strong_induction_on with n ih,
  {
    contradiction
  },
  { simp at ih, intro l, intro hl, intro sl', intro hsl',

    -- seem to need to state these up-front so they get picked up when we move to cases later
    have hslprod : product (list.insertion_sort l) = product l,
      by apply list.perm_product; exact list.perm_insertion_sort l,
    have hslplist : plist (list.insertion_sort l) = tt,
    begin
      have : l ~ list.insertion_sort l, by symmetry; exact list.perm_insertion_sort l,
      exact list.perm_plist this hl.left
    end,
    have hslsorted : sorted (list.insertion_sort l) = tt, from list.sorted_insertion_sort l,

    cases (list.insertion_sort l) with p t,
    { simp [product] at hslprod, rw [←hslprod] at hl, rw [←hl.right] at hsl',
      exact list.plist_prod_one hsl'.left hsl'.right.right
    },
    { cases sl' with q t',
      { simp [product] at hsl', rw [←hsl'.right.right] at hl, rw [hl.right] at hslprod,
        exact eq.symm (list.plist_prod_one hslplist hslprod)
      },
      { have hiq : irreducible q, by simp [plist, computable_irreducible] at hsl'; exact of_to_bool_true hsl'.right.right.left,
        have hip : irreducible p, by simp [plist, computable_irreducible] at hslplist; exact of_to_bool_true hslplist.right,

        have hqd : q ∣ product (p :: t),
        begin
          have : product (q :: t') = nat.succ n, from hsl'.right.right,
          simp [product] at this,
          simp [hl.right] at hslprod, rw [hslprod],
          exact dvd.intro (product t') this
        end,
        have hpd : p ∣ product (q :: t'),
        begin
          simp [product,hl.right] at hslprod,
          rw [hsl'.right.right,←hslprod],
          exact dvd.intro (product t) (eq.refl (p * product t))
        end,

        have hpt : plist t = tt ∧ sorted (p :: t) = tt,
        begin
          apply and.intro,
          { simp [plist] at hslplist, exact hslplist.left },
          { exact hslsorted }
        end,
        have hqt' : plist t' = tt ∧ sorted (q :: t') = tt,
        begin
          apply and.intro,
          { simp [plist] at hsl', exact hsl'.left },
          { exact hsl'.right.left }
        end,

        have hplq: p ≤ q, from plist_lte hip hiq hpd hqt',
        have hqlp : q ≤ p, from plist_lte hiq hip hqd hpt,
        have hpq: p = q, from le_antisymm hplq hqlp,

        have : q * product t' = nat.succ n, by simp [product] at hsl'; exact hsl'.right.right,
        have ht' : product t' = nat.succ n / q, 
          from eq.symm (nat.div_eq_of_eq_mul_right (nat.pos_of_ne_zero hiq.left) (eq.symm this)),

        have hprod : p * product t = nat.succ n, by simp [product] at hslprod; rw [hslprod]; exact hl.right,
        have ht : product t = nat.succ n / p, 
          from eq.symm (nat.div_eq_of_eq_mul_right (nat.pos_of_ne_zero hip.left) (eq.symm hprod)),

        let m := product t,
        have handt : plist t = tt ∧ product t = m, by {apply and.intro, exact hpt.left, simp},
        have hst : sorted t = tt, by simp [sorted] at hpt; exact hpt.right.left,
        have handt' : plist t' = tt ∧ sorted t' = tt ∧ product t' = m,
        begin
          apply and.intro,
          { exact hqt'.left },
          { apply and.intro, 
            { simp [sorted] at hsl', exact hsl'.left },
            { rw [ht',←hpq,←ht] }
          }
        end,
        have hmt : product t = m, by simp,
        have hmt': product t' = m, by rw [ht',←hpq,←ht],
        have hmnz : m ≠ 0, from list.plist_prod_nonzero handt.left,
        have hmltn : m ≤ n,
        begin
          suffices hmltn' : m < nat.succ n, from nat.le_of_lt_succ hmltn',
          rw [←hprod,←nat.one_mul m,hmt],
          have h1ltp : 1 < p,
          begin
            cases p with p,
            { have : q ≠ 0, from hiq.left, contradiction },
            { cases p with p,
              { have : q ≠ 1, from hiq.right.left, exact absurd (eq.symm hpq) this },
              { have : nat.succ p ≠ 0, from nat.succ_ne_zero p,
                have : 0 < nat.succ p, from nat.pos_of_ne_zero this,
                have : 1 + 0 < 1 + nat.succ p, from nat.add_lt_add_left this 1,
                simp [nat.one_add] at this, exact this
              }
            }
          end,
          have hmgt0: m > 0, from nat.pos_of_ne_zero hmnz,
          exact nat.mul_lt_mul_of_pos_right h1ltp hmgt0
        end,
        have hxl : ∃ (l : list ℕ), plist l ∧ product l = m, by existsi t; exact handt,
        have htt' : t = t',
        begin
          have : t' = list.insertion_sort t, from ih m hmltn hmnz hxl t handt t' handt',
          simp [list.idem_insertion_sort hst] at this, simp [this]
        end,
        rw [hpq, htt']
      }
    }
  }
}
end

end nt