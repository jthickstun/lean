import .definitions
import .nat_extra
import .logic_extra

namespace nt

/-
I don't think we need this, but it's easy enough to prove. 
This establishes the connection between the two computable properties.
-/

lemma prime_dichotomy {n : ℕ} (h : n ≠ 0 ∧ n ≠ 1) : is_prime n = tt ↔ is_composite n = ff :=
begin
split; intro a,
{ by_cases (n = 0) with h0,
  { from absurd h0 h.left },
  { by_cases (n = 1) with h1,
    { from absurd h1 h.right },
    { simp [h0,h1,is_prime] at a,
      from (to_bool_iff (is_composite n = ff)).1 a
    }
  }
},
{ by_cases (n = 0) with h0,
  { from absurd h0 h.left },
  { by_cases (n = 1) with h1,
    { from absurd h1 h.right },
    { simp [h0,h1,is_prime], apply to_bool_tt, assumption }
  }
}
end

/-
Now establish the connection between the two conceptual properties.
-/

lemma not_composite {n : ℕ} (h : n ≠ 0 ∧ n ≠ 1) : ¬composite n ↔ irreducible n :=
begin
split; intro a,
{
  by_cases (n = 0) with h1,
  { exact absurd h1 h.left },
  { by_cases (n = 1) with h2,
    { exact absurd h2 h.right },
    { delta irreducible, apply and.intro, exact h1, apply and.intro, exact h2,
      { simp [h1, h2, composite] at a,
        have : ∀ x : ℕ, ¬∃ b : ℕ, (¬x = 1 ∧ ¬b = 1 ∧ n = x * b), from forall_not_of_not_exists a,
        assume k : ℕ, have hk : ¬∃ (b : ℕ), ¬k = 1 ∧ ¬b = 1 ∧ n = k * b, from this k,
        intro hkdn, apply dvd.elim hkdn, intro x, intro hnkx,
        by_contradiction, simp [demorgan] at a_1,
        have hx : x ≠ 1, from assume : x = 1,
          have hnk : k = n, by simp [this] at hnkx; exact eq.symm hnkx, 
          absurd hnk a_1.left,
        have : ¬k = 1 ∧ ¬x = 1 ∧ n = k*x, by
        begin
          apply and.intro, 
            exact a_1.right, 
            apply and.intro,
              exact hx,
              exact hnkx
        end,
        have : ∃ b : ℕ, ¬k = 1 ∧ ¬b = 1 ∧ n = k*b, by existsi x; exact this,
        contradiction
      },
    }
  }
},
{
  by_cases (n = 0) with h1,
  { exact absurd h1 h.left },
  { by_cases (n = 1) with h2,
    { exact absurd h2 h.right },
    { simp [h1, h2, irreducible] at a,
      simp [composite, h1], 
      by_contradiction,
      cases a_1 with k,
      cases a_1 with b h',
      have hkdiv : k ∣ n, from dvd.intro b (eq.symm h'.right.right),
      have hk1 : k ≠ 1, from h'.left,
      have hkn : k ≠ n, by
      begin
        by_cases (k = n) with hkeqn,
        { have : n = n*b, by rw [hkeqn] at h'; exact h'.right.right,
          have : n*1 = n*b, by simp; exact this,
          have : 1 = b, from nat.eq_of_mul_eq_mul_left (nat.pos_of_ne_zero h.left) this,
          from absurd (eq.symm this) h'.right.left
        },
        { assumption }
      end,
      have hn1 : k = n ∨ k = 1, from (a k) hkdiv,
      have hn1' : ¬(k = n ∨ k = 1), by simp [demorgan]; exact and.intro hkn hk1,
      contradiction
    }
  }
}
end

/-
Build-up to decidability of the 'composite' relation. First show that the
auxillary function for is_composite does the right thing. Then use that to
get the correctness of is_composite itself.
-/

lemma zero_is_zero (n : ℕ) : zero_test n = tt ↔ n = 0 :=
begin
  split; intros;
  by_cases (n = 0);
  simp [zero_test, *],
  delta zero_test at a,
  simp * at *
end

lemma composite_aux_lem {n m : ℕ} 
  (h : is_composite_aux n m = tt)
  (hm : m < n) :
  ∃ a : ℕ, ∃ b : ℕ, a ≠ 1 ∧ b ≠ 1 ∧ n = a*b :=
begin
  cases m with m,
  { contradiction },
  { induction m with m ih_1,
    { contradiction },
    { simp [is_composite_aux] at h,
      cases h with hc hz,
      { apply ih_1, 
        { assumption },
        { from nat.lt_of_succ_lt hm }
      },
      { simp [zero_is_zero] at hz,
        let a := nat.succ (nat.succ m),
        let b := n/a,
        have hmod : n%a + a*(n/a) = n, from nat.mod_add_div n a,
        have hdiv : a*b = n, by simp [hz,hmod,*] at *,
        have ha : a ≠ 1, from
          assume ha1 : a = 1,
          have hlz : nat.succ m ≤ 0, by simp [nat.succ_inj ha1],
          by simp [nat.not_succ_le_zero] at hlz; contradiction,
        have hb : b ≠ 1, from
          assume hb1 : b = 1,
          have han : a = n, by simp [hb1,nat.mul_one] at hdiv; assumption,
          have haln : a ≠ n, by simp [hm,nat.lt_imp_ne],
          by contradiction,
        existsi a, existsi b, apply and.intro ha,
          { apply and.intro hb, simp [hdiv] }
      }
    }
  }
end

lemma composite_aux_lem2 {a b n : ℕ} 
  (ha : a ≠ 1)
  (hb : b ≠ 1)
  (hn : a*b = (nat.succ n)) :
  is_composite_aux (nat.succ n) a = tt :=
begin
  cases a with a,
  { simp [is_composite_aux], simp at hn, contradiction },
  { cases a with a,
    { contradiction },
    { simp [is_composite_aux], 
      apply or.intro_right,
      simp [zero_is_zero],
      rw [←hn],
      apply nat.mul_mod_right,
    }
  }
end

lemma composite_aux_lem3 {a m n : ℕ}
  (ha : a ≤ m) 
  (hcomp : is_composite_aux n a = tt) :
  is_composite_aux n m = tt :=
begin
  induction m with m ih,
  { simp [nat.eq_zero_of_le_zero ha, is_composite_aux] at hcomp, contradiction },
  { by_cases (a = nat.succ m),
    { rw [←h], assumption },
    { simp [nat.le_ne_succ ha h] at ih,
      cases m with m,
      { simp [is_composite_aux] at ih, contradiction },
      { simp [is_composite_aux], apply or.intro_left, assumption }
    }
  }
end

lemma computable_composite {n : ℕ} : is_composite n = tt ↔ composite n :=
begin
split; intro h,
{ apply and.intro,
  { assume hnz : n = 0, simp [hnz, is_composite] at h, contradiction },
  { cases n with n,
    { contradiction },
    { simp [is_composite] at h,
      cases n with n,
      { contradiction },
      { from composite_aux_lem h nat.lt_succ }
    }
  }
},
{ delta composite at h,
  cases h.right with a ha,
  cases ha with b hab,
  have hnp : n ≠ 0, from h.left,
  cases n with n,
  { contradiction },
  { simp [is_composite],
    have hc : is_composite_aux (nat.succ n) a = tt, from
      composite_aux_lem2 hab.left hab.right.left (eq.symm hab.right.right),
    have : a*b ≠ 0, from hab.right.right ▸ hnp,
    have hnz : a ≠ 0 ∧ b ≠ 0, from nat.no_zero_divisors this,
    have : a = (nat.succ n)/b, from
      eq.symm (nat.div_eq_of_eq_mul_left 
                (nat.pos_of_ne_zero hnz.right)
                hab.right.right),
    have haltn : a ≤ (nat.succ n), by simp [nat.div_le_self, this],
    have : a ≠ nat.succ n, from 
      assume han : a = nat.succ n,
      have h' : (nat.succ n)*1 = (nat.succ n)*b, from calc
                (nat.succ n)*1 = nat.succ n      : nat.mul_one $ nat.succ n
                           ... = a * b           : by simp [hab.right.right]
                           ... = (nat.succ n)*b  : by rw [han],
      have b = 1, by rw [han] at hnz; 
                     simp [nat.eq_of_mul_eq_mul_left (nat.pos_of_ne_zero hnz.left) h'],
      absurd this hab.right.left,
    have ha : a ≤ n, from nat.le_ne_succ haltn this,
    exact composite_aux_lem3 ha hc
  }
}
end

/-
Decidability of 'irreducible' is almost a layup once we have
  (1) the connection between composite and irreducible, i.e. 'not_composite'
  (2) the decidability of composite, i.e. 'computable_composite'
-/

lemma computable_irreducible {n : ℕ} : is_prime n = tt ↔ irreducible n :=
begin
split; intro a,
{
  by_cases (n = 0) with h,
  { simp [h, is_prime] at a, contradiction },
  { by_cases (n = 1) with h1,
    { simp [h1, is_prime] at a, contradiction },
    { simp [h, h1, is_prime] at a,
      -- why was this so hard? (manual application of to_bool_iff)
      have hnic : ¬is_composite n = tt, by simp; exact (to_bool_iff (is_composite n = ff)).1 a,
      have hnc : ¬composite n, from mt (iff.elim_right computable_composite) hnic,
      exact (iff.elim_left (not_composite $ and.intro h h1)) hnc
    }
  }
},
{
  by_cases (n = 0) with h,
  { simp [h, irreducible] at a, contradiction },
  { by_cases (n = 1) with h1,
    { simp [h1, irreducible] at a, contradiction },
    {
      have hnc : ¬composite n, from (iff.elim_right (not_composite $ and.intro h h1)) a,
      have hnic : ¬is_composite n = tt, from mt (iff.elim_left computable_composite) hnc,
      -- why was this so hard? (manual application of to_bool_tt)
      simp [h, h1, is_prime], apply to_bool_tt, simp at hnic, assumption
    }
  }
}
end

end nt