import .logic_extra

namespace nat

/-
Useful stuff that should possibly be in the standard library.
(Maybe some of this is already there and I overlooked it?)
-/

lemma lt_one_zero (n : ℕ) : n < 1 → n = 0 :=
assume h : n < 1,
have h1 : n+1 ≤ 0+1, from h,
nat.eq_zero_of_le_zero (le_of_add_le_add_right h1)

lemma lt_succ {n : ℕ} : n < nat.succ n :=
begin
induction n,
{ exact zero_lt_one },
{ simp [nat.succ_lt_succ,*] }
end

lemma le_ne_succ {m n : ℕ} 
  (hle : m ≤ nat.succ n) 
  (hne : m ≠ nat.succ n) :
  m ≤ n :=
have m = nat.succ n ∨ m < nat.succ n, from nat.eq_or_lt_of_le hle,
have m < nat.succ n, from or.resolve_left this hne,
nat.le_of_lt_succ this

lemma eq_or_less (n : ℕ) : n < 1 → n = 0 :=
assume h : n < 1,
have h1 : n+1 ≤ 0+1, from h,
nat.eq_zero_of_le_zero (le_of_add_le_add_right h1)

lemma lt_imp_ne {m n : ℕ} (h : m < n) : m ≠ n :=
assume h' : m = n, 
have hn : n < n, by simp [h'] at h; assumption,
have hlen : n ≤ n, by refl,
nat.lt_le_antisymm hn hlen

lemma m_dvd_mn {m n : ℕ} : m ∣ m*n :=
begin
  simp [has_dvd.dvd],
  existsi n, reflexivity
end

lemma no_zero_divisors {m n : ℕ} : m*n ≠ 0 → m ≠ 0 ∧ n ≠ 0 :=
assume hmn : m*n ≠ 0,
have (m = 0 ∨ n = 0) → m*n = 0, from
  assume h : m = 0 ∨ n = 0, or.elim h
    (assume hm : m = 0, (eq.symm hm) ▸ zero_mul n)
    (assume hn : n = 0, (eq.symm hn) ▸ mul_zero m),
have ¬(m = 0 ∨ n = 0), from (mt this) hmn,
(iff.elim_left (demorgan (m=0) (n=0))) this

end nat