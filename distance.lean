/-
Some useful facts about distances 
(this helps us avoid reasoning about negative numbers)
-/

def dist : ℕ → ℕ → ℕ
| 0     m     := m
| n     0     := n
| (n+1) (m+1) := dist n m

lemma dist_rfl (n : ℕ) : dist n n = 0 :=
begin
induction n with n ih,
{ reflexivity },
{ simp [dist, ih] }
end

lemma dist_zero_left (m : ℕ) : dist 0 m = m := by cases m; reflexivity
lemma dist_zero_right (n : ℕ) : dist n 0 = n := by cases n; reflexivity

lemma dist_add (n m : ℕ) : dist n (n+m) = m :=
begin induction n with n ih,
  { by simp [dist_zero_left] },
  { from calc dist (nat.succ n) (nat.succ n + m) 
            = dist (nat.succ n) (nat.succ (n + m)) : by simp
        ... = dist n (n + m)                       : by simp [dist]
        ... = m                                    : ih
  }
end

lemma add_dist (n m : ℕ) : dist (n+m) n = m :=
begin induction n with n ih,
  { by simp [dist_zero_right] },
  { from calc dist (nat.succ n + m) (nat.succ n) 
            = dist (nat.succ (n + m)) (nat.succ n) : by simp
        ... = dist (n + m) n                       : by simp [dist]
        ... = m                                    : ih
  }
end

lemma dist_sum (n m k : ℕ) (h : n = m + k) : dist n m = k :=
by rw [h]; simp [add_dist]

lemma dist_iden (m n : ℕ) : dist m n = 0 ↔ m = n :=
iff.intro
(begin
revert n, induction m with m ih,
{ intro n, simp [dist_zero_left]; from eq.symm },
{ intro n, cases n with n,
  { simp [dist]; intro; assumption },
  { simp [dist]; intro h; rw [(ih n) h] } } 
end)
(by intro h; simp [h, dist_rfl] )

lemma dist_symm (m n : ℕ) : dist m n = dist n m :=
begin
revert n, induction m with m ih,
{ intro n; induction n; reflexivity },
{ intro n, cases n with n,
  { simp [dist_zero_left, dist_zero_right] },
  { simp [dist, ih n] } }
end

lemma dist_cancel (n m k : ℕ) : dist (n+k) (m+k) = dist n m :=
begin revert n m, induction k with k ih,
{ intros, simp },
{ intros, apply ih }
end

lemma dist_mul (n m k : ℕ) : dist (n*k) (m*k) = (dist n m)*k :=
begin
revert n, induction m with m ih,
{ intro n; simp [dist_zero_right] },
{ intro n; cases n with n,
  { simp [dist_zero_left] },
  { simp [dist, nat.succ_mul]; 
    repeat { rw [nat.add_comm k] }; 
    rw [dist_cancel]; 
    repeat { rw [nat.mul_comm k] }; 
    apply ih
  }
}
end

lemma bounded_dist {n m k : ℕ} (hn : n < k) (hm : m < k) : dist n m < k :=
begin
revert n m, induction k with k ih,
{ intros, from absurd (nat.eq_zero_of_le_zero hn) (nat.succ_ne_zero n) },
{ intros, cases n with n,
  { cases m with m; simp [dist]; assumption },
  { cases m with m,
    { simp [dist]; assumption },
    { simp [dist];
      have hnk : n < k, from nat.lt_of_succ_lt_succ hn,
      have hmk : m < k, from nat.lt_of_succ_lt_succ hm,
      apply nat.lt.step; apply ih hnk hmk; assumption
    }
  }
}
end

lemma dist_sub {n m : ℕ} (hm : m ≤ n) : dist n (n - m) = m :=
calc dist n (n - m) = dist (n+m) ((n - m) + m) : by rw [dist_cancel]
                ... = dist (n+m) n             : by rw [nat.sub_add_cancel hm]
                ... = m                        : by rw [add_dist]

lemma dist_cancel_sub {n m k : ℕ} (hm : m ≤ n) (hk : k ≤ n) : dist (n - m) (n - k) = dist m k :=
calc dist (n - m) (n - k) = dist (n - m + m) ((n - k) + m) : by rw [dist_cancel]
                      ... = dist n (n - k + m)             : by rw [nat.sub_add_cancel hm]
                      ... = dist (n+k) (n - k + m + k)     : by rw [dist_cancel]
                      ... = dist (n+k) (n - k + (m + k))   : by rw [nat.add_assoc]
                      ... = dist (n+k) (n - k + (k + m))   : by rw [nat.add_comm k]
                      ... = dist (n+k) ((n - k + k) + m)   : by rw [nat.add_assoc]
                      ... = dist (n+k) (n+m)               : by rw [nat.sub_add_cancel hk]
                      ... = dist (k+n) (m+n)               : by rw [nat.add_comm k, nat.add_comm m]
                      ... = dist k m                       : by rw [dist_cancel]
                      ... = dist m k                       : by rw [dist_symm]