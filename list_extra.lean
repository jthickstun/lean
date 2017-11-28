import .definitions
import .nat_extra
import .decidable_relations

namespace list

/-
Basic lemmas concerning products and prime lists
-/

lemma product_concat (l1 l2 : list ℕ) : product (l1 ++ l2) = (product l1) * (product l2) :=
begin
induction l1,
{ by simp [product] },
{ by simp [product, ih_1] }
end

lemma plist_concat (l1 l2 : list ℕ) : plist l1 = tt → plist l2 = tt → plist (l1 ++ l2) = tt :=
begin
induction l1,
{ intros, by simp [a_1] },
{ intros, simp [plist] at a_2, simp [plist], apply and.intro,
  { exact a_2.left },
  { exact ih_1 a_2.right a_3 }
}
end

lemma lmax_head {x y : ℕ} {t : list ℕ} (h : sorted (x :: y :: t) = tt) : y ≤ x := 
begin
  simp [sorted] at h,
  have : max x (lmax (y :: t)) = x, exact nat.eq_eq h.right.right,
  have hx : max y (lmax t) ≤ x, by rw [←this]; exact le_max_right x (lmax (y :: t)),
  have hy : y ≤ max y (lmax t), by simp [le_max_left],
  exact nat.le_trans hy hx
end

lemma plist_prod_nonzero {l : list ℕ} (h : plist l = tt) : product l ≠ 0 :=
begin
  induction l with p t ih,
  { simp [product] },
  { simp [product],
    have ht : plist t = tt, by simp [plist] at h; exact h.right,
    by_cases p = 0 with hp,
    { simp [plist, nt.computable_irreducible] at h, exact absurd hp h.left.left },
    { have hpg0 : product t ≠ 0, from ih ht,
      --this was incredibly annoying; any ideas how we could make this easier?
      have hp : nat.succ (nat.pred p) = p, from nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hp),
      have ht : nat.succ (nat.pred (product t)) = product t, from nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hpg0),
      have : p*(product t) = 1 + (nat.pred p) + (nat.pred (product t)) + (nat.pred p)*(nat.pred (product t)),
        by rw [←hp,←ht]; apply nat.foil,
      have : p*(product t) = nat.succ((nat.pred p) + (nat.pred (product t)) + (nat.pred p)*(nat.pred (product t))),
        by rw [←nat.one_add]; simp [this],
      rw [this], exact nat.succ_ne_zero ((nat.pred p) + (nat.pred (product t)) + (nat.pred p)*(nat.pred (product t)))
    }
  }
end

lemma plist_prod_one {l : list ℕ} (h : plist l = tt) : product l = 1 → l = [] :=
begin
  cases l with p t,
  { simp },
  { intro, simp [product] at a,
    have : p = 1, from (nat.unique_unit a).left,
    simp [plist, nt.computable_irreducible] at h,
    have : p ≠ 1, from h.left.right.left,
    contradiction
  }
end

/-
We'll need some machinery about permutations to talk about unique prime lists.
This stuff is ripped from mathlib.
-/

variable {α : Type}
open perm

@[refl] protected theorem perm.refl : ∀ (l : list α), l ~ l
| []      := perm.nil
| (x::xs) := skip x (perm.refl xs)

@[symm] protected theorem perm.symm {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
perm.rec_on p
  perm.nil
  (λ x l₁ l₂ p₁ r₁, skip x r₁)
  (λ x y l, swap y x l)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₂ r₁)

attribute [trans] perm.trans

/-
Interactions of permutations with our other list definitions
-/

lemma perm_product {l₁ l₂ : list ℕ} (h : l₁ ~ l₂) : product l₁ = product l₂ :=
begin
induction h,
{ simp },
{ simp [product,ih_1] },
{ simp [product] },
{ simp [ih_1,ih_2] }
end

lemma perm_lmax {l₁ l₂ : list ℕ} (h : l₁ ~ l₂) : lmax l₁ = lmax l₂ :=
begin
induction h,
{ simp },
{ simp [lmax,ih_1] },
{ simp [lmax,max_left_comm] },
{ simp [ih_1,ih_2] }
end

lemma perm_plist {l₁ l₂ : list ℕ} (h : l₁ ~ l₂) (hp : plist l₁ = tt) : plist l₂ = tt :=
begin
-- is there a way to clean up this induction re: term introduction?
-- check out perm_induction_on in perm.lean in mathlib?
induction h with x l₁ l₂ l₃ ih x y l l₁ l₂,
{ exact hp },
{ have : plist l₁ = tt, by simp [plist] at hp; exact hp.right,
  have hp2 : plist l₂ = tt, by simp [this] at ih; exact ih,
  have : nt.is_prime x = tt, by simp [plist] at hp; exact hp.left,
  simp [plist], exact and.intro this hp2
},
{ have hpx : nt.is_prime x = tt, by simp [plist] at hp; exact hp.left,
  have hpy : nt.is_prime y = tt, by simp [plist,plist] at hp; exact hp.right.left,
  have hpl : plist l = tt, by simp [plist, plist] at hp; exact hp.right.right,
  have hpyl : plist (y :: l) = tt, by simp [plist]; exact and.intro hpy hpl,
  simp [plist], exact and.intro hpx (and.intro hpy hpl)
},
{ apply ih_2, apply ih_1, assumption }
end

/-
We need to prove the existence of sorted lists. To do this, we introduce a
sorting algorithm and show that it spits out a sorted permutation.
-/

lemma perm_ordered_insert (x : ℕ) (l : list ℕ) : ordered_insert x l ~ x :: l :=
begin
induction l with y l ih,
{ simp [ordered_insert] },
{ by_cases y ≤ x with h,
  { simp [ordered_insert, h] },
  { simp [ordered_insert, h],
    have hxy : y :: x :: l ~ x :: y :: l, by simp [perm.swap],
    suffices : y :: ordered_insert x l ~ y :: x :: l,
    { transitivity, apply this, apply hxy },
    { apply perm.skip, simp [ih] }
  }
}
end

lemma perm_insertion_sort (l : list ℕ) : insertion_sort l ~ l :=
begin
induction l with y l ih,
{ simp [insertion_sort] },
{ simp [insertion_sort],
  have h : ordered_insert y (insertion_sort l) ~ y :: insertion_sort l,
    by apply perm_ordered_insert,
  transitivity, assumption, apply perm.skip, apply ih
}
end

lemma sorted_singleton (x : ℕ) : sorted [x] = tt :=
begin
  simp [sorted, lmax, max],
  by_cases x ≤ 0,
  { simp [nat.eq_zero_of_le_zero h, nat.eq] },
  { simp [h, nat.eq] }
end

lemma sorted_head (x : ℕ) (l : list ℕ) 
  : sorted (x :: l) = tt ↔ lmax l ≤ x ∧ sorted l = tt :=
begin
split,
{ intro h, simp [sorted] at h,
  have hx : max x (lmax l) = x, from nat.eq_eq h.right,
  split,
  { rw [←hx], simp [le_max_right] },
  { exact h.left }
},
{ intro h, simp [sorted],
  have : max x (lmax l) = x, by simp [max_eq_left h.left],
  apply and.intro,
  { exact h.right },
  { exact nat.eq_of_eq this }
}  
end

lemma sorted_ordered_insert {x : ℕ} {l : list ℕ}
 : sorted l = tt → sorted (ordered_insert x l) = tt :=
begin
intro h, induction l with y l ih,
{ simp [sorted_singleton] },
{ by_cases y ≤ x with hxy,
  { simp [hxy], simp [sorted],
    apply and.intro,
    { simp [sorted] at h, exact h.left },
    { simp [sorted] at h, apply and.intro,
      { exact h.right },
      { have : lmax (y :: l) ≤ x,
        begin
          simp [lmax],
          have : max y (lmax l) = y, from nat.eq_eq h.right,
          rw [←this] at hxy, exact hxy
        end,
        have : max x (lmax (y :: l)) = x, from max_eq_left this,
        exact nat.eq_of_eq this
      }
    }
  },
  { have : x ≤ y ∨ y ≤ x, from le_total x y,
    have hyx : x ≤ y, by simp [hxy] at this; assumption,
    have hyl : lmax l ≤ y, by simp [sorted_head] at h; exact h.right,
    have : ordered_insert x l ~ x :: l, by simp [perm_ordered_insert],
    have hyxl : lmax (ordered_insert x l) ≤ y, by 
      simp [perm_lmax this, lmax]; simp [max_le hyx hyl],

    have : sorted l = tt, by simp [sorted] at h; exact h.left,
    have hxl : sorted (ordered_insert x l) = tt, from ih this,
    
    simp [hxy,sorted_head], apply and.intro,
    { exact hxl },
    { exact hyxl }
  }
}
end

lemma sorted_insertion_sort (l : list ℕ) : (sorted $ insertion_sort l) = tt :=
begin
induction l with x l ih,
{ simp [insertion_sort, sorted] },
{ simp [sorted_ordered_insert ih] }
end

/-
Sorting a sorted list is idempotent: idem_insertion_sort. 

We conceptually might want the following lemma:

lemma perm_sorted {l₁ l₂ : list ℕ} (h : l₁ ~ l₂) (hs1 : sorted l₁) (hs2 : sorted l₂) : l₁ = l₂

But this seems very hard to prove given our definition of perm_sorted. So
instead we'll get the needed result from less general principles.
-/

lemma idem_insertion_sort {l : list ℕ} (h : sorted l = tt) : insertion_sort l = l :=
--perm_sorted (perm_insertion_sort l) (sorted_insertion_sort l) h
begin
induction l with x t ih,
{ simp },
{ have : sorted t = tt, by simp [sorted] at h; exact h.left,
  simp [insertion_sort], rw [ih this],
  induction t, { simp }, { simp [ordered_insert, list.lmax_head h] }
}
end

end list