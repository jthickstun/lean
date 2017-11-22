import .definitions

namespace list

/-
We're going to need a lot more stuff about lists to prove FTA.
But for now we just need these (to prove existence).
-/

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

end list