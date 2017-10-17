namespace group_theory

universe u

--
-- Definitions and basic properties
--

class Magma (α : Type u) :=
(mul : α → α → α)
infix * := Magma.mul

class Group (α : Type u) extends Magma α :=
(associativity : ∀ a b c : α, a * (b * c) = (a * b) * c)
(e : α)
(left_identity : ∀ g : α, e * g = g)
(inv : α → α)
(left_inverse : ∀ g : α, (inv g) * g = e)
postfix ⁻¹ := Group.inv

variables {α : Type u}

example [G : Group α] : ∀ g : α, G.e * g = g := Group.left_identity
example [G : Group α] : ∀ g : α, g = G.e * g := 
assume g : α, eq.symm (Group.left_identity g)

lemma expansion [G : Group α] : ∀ g h : α, h = (g⁻¹*g)*h :=
assume g h : α,
have inv : G.e = g⁻¹*g, from eq.symm (Group.left_inverse g),
have h = G.e*h, from eq.symm (Group.left_identity h),
inv ▸ this

lemma idempotence [G : Group α] : ∀ g : α, g = g*g → g = G.e := 
assume g : α, assume hg: g = g*g,
calc g = (g⁻¹*g)*g  : expansion g g
 ...   = g⁻¹*(g*g)  : eq.symm (Group.associativity g⁻¹ g g)
 ...   = g⁻¹*g      : hg ▸ (eq.refl (g⁻¹*g)) --by simp [(eq.symm hg)]
 ...   = G.e        : Group.left_inverse g

lemma Group.right_inverse [G : Group α] : ∀ g : α, g*g⁻¹ = G.e :=
assume g : α,
have (g*g⁻¹)*(g*g⁻¹) = g*g⁻¹, from
calc (g*g⁻¹)*(g*g⁻¹) = g*(g⁻¹*g)*g⁻¹ : by simp [Group.associativity]
 ...                 = g*G.e*g⁻¹     : by simp [Group.left_inverse]
 ...                 = g*(G.e*g⁻¹)   : by simp [Group.associativity]
 ...                 = g*g⁻¹         : by simp [Group.left_identity],
idempotence (g*g⁻¹) (eq.symm this)

lemma Group.right_identity [G : Group α] : ∀ g : α, g * G.e = g :=
assume g : α,
have g = g*G.e, from
calc g = G.e*g      : eq.symm (Group.left_identity g)
 ...   = (g*g⁻¹)*g  : by simp [Group.right_inverse]
 ...   = g*(g⁻¹*g)  : eq.symm (Group.associativity g g⁻¹ g)
 ...   = g*G.e      : by simp [Group.left_inverse],
eq.symm this

lemma unique_identity [G : Group α] : ∀ g : α, (∀ h : α, g*h = h) → g = G.e :=
assume g : α, assume H : ∀ h , g*h = h, idempotence g (eq.symm (H g))

lemma unique_inverses [G : Group α] : ∀ g h : α, g*h = G.e → h = g⁻¹ :=
assume g h : α, assume H: g*h = G.e,
calc h = G.e*h      : eq.symm (Group.left_identity h)
 ...   = (g⁻¹*g)*h  : by simp [Group.left_inverse]
 ...   = g⁻¹*(g*h)  : eq.symm (Group.associativity g⁻¹ g h)
 ...   = g⁻¹*G.e    : by simp [H]
 ...   = g⁻¹        : Group.right_identity g⁻¹

lemma identity_involution [G : Group α] : G.e⁻¹ = G.e := 
calc G.e⁻¹ = G.e*G.e⁻¹ : eq.symm (Group.left_identity G.e⁻¹)
 ...       = G.e       : Group.right_inverse G.e

lemma inverse_product [G : Group α] (g h : α) : h⁻¹*g⁻¹ = (g*h)⁻¹ :=
have (g*h)*(h⁻¹*g⁻¹) = G.e, from
calc (g*h)*(h⁻¹*g⁻¹) = g*(h*h⁻¹)*g⁻¹ : by simp [Group.associativity]
 ...                 = g*G.e*g⁻¹     : by simp [Group.right_inverse]
 ...                 = g*g⁻¹         : by simp [Group.right_identity]
 ...                 = G.e           : Group.right_inverse g,
unique_inverses (g*h) (h⁻¹*g⁻¹) this

lemma inv_inv [G : Group α] (g : α) : g⁻¹⁻¹ = g :=
have g⁻¹*g = g*g⁻¹, by simp [Group.left_inverse, Group.right_inverse],
calc g⁻¹⁻¹ = (g⁻¹*g)*g⁻¹⁻¹  : expansion g g⁻¹⁻¹
 ...       = (g*g⁻¹)*g⁻¹⁻¹  : by simp [this]
 ...       = g*(g⁻¹*g⁻¹⁻¹)  : eq.symm (Group.associativity g g⁻¹ g⁻¹⁻¹)
 ...       = g*G.e          : by simp [Group.right_inverse]
 ...       = g              : Group.right_identity g

end group_theory