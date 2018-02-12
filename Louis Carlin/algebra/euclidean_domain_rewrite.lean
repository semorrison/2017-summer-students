--TODO
-- write induction principle :(
-- convert to well founded instead of ℕ
-- change to require only decidability for (x=0) (get rid of decidable_euclidean_domain entirely?)

import data.int.basic
import tactic.ring

universes u v

definition euclidean_valuation {α} [has_zero α] (r : α → α → α) := { f : α → ℕ // ∀ a b, b = 0 ∨ has_well_founded.r (f(r a b)) (f b)}

class euclidean_domain (α : Type) extends integral_domain α :=
( quotient : α → α → α )
( remainder : α → α → α )
( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a )
( valuation : euclidean_valuation remainder)

/- 
Wikipedia suggests defining a valuation with the property "For all nonzero a and b in α, f(a) ≤ f(ab)".
-/
def valuation' {α : Type} [ed : euclidean_domain α] : euclidean_valuation (ed.remainder) :=
{
    val := λ a, {n : nat | ∃ x, n = ed.valuation.val (x*a)},
    property := sorry,
}

def p : ℕ → Prop := λ n, n > 10

lemma ep : ∃ n : ℕ, p n :=
begin
existsi 14,
rw p,
exact dec_trivial,
end

#check well_founded.min

class decidable_euclidean_domain (α : Type) extends euclidean_domain α:=
(decidable_eq_zero : ∀ a : α, decidable (a = 0))


instance decidable_eq_zero {α : Type} [ed : decidable_euclidean_domain α] (a : α) : decidable (a = 0) :=
begin
    have := ed.decidable_eq_zero,
    exact this a,
end





instance euclidean_domain_has_div {α : Type} [euclidean_domain α] : has_div α := {
    div := euclidean_domain.quotient
}

instance euclidean_domain_has_mod {α : Type} [euclidean_domain α] : has_mod α := {
    mod := euclidean_domain.remainder
}


instance ed_has_sizeof {α : Type} [ed:decidable_euclidean_domain α] : has_sizeof α := {
    sizeof := λ x, ed.valuation.val x, -- note that out uses choice
}



-- instance ed_has_well_founded {α : Type} [ed: decidable_euclidean_domain α] : has_well_founded α := {
--     r := λ (x y : α), has_well_founded.r (ed.valuation.val x) (ed.valuation.val y),
--     wf := 
--         begin
--             split,
--             admit,
--         end
-- }


/- lemmas -/
@[simp] lemma mod_zero {α : Type} [ed : euclidean_domain α] (a : α)  : a % 0 = a :=
begin
    have := ed.witness,
    have := this a 0,
    simp at this,
    exact this,
end

def gcd {α : Type} [ed : decidable_euclidean_domain α] : α → α → α
| x y := if x_zero : x = 0 then y
else have has_well_founded.r (y % x) x, by {
    unfold has_well_founded.r,
    unfold sizeof_measure,
    unfold sizeof,
    unfold has_sizeof.sizeof,
    unfold measure,
    unfold inv_image,
    have := ed.valuation.property y x,
    cases this,
    {
        contradiction,
    },
    {
        exact this,
    }
},
        gcd (y%x) x


@[simp] theorem gcd_zero_left {α : Type} [decidable_euclidean_domain α] (x : α) : gcd 0 x = x := 
begin
    rw gcd,
    simp,
end


@[simp] theorem gcd_next {α : Type} [decidable_euclidean_domain α] (x y : α) (h : x ≠ 0) : gcd x y = gcd (y % x) x :=
begin
    rw gcd,
    simp [h],
end

@[simp] theorem gcd_one_left {α : Type} [decidable_euclidean_domain α] (n : α) : gcd 1 n = 1 := 
begin
rw [gcd],
simp,
rw [gcd],
simp, -- does n % 1 always equal 0?
sorry,
end

@[simp] theorem gcd_self {α : Type} [decidable_euclidean_domain α] (n : α) : gcd n n = n :=
by cases n;
 simp [gcd, mod_self]

