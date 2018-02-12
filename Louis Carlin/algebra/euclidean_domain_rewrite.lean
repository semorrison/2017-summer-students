--TODO
-- write induction principle :(
-- convert to well founded instead of ℕ
-- change to require only decidability for (x=0) (get rid of decidable_euclidean_domain entirely?)

import data.int.basic
import tactic.ring

universes u v

def lt_wf : (well_founded nat.lt) := -- will need to be replaced by more general well_founded
    begin
      split, intro a, induction a with b h,
      {
          split,
          intro y,
          intro h,
          cases h,
      },
      {
        split,
        intro y,
        intro h,
        cases h,
        {
            assumption
        },
        {
            have p : y < b, by sorry,
            cases h,
            exact h_h y p,
        }
      }
    end



definition euclidean_valuation {α} [has_zero α] (r : α → α → α) := { f : α → ℕ // ∀ a b, b = 0 ∨ has_well_founded.r (f(r a b)) (f b)}

class euclidean_domain (α : Type) extends integral_domain α :=
( quotient : α → α → α )
( remainder : α → α → α )
( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a )
( valuation : euclidean_valuation remainder)



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



/- 
Wikipedia suggests defining a valuation with the property "For all nonzero a and b in α, f(a) ≤ f(ab)".
-/
noncomputable def valuation' {α : Type} [ed : decidable_euclidean_domain α] : euclidean_valuation (ed.remainder) := 
{ -- you could maybe get around this requiring decidable_euclidean_domain by using em since this is already non-computable
    val := λ a, if a = 0 then 0 else well_founded.min lt_wf {n : nat | ∃ x, x ≠ 0 ∧ n = ed.valuation.val (x*a)} 
    begin
        have fin :ed.valuation.val (1*a) ∈ {n : nat | ∃ x, x ≠ 0 ∧ n = ed.valuation.val (x*a)},
        simp,
        existsi (1:α),
        split,
        exact one_ne_zero,
        simp,
        exact set.ne_empty_of_mem fin,
    end,
    property :=
    begin
        intros,
        cases decidable.em (b=0),
        left, exact h,
        right,
        simp [h],
        cases decidable.em (euclidean_domain.remainder a b = 0),
        simp [h_1],
        sorry,
        sorry,
    end,
}

lemma valuation'_property_2 {α : Type} [ed : decidable_euclidean_domain α] : ∀ a b : α, a = 0 ∨ b = 0 ∨ has_well_founded.r (valuation'.val a) (valuation'.val (a*b)) :=
sorry


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

@[simp] lemma mod_zero {α : Type} [ed : euclidean_domain α] (a : α)  : a % 0 = a :=
begin
    have := ed.witness,
    have := this a 0,
    simp at this,
    exact this,
end

lemma valuation'_lt_one {α : Type} [ed : decidable_euclidean_domain α] (x : α) : 
has_well_founded.r (valuation'.val x) (valuation'.val (1:α)) → x = 0 :=
begin
    intro,
    have := valuation'_property_2 x 1,
    cases this, exact this,
    cases this, have := one_ne_zero, contradiction,
    simp at this, sorry -- wf contradiction
end

@[simp] lemma mod_one {α : Type} [decidable_euclidean_domain α] (x : α) : x % 1 = 0 :=
begin
    have := valuation'.property x 1,
    cases this, have := one_ne_zero, contradiction,
    exact valuation'_lt_one (x % 1) this,
end 

@[simp] lemma zero_mod  {α : Type} [ed : decidable_euclidean_domain α] (b : α) : 0 % b = 0 :=
begin
    have := ed.witness,
    have h1:= this 0 b,
    have h2 : euclidean_domain.remainder 0 b = b * (-euclidean_domain.quotient 0 b ), from sorry,
    have := valuation'_property_2 b (-euclidean_domain.quotient 0 b),
    cases this,
    {
        rw this_1, exact mod_zero (0:α)
    },
    {
        cases this_1, 
        {
            simp at this_1, rw this_1 at h1, simp at h1,
            dsimp [(%)], 
            exact h1
        },
        {
            have := valuation'.property 0 b,
            rw ←h2 at this_1,
            cases this,
            rw this_2, exact mod_zero (0:α),
            sorry -- contradiction between this_1 and this_2
        }
    }
end

@[simp] lemma zero_div' {α : Type} [ed : decidable_euclidean_domain α] (b : α) : b = 0 ∨ 0 / b = 0 :=
begin
    have := ed.witness,
    have := this 0 b,
    have h1 := zero_mod b, dsimp [(%)] at h1,
    rw h1 at this,
    simp at this,
    dsimp [(/)],
    cases decidable.em (b=0),
    left, exact h,
    right,
    have := eq_zero_or_eq_zero_of_mul_eq_zero this,
    cases this,
    exact this_1,
    contradiction,
end

#check no_zero_divisors

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

