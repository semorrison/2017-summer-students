import Louis.euclidean_domain

-- notation for has_well_founded.r?
notation  a < b := has_well_founded.r a b
notation a > b := has_well_founded.r b a

#check (5/3)

noncomputable instance ed_has_sizeof {α : Type} [ed:decidable_euclidean_domain α] : has_sizeof α := {
    sizeof := λ x, ed.valuation.out.val x, -- note that out uses choice
}

-- noncomputable instance ed_has_well_founded {α : Type} [ed: decidable_euclidean_domain α] : has_sizeof α := {
--     r := λ x y, 
--     wf :=
-- }




/- lemmas -/
@[simp] lemma mod_zero {α : Type} [ed : euclidean_domain α] (a : α)  : a % 0 = a :=
begin
    have := ed.witness,
    have := this a 0,
    simp at this,
    exact this,
end

#check integral_domain.to_no_zero_divisors
#check no_zero_divisors -- (eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)
#check zero_div
#check dvd_zero

@[simp] lemma zero_div_ed {α : Type} [ed : euclidean_domain α] (b : α) : 0 / b = 0 :=
begin
    have := ed.witness,
    have := this 0 b,
    admit,
end

@[simp] lemma zero_mod {α : Type} [ed : euclidean_domain α] (b : α) : 0 % b = 0 :=
begin -- TODO: shorten/tidy this
    have := ed.witness,
    have h1 := this 0 b,
    have := zero_div_ed b,
    simp [has_div.div] at this,
    rw [this] at h1,
    have h2 : 0 * b = 0, by ring,
    rw [h2] at h1,
    simp at h1,
    exact h1,
end

-- lemma eq_zero_or_pos {α : Type} [ed:decidable_euclidean_domain α] (n : α) : n = 0 ∨ n > (0 : α) :=
-- begin
-- cases decidable.em (n=0),
-- left, exact h,
-- right, simp, unfold has_well_founded.r,
-- unfold sizeof_measure,
-- unfold sizeof,
-- unfold has_sizeof.sizeof,
-- unfold measure,
-- unfold inv_image,
-- have := ed.valuation.out.property 0 n,
-- cases this,
-- {
--     contradiction
-- },
-- {
    
--     admit,
-- }
-- end

-- #reduce (0%5)

-- lemma mod_eq_sub_mod {a b : nat} (h : a ≥ b) : a % b = (a - b) % b :=
-- or.elim (eq_zero_or_pos b)
--   (λb0, by rw [b0, nat.sub_zero])
--   (λh₂, by rw [mod_def, if_pos (and.intro h₂ h)])

-- @[simp] theorem mod_self (n : nat) : n % n = 0 :=
-- by rw [mod_eq_sub_mod (le_refl _), nat.sub_self, zero_mod]




noncomputable def gcd {α : Type} [ed : decidable_euclidean_domain α] : α → α → α
| x y := if x_zero : x = 0 then y
else have (y % x) < x, by {
    unfold has_well_founded.r,
    unfold sizeof_measure,
    unfold sizeof,
    unfold has_sizeof.sizeof,
    unfold measure,
    unfold inv_image,
    have := ed.valuation.out.property y x,
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

@[simp] theorem gcd_self {α : Type} [decidable_euclidean_domain α] (n : α) : gcd n n = n :=
by cases n;
 simp [gcd, mod_self]

