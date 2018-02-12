

-- def wf_measure {α : Sort u} {β : Sort u} [has_well_founded β] : (α → β) → α → α → Prop :=
-- inv_image has_well_founded.r

-- def wf_measure_wf {α : Sort u} {β : Sort u} [ hwf : has_well_founded β] (f : α → β) : well_founded (wf_measure f) :=
-- inv_image.wf f hwf.wf


-- class has_towf (α : Sort u) (β : Sort u) [ hwf : has_well_founded β]:=
-- (towf : α → β)


-- def wf_sizeof_measure (α : Sort u) {β : Sort u} [has_well_founded β] [has_towf α β] : α → α → Prop :=
-- wf_measure has_towf.towf

-- def wf_sizeof_measure_wf (α : Sort u) {β : Sort u} [has_well_founded β] [sizeof : α → β] : well_founded (wf_sizeof_measure α ) :=
-- wf_measure_wf sizeof

-- instance has_well_founded_of_has_sizeof (α : Sort u) [has_sizeof α] : has_well_founded α :=
-- {r := sizeof_measure α, wf := sizeof_measure_wf α}












-- @[simp] lemma zero_div_ed {α : Type} [ed : euclidean_domain α] (b : α) : 0 / b = 0 :=
-- begin
--     have := ed.witness,
--     have := this 0 b,
--     admit,
-- end

-- @[simp] lemma zero_mod {α : Type} [ed : euclidean_domain α] (b : α) : 0 % b = 0 :=
-- begin -- TODO: shorten/tidy this
--     have := ed.witness,
--     have h1 := this 0 b,
--     have := zero_div_ed b,
--     simp [has_div.div] at this,
--     rw [this] at h1,
--     have h2 : 0 * b = 0, by ring,
--     rw [h2] at h1,
--     simp at h1,
--     exact h1,
-- end

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