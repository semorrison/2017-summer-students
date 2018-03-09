import Louis.euclidean_domain

example : integral_domain ℤ := by apply_instance




/- instances -/
instance int_euclidean_domain : decidable_euclidean_domain ℤ := {
    ((by apply_instance) : integral_domain ℤ) with 
    quotient := λ a b, a/b,
    remainder := λ a b, a%b,
    witness := 
    begin
        intros a b,
        rw [add_comm, mul_comm],
        exact int.mod_add_div a b,
    end,
    valuation :=
    begin
        split,
        tactic.swap,
        exact int.nat_abs,
        intros,
        cases decidable.em (b=0),
        {
            left, exact h,
        },
        {
            right,
            simp,
            sorry,
        }
    end,
    decidable_eq_zero := by apply_instance
}
#check nat.mod_add_div
#check int.mod_lt
#check int.nat_abs_abs

-- As is this definition isn't right. You could define this with a unit instead of one?
-- @[reducible] def coprime {α : Type} [ed: decidable_euclidean_domain α]  (a b : α) : Prop := gcd a b = 1

theorem gcd_rec {α} [decidable_euclidean_domain α] (m n : α) : m ≠ 0 → gcd m n = gcd (n % m) m :=
begin
    intro hm,
    rw gcd,
    simp [hm],
end

/- extended euclidean algorithm -/

def xgcd_aux {α} [decidable_euclidean_domain α] : α → α → α → α → α → α → α × α × α
| r s t r' s' t' := if r_zero : r = 0 then (r', s', t')
    else have has_well_founded.r (r' % r) r, from neq_zero_lt_mod_lt r' r r_zero,
    let q := r' / r in xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t

@[simp] theorem xgcd_zero_left {α} [decidable_euclidean_domain α] {s t r' s' t' : α} :
    xgcd_aux (0:α) s t r' s' t' = (r', s', t') :=
by rw xgcd_aux; simp

@[simp] theorem xgcd_aux_rec {α} [decidable_euclidean_domain α] {r s t r' s' t' : α} (h : r ≠ 0) : xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - (r' / r) * s) (t' - (r' / r) * t) r s t :=
begin
    rw xgcd_aux,
    simp [h],
end


/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd {α} [decidable_euclidean_domain α] (x y : α) : α × α := (xgcd_aux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a {α} [decidable_euclidean_domain α] (x y : α) : α := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b {α} [decidable_euclidean_domain α] (x y : α) : α := (xgcd x y).2

@[simp] theorem xgcd_aux_fst {α} [decidable_euclidean_domain α] (x y : α) :
    ∀ s t s' t', (xgcd_aux x s t y s' t').1 = gcd x y :=
gcd.induction x y
(begin
    intros,
    unfold xgcd_aux,
    simp,
end)
(λ x y h IH s t s' t',
begin
  unfold xgcd_aux,
  simp [h,IH],
  exact eq.symm (gcd_rec x y h)
end)

theorem xgcd_aux_val {α} [decidable_euclidean_domain α] (x y : α) : xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) :=
by rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1]; cases xgcd_aux x 1 0 y 0 1; refl

theorem xgcd_val {α} [decidable_euclidean_domain α] (x y : α) : xgcd x y = (gcd_a x y, gcd_b x y) :=
by unfold gcd_a gcd_b; cases xgcd x y; refl

-- private def P {α} [euclidean_domain α] (x y : α) : α × α × α × α × α → Prop
-- | (a,b,r, s, t) := r = a * s + b * t

-- theorem xgcd_aux_P  {α  [euclidean_domain α] (a b : α) {r r' } : ∀ {s t s' t'}, P (a,b,r, s, t) → P (a,b,r', s', t') → P (xgcd_aux r s t r' s' t') :=
-- gcd.induction r r' 
-- begin
-- intros,
-- simp,
-- exact a_2,
-- end
--  $ λ x y h IH s t s' t' p p', begin
--   rw [xgcd_aux_rec h], refine IH _ p, dsimp [P] at *, -- a % b = a - b * (a / b)
--   have mod_def : ∀ a b : α, a % b = a - b * (a / b), from sorry,
--   rw [mod_def], generalize : (y / x : α) = k,
--   rw [p, p'], simp [mul_add, mul_comm, mul_left_comm]
-- end

-- theorem gcd_eq_gcd_ab : (gcd a b : α) = a * gcd_a a b + b * gcd_b a b :=
-- by have := @xgcd_aux_P a b a b 1 0 0 1 (by simp [P]) (by simp [P]);
--    rwa [xgcd_aux_val, xgcd_val] at this
-- end


section
parameters (α : Type) [decidable_euclidean_domain α] (a b : α)

/- mathlib defines parameters for a and b at this point, maybe I should be doing that? -/
private def P : α × α × α → Prop | (r, s, t) := r = a * s + b * t

theorem xgcd_aux_P  {r r' : α} : ∀ {s t s' t'}, P (r, s, t) → P (r', s', t') → P (xgcd_aux r s t r' s' t') :=
gcd.induction r r'
begin
intros,
simp,
exact a_2,
end
( λ x y h IH s t s' t' p p', -- what is going on with this extra prop : Prop?
begin
rw [xgcd_aux_rec h],
refine IH  _  p,
dsimp [P] at *, -- a % b = a - b * (a / b)
  have mod_def : ∀ a b : α, a % b = a - b * (a / b), from sorry, -- why does this fail to mind has_sub?
  rw [mod_def], generalize : (y / x : α) = k,
  rw [p, p'], simp [mul_add, mul_comm, mul_left_comm]
end)

-- theorem xgcd_aux_P {r r'} : ∀ {s t s' t'}, P (r, s, t) → P (r', s', t') → P (xgcd_aux r s t r' s' t') :=
-- gcd.induction r r' (by simp) $ λ x y h IH s t s' t' p p', begin
--   rw [xgcd_aux_rec h], refine IH _ p, dsimp [P] at *,
--   rw [int.mod_def], generalize : (y / x : ℤ) = k,
--   rw [p, p'], simp [mul_add, mul_comm, mul_left_comm]
-- end


theorem gcd_eq_gcd_ab : (gcd a b : α)  = a * gcd_a a b + b * gcd_b a b :=
by have := @xgcd_aux_P a b a b 1 0 0 1 (by simp [P]) (by simp [P]);
   rwa [xgcd_aux_val, xgcd_val] at this
end

-- theorem gcd_eq_gcd_ab : (gcd a b : ℤ) = a * gcd_a a b + b * gcd_b a b :=
-- by have := @xgcd_aux_P a b a b 1 0 0 1 (by simp [P]) (by simp [P]);
--    rwa [xgcd_aux_val, xgcd_val] at this
-- end


--TODO
-- convert to well founded instead of ℕ
-- do I do well founded on the valuation or just the inputs?
-- Fix loads of unfolds
-- In general we don't have 0 % a = 0
-- Does the sizeof defintion issue hold everywhere?

-- Clean up:
-- indentation style?
-- is it better to get rid of haves wherever possible or do they make things more readable?


--definition euclidean_valuation' {α} [has_zero α] (r : α → α → α) := Σ W : Well_Ordered_Type, { f : α → W.β // ∀ a b, b = 0 ∨ @has_well_founded.r _ sorry (f(r a b)) (f b)}
-- probably easier to just use a structure at this point


-- class has_well_order (β : Type) :=
-- (ordering : β → β → Prop)
-- (iwo : is_well_order β ordering)


-- def measure' {α} {β} [hwo : has_well_order β] : (α → β) → α → α → Prop :=
-- inv_image (hwo.ordering)

-- def measure_wf' {α} {β} [hwo : has_well_order β] (f : α → β) : well_founded (measure'  f) :=
-- inv_image.wf f hwo.iwo.wf

-- def has_well_founded_of_has_wo {α : Sort u} {β} [hwo : has_well_order β] (f: α → β) : has_well_founded α :=
-- {r := measure' f, wf := measure_wf' f}


-- instance has_well_order_nat : has_well_order ℕ :=
-- {
--     ordering := (<), --nat.lt,
--     iwo := by apply_instance
-- }

-- instance ed_has_well_founded {α : Type} [ed: decidable_euclidean_domain α] : has_well_founded α :=
-- has_well_founded_of_has_wo ed.valuation.val

-- def lt_wf : well_founded (<) :=
-- begin
--     have : is_well_order ℕ (<), by apply_instance,
--     induction this,
--     exact this_wf, -- why can't lean work this out itself?
-- end

structure Well_Ordered_Type :=
(β : Type)
(lt : β → β → Prop)
(w : is_well_order β lt)   -- TODO can β be made implicit in the defintion of is_well_order in mathlib?

/-
 This is a counterexample to the claim that ∀ a, 0 % a = 0 in EDs.
 We have defined division such that 0 % 1 = -1 and defined a valuation  such that this is consistent with the ED definition
-/
instance weird_int_euclidean_domain : euclidean_domain ℤ :=
{
    quotient := λ a b, if a=0 then (if b=1 then 1 else a/b) else a/b,
    remainder := λ a b, if a = 0 then (if b=1 then -1 else a%b) else a%b,
    witness :=
    begin
    intros a b,
    cases decidable.em (a=0),
    {
        simp [h],
        cases decidable.em (b=1),
        {
            simp [h_1],
        },
        {
            simp [h_1],
        }
    },
    {
        simp [h],
        have hab := int.mod_add_div a b,
        rw mul_comm at hab,
        exact hab,
    }
    end,
    valuation := {
        val :=  λ a : ℤ, if a = 0 ∨ a = -1 then int.nat_abs a else (int.nat_abs a) + 1,
        property :=
        begin
            intros a b,
            cases decidable.em (b=0),
            {left, exact h},
            {
                right,
                cases decidable.em (a=0),
                {
                    simp [h_1],
                    cases decidable.em (b=1),
                    {
                        have one_neq : (1:int) ≠ -1, from dec_trivial,
                        simp [h_2, one_neq],
                        exact dec_trivial, -- is this the way you're meant to do this? (surely there's just a tactic)
                    },
                    {
                        simp [h_2,h],
                        cases decidable.em (b=-1),
                            {
                                simp [h_3],
                                exact dec_trivial,
                            },
                            {
                                simp [h_3],
                                exact dec_trivial,
                            }
                    }

                },
                {
                    simp [h_1],
                    cases decidable.em(b=1),
                    {
                        have one_neq : (1:ℤ) ≠ -1, from dec_trivial,
                        simp [h_2, one_neq],
                        exact dec_trivial,
                    },
                    {
                        simp [h],
                        cases decidable.em (b=-1),
                        {
                            simp [h_3],
                            exact dec_trivial,
                        },
                        {
                            simp [h_3],
                            cases decidable.em (a % b = 0 ∨ a % b = -1),
                            {
                                simp [h_4],
                                cases h_4,
                                {
                                    rw [h_4],
                                    exact dec_trivial,
                                },
                                {
                                    rw [h_4],
                                    simp,
                                    sorry -- follows from here since the only things -1 is not less than are itself and 0 and b+1 can't be 0 since b≠-1
                                }
                            },
                            {
                                simp [h_4],
                                sorry -- follows (we subtract 1 from both sides and then we have what we want from int's being a ED)
                            }
                        }
                    }
                }
            }
        end
    }
}
#reduce (euclidean_domain.remainder (0:int) 1)

lemma dvd_mod_zero {α : Type} [ed : decidable_euclidean_domain α] (a b : α) :  b ∣ a → a % b = 0 :=
begin
    intro b_dvd,

    cases decidable.em (b=0),
    {
        rw h at b_dvd,
        induction b_dvd with x hx,
        rw hx, simp,
    },
    {
        cases  val_mod a b,
        {contradiction},
        {
            induction b_dvd with x hx,
            have wit_ab := witness a b,
            conv at wit_ab {for a [1] {rw hx}},
            -- conv at wit_xx {for x [4] {rw ←h1}},
            -- conv {for b [2] {rw ←(witness b a)}},
            -- have b_dvd_mod : b ∣ (a%b), from sorry, -- this follows from a = b * x = (a/b)*b + (a%b)
            
            -- have := val_mul a b,
            sorry
        }
    }
end

--  @[simp] theorem mul_mod_right {α : Type} [ed: decidable_euclidean_domain α] (a b : α) : (a * b) % a = 0 :=
--  begin

--  end

-- theorem mod_eq_zero_of_dvd {α : Type} [ed: decidable_euclidean_domain α] {a b : α} (H : a ∣ b) :
--     b % a = 0 :=
-- dvd.elim H (λ z H1, by {rw [H1], sorry})

-- theorem mod_eq_zero_of_dvd {m n : ℕ} (H : m ∣ n) : n % m = 0 :=
-- dvd.elim H (λ z H1, by rw [H1, mul_mod_right])

-- @[simp] theorem mul_mod_right (m n : ℕ) : (m * n) % m = 0 :=
-- by rw [← zero_add (m*n), add_mul_mod_self_left, zero_mod]


theorem gcd_comm {α : Type} [ed: decidable_euclidean_domain α] (a b : α) : gcd a b = gcd b a :=
gcd.induction a b
    (λ b, by simp)
    (λ a b hna,
    begin
        intro h,
        rw gcd,
        simp[hna],
        cases decidable.em(b=0),
        {
            rw h_1,
            simp,
        },
        {
            apply eq.symm, -- This is a work-around as for some reason rw doesn't change the gcd on the right side
            rw gcd, 
            simp [h_1],
            --exact eq.symm h,

        }
    end)