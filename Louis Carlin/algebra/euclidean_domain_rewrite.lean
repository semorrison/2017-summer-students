import Louis.euclidean_domain

def xgcd_aux {α} [decidable_euclidean_domain α] : α → α → α → α → α → α → α × α × α
| r s t r' s' t' := if r_zero : r = 0 then (r', s', t') 
    else have has_well_founded.r (r' % r) r, from neq_zero_lt_mod_lt r' r r_zero,
    let q := r' / r in xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t

@[simp] theorem xgcd_zero_left {α} [decidable_euclidean_domain α] {s t r' s' t' : α} :
    xgcd_aux (0:α) s t r' s' t' = (r', s', t') :=
by rw xgcd_aux; simp

@[simp] theorem xgcd_aux_rec {α} [decidable_euclidean_domain α] {r s t r' s' t' : α} (h : has_well_founded.r 0 r) : xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - (r' / r) * s) (t' - (r' / r) * t) r s t :=
begin
    cases decidable.em (r = 0),
    {
        rw h_1 at h,
        exact absurd h (lt_irrefl ((euclidean_domain.valuation α).val 0)),
    },
    {
        rw xgcd_aux,
        simp [h_1],
    }
end



--by simp [xgcd_aux]


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
