import Louis.euclidean_domain
import 

lemma set_nonempty {α : Type} [ed : decidable_euclidean_domain α] :
        ∀ a, {n : ℕ | ∃ (x : α), x ≠ 0 ∧ n = (euclidean_domain.valuation α).val (x * a)} ≠ ∅ :=
    begin
        intro a,
        have fin :ed.valuation.val (1*a) ∈ {n : nat | ∃ x, x ≠ 0 ∧ n = ed.valuation.val (x*a)},
        existsi (1:α),
        split,
        exact one_ne_zero,
        simp,
        exact set.ne_empty_of_mem fin,
    end

lemma not_zero_mul_not_zero_to_not_zero {α} [decidable_euclidean_domain α] {a b : α} (h1 : a ≠ 0) (h2 : b ≠ 0) : a*b ≠ 0 :=
begin
cases decidable.em (a*b=0),
{
    cases eq_zero_or_eq_zero_of_mul_eq_zero h,
        contradiction,
        contradiction,
},
{
    exact h
},
end

noncomputable def valuation'_val  {α : Type} [ed : decidable_euclidean_domain α] :=
λ a, well_founded.min lt_wf {n : nat | ∃ x, x ≠ 0 ∧ n = ed.valuation.val (x*a)}  (set_nonempty a)

lemma valuation'_property_2 {α : Type} [ed : decidable_euclidean_domain α] :
    ∀ a b : α, a = 0 ∨ b = 0 ∨ (valuation'_val a) ≤ (valuation'_val (b*a)) :=
begin
    intros,
    cases decidable.em (a=0),
    {
        left,
        exact h
    },
    {
        cases decidable.em (b=0),
        {
            right, left, exact h_1,
        },
        {
            right, right,
            rw [valuation'_val],
            cases decidable.em (b*a=0),
            {
                have := eq_zero_or_eq_zero_of_mul_eq_zero h_2,
                cases this, contradiction, contradiction,
            },
            {
                simp [h,h_1,h_2],
                let S_ba := {n : ℕ | ∃ (x : α), ¬x = 0 ∧ n = (euclidean_domain.valuation α).val (x * (b * a))},
                have min_in := well_founded.min_mem lt_wf S_ba (set_nonempty (b*a)),
                dsimp [S_ba] at min_in, unfold set_of at min_in,
                induction min_in with c hc,
                cases hc, rw ←mul_assoc at hc_right,
                
                
                have cb_in : ((euclidean_domain.valuation α).val (c*b*a)) ∈ {n : ℕ | ∃ (x : α), ¬x = 0 ∧ n = (euclidean_domain.valuation α).val (x * a)}, 
                    by {
                        unfold set_of, dsimp [(∈)], unfold set.mem, -- there's a lemma
                        existsi (c*b),
                        split,
                        exact not_zero_mul_not_zero_to_not_zero hc_left h_1,
                        refl,
                    },

                let S_a := {n : ℕ | ∃ (x : α), ¬x = 0 ∧ n = (euclidean_domain.valuation α).val (x * a)},
                have leq:= le_of_not_lt (well_founded.not_lt_min lt_wf S_a (set_nonempty a) cb_in),
                unfold set_of, rw hc_right,
                exact leq,
            }
        }
    }
end

/- 
Wikipedia suggests defining a valuation with the property "For all nonzero a and b in α, f(a) ≤ f(ab)".
Proof is based on the one by Rogers, Kenneth (1971), "The Axioms for Euclidean Domains"
-/
noncomputable def valuation' {α : Type} [ed : decidable_euclidean_domain α] : euclidean_valuation (ed.remainder) := 
{ -- you could maybe get around this requiring decidable_euclidean_domain by using em since this is already non-computable
    val := valuation'_val,
    property :=
    begin
        intros,
        cases decidable.em (b=0),
            {left, exact h},
            {
                right,
                let S_b :=  {n : ℕ | ∃ (x : α), x ≠ 0 ∧ n = (euclidean_domain.valuation α).val (x * b)},
                have min_in := well_founded.min_mem lt_wf S_b (set_nonempty b),
                dsimp [S_b] at min_in, unfold set_of at min_in,
                induction min_in with c hc,
                cases hc,
                have wit_acbc := euclidean_domain.witness (a*c) (b*c),
                have dvd_c : c ∣ euclidean_domain.remainder (a * c) (b * c), from sorry,
                induction dvd_c with r,
                --rw dvd_c_h at wit_acbc,

                have trans1 : valuation'_val r ≤ ed.valuation.val (r*c), from sorry, -- this follows from well_founded.min_mem and the fact that valuation.val (r*c) is in the set
                have trans2 := ed.valuation.property (a*c) (b*c),
                cases trans2,
                    {
                        have :=  not_zero_mul_not_zero_to_not_zero h hc_left,
                        contradiction,
                    },
                    {

                        
                         unfold valuation'_val, unfold set_of,
                        rw hc_right,
                    }
            }
    end,
}

-- This is a mess, get it in order
lemma dvd_mod_zero {α : Type} [ed : decidable_euclidean_domain α] (a b : α) :
    b ∣ a → a % b = 0 :=
begin
    intro b_dvd,
    have := valuation'.property a b,
    cases decidable.em (b=0),
    {
        induction b_dvd with x hx,
        rw h at hx, simp at hx,
        rw [h,hx],
        simp,
    },
    {
        cases this,
        contradiction,
        {
            cases decidable.em (a=0),

            rw h_1,
            exact zero_mod b,

            unfold has_well_founded.r at this, -- this is ugly; stop doing it
            unfold sizeof_measure at this,
            unfold sizeof at this,
            unfold has_sizeof.sizeof at this,
            unfold measure at this,
            unfold inv_image at this,
            unfold nat.sizeof at this,
            have b_dvd_mod : b ∣ (a%b), from sorry, -- this follows from a = b * x = (a/b)*b + (a%b)
            cases decidable.em ((a%b)=0),
                exact h_2,
            have := not_lt_of_le ( valuation'_dvd_le _ _ b_dvd_mod h_2),
            contradiction,
        }
    }
    
end


-- lemma zero_lt_nonzero {α : Type} [ed:decidable_euclidean_domain α] : ∀ a : α, a ≠ 0 → (ed.valuation.val (0:α)) < (ed.valuation.val a) :=
-- begin
--     intros a aneq,
--     cases ed.valuation.property 0 a,
--     { contradiction },
--     {
--         have hr := zero_mod a, dsimp [(%)] at hr, -- uses zero_mod
--         rw [hr] at h,
--         exact  h,
--     }
-- end