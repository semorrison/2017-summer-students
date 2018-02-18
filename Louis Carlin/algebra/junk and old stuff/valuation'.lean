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

lemma valuation'_lt_one {α : Type} [decidable_euclidean_domain α] (x : α) : 
has_well_founded.r (valuation'.val x) (valuation'.val (1:α)) → x = 0 :=
begin
    intro x_lt,
    cases valuation'_property_2 1 x,
        {have := one_ne_zero, contradiction,},
        {cases h, 
            {exact h,},
            { simp at h,
            unfold has_well_founded.r at x_lt, -- this is ugly; stop doing it
            unfold sizeof_measure at x_lt,
            unfold sizeof at x_lt,
            unfold has_sizeof.sizeof at x_lt,
            unfold measure at x_lt,
            unfold inv_image at x_lt,
            unfold nat.sizeof at x_lt,
            have := not_le_of_lt x_lt,
            contradiction}
        }
end

lemma valuation'_dvd_le {α : Type} [ed : decidable_euclidean_domain α] (a b : α) :
    b ∣ a → a ≠ 0 → valuation'.val b ≤ valuation'.val a :=
begin
    intros b_dvd ha,
    induction b_dvd with x hx, rw hx,
    cases valuation'_property_2 b x,
        {rw h, simp},
        {cases h,
            {rw h at hx,
            simp at hx,
            contradiction},
            {rw mul_comm,
            exact h}}
end

@[simp] lemma mod_one {α : Type} [decidable_euclidean_domain α] (x : α) : x % 1 = 0 :=
begin
    have := valuation'.property x 1,
    cases this, have := one_ne_zero, contradiction,
    exact valuation'_lt_one (x % 1) this,
end 


@[simp] lemma zero_mod  {α : Type} [ed : decidable_euclidean_domain α] (b : α) : 0 % b = 0 :=
begin
    have h1 := euclidean_domain.witness 0 b,
    have h2 : euclidean_domain.remainder 0 b = b * (-euclidean_domain.quotient 0 b ), from sorry,
    cases valuation'_property_2 b (-euclidean_domain.quotient 0 b),
    {
        rw h, exact mod_zero (0:α)
    },
    {
        cases h, 
        {
            simp at h, rw h at h1, simp at h1,
            exact h1
        },
        {
            have h3 : -euclidean_domain.quotient 0 b * b = b * -euclidean_domain.quotient 0 b , by ring,
            rw [h3,←h2] at h,
            cases valuation'.property 0 b,
            {
                rw h_1, exact mod_zero (0:α),
            },
                unfold has_well_founded.r at h_1, -- lemma this unfold?
                unfold sizeof_measure at h_1,
                unfold sizeof at h_1,
                unfold has_sizeof.sizeof at h_1,
                unfold measure at h_1,
                unfold inv_image at h_1,
                unfold nat.sizeof at h_1,
                have := not_le_of_lt h_1,
                contradiction,
        }
    }
end


@[simp] lemma zero_div' {α : Type} [decidable_euclidean_domain α] (b : α) : b = 0 ∨ 0 / b = 0 :=
begin
    have h1 := zero_mod b, dsimp [(%)] at h1,
    have h2 := euclidean_domain.witness 0 b,
    rw h1 at h2,
    simp at h2,
    dsimp [(/)],
    cases decidable.em (b=0),
        {left, exact h},
        {right,
        cases eq_zero_or_eq_zero_of_mul_eq_zero h2,
            {exact h_1},
            {contradiction}}
end

@[simp] lemma mod_self {α : Type} [ed : decidable_euclidean_domain α] (x : α) : x % x = 0 :=
begin
    have := euclidean_domain.witness  x x,
    have divides : x ∣ x % x, from sorry,
    induction divides with m x_mul,
    cases valuation'_property_2 x m, rw h, 
        {exact mod_zero (0:α)},
        {cases h, 
            {rw [x_mul, h], simp},
            {rw mul_comm at x_mul, rw ←x_mul at h,
            cases  valuation'.property x x, 
                {rw h_1, exact mod_zero (0:α)},
                {unfold has_well_founded.r at h_1, -- this is ugly; stop doing it
                unfold sizeof_measure at h_1,
                unfold sizeof at h_1,
                unfold has_sizeof.sizeof at h_1,
                unfold measure at h_1,
                unfold inv_image at h_1,
                unfold nat.sizeof at h_1,
                have := not_le_of_lt h_1,
                contradiction}}}
end 


lemma div_self' {α : Type} [ed : decidable_euclidean_domain α] (x : α) : x = 0 ∨ x / x = (1:α) :=
begin
    have wit_xx := euclidean_domain.witness x x,
    have xx := mod_self x, 
    dsimp [(%)] at xx,
    rw xx at wit_xx, simp at wit_xx,
    have h1 : 1 * x = x, from one_mul x, -- use cases on x = 0
    cases decidable.em (x=0),
        {left, exact h},
        {right,
        conv at wit_xx {for x [4] {rw ←h1}},
        exact eq_of_mul_eq_mul_right h wit_xx}
end


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


-- @[simp] theorem gcd_zero_right {α : Type} [decidable_euclidean_domain α]  (n : α) : gcd n 0 = n :=
-- begin
--     cases decidable.em (n=0),
--     {
--         rw h,
--         simp,
--     },
--     {
--         rw gcd,
--         simp [h],
--     }
-- end

-- @[simp] theorem gcd_one_left {α : Type} [decidable_euclidean_domain α] (n : α) : gcd 1 n = 1 := 
-- begin
--     rw [gcd],
--     simp,
-- end

-- lemma zero_mod {α : Type} [ed:decidable_euclidean_domain α] (a : α) : 0 % a = 0 :=
-- begin

--     sorry
-- end


-- theorem gcd_next {α : Type} [decidable_euclidean_domain α] (x y : α) : gcd x y = gcd (y % x) x :=
-- begin
--     cases decidable.em (x=0),
--     {
--         rw [h],
--         simp,
--         rw gcd,
--         cases decidable.em (y=0),
--             {
--                 simp [h_1],
--             },
--             {
--                 simp [h_1],
--                 rw [zero_mod y], -- uses zero_mod
--                 simp,
--             }
--     },
--     {
--         rw gcd,
--         simp [h],
--     }
-- end


-- @[simp] theorem gcd_self {α : Type} [decidable_euclidean_domain α] (n : α) : gcd n n = n :=
-- by rw [gcd_next n n, mod_self n, gcd_zero_left]


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




-- theorem mod_eq_zero_of_dvd {α : Type} [ed: decidable_euclidean_domain α] {a b : α} (H : a ∣ b) :
--     b % a = 0 :=
-- dvd.elim H (λ z H1, by {rw [H1], sorry})

--  theorem gcd_comm {α : Type} [ed: decidable_euclidean_domain α] (a b : α) : gcd a b = gcd b a :=
-- begin
--     have := gcd.induction a b
--     begin
--         intro x,
--     end

-- end