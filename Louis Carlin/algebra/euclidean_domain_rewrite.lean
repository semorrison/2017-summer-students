import Louis.euclidean_domain

--TODO
-- convert to well founded instead of ℕ
-- do I do well founded on the valuation or just the inputs? 
-- Fix loads of unfolds
-- In general we don't have 0 % a = 0
-- Does the sizeof defintion issue hold everywhere?

-- Clean up:
-- indentation style?
-- is it better to get rid of haves wherever possible or do they make things more readable?




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
            {left, assumption},
            {
                right,
                cases decidable.em (a=0),
                {
                    simp [h_1],
                    cases decidable.em (b=1),
                    {
                        have one_neq : (1:int) ≠ -1, from dec_trivial, 
                        simp [h_2, one_neq],
                        
                        unfold has_well_founded.r,
                        unfold sizeof_measure,
                        unfold sizeof,
                        unfold measure,
                        unfold inv_image,
                        sorry --unfold has_sizeof.size, -- this doesn't work, some weird type class stuff is going on here (lean doesn't know what sizeof is because we're defining it here). The basic idea holds though
                        --unfold nat.sizeof,
                    },
                    {
                        simp [h_2,h],
                        sorry -- follows from cases on b=-1 here
                    }
                    
                },
                {
                    simp [h_1],
                    cases decidable.em(b=1),
                    {
                        have one_neq : (1:ℤ) ≠ -1, from dec_trivial,
                        simp [h_2, one_neq],
                        sorry -- same sizeof issue, but it would follow from here
                    },
                    {
                        simp [h],
                        cases decidable.em (b=-1),
                        {
                            simp [h_3],
                            sorry -- follows again
                        },
                        {
                            simp [h_3],
                            cases decidable.em (a % b = 0 ∨ a % b = -1),
                            {
                                simp [h_4],
                                cases h_4,
                                {
                                    rw [h_4],
                                    sorry -- follows from here
                                },
                                {
                                    rw [h_4],
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