--TODO
-- convert to well founded instead of ℕ
-- change to require only decidability for (x=0) (get rid of decidable_euclidean_domain entirely?)
-- do I do well founded on the valuation or just the inputs? 
-- Fix loads of unfolds

-- Clean up:
-- indentation style?
-- is it better to get rid of haves wherever possible or do they make things more readable?

import data.int.basic
import tactic.ring
--import init.meta.well_founded_tactics

universes u v

--definition euclidean_valuation' {α} [has_zero α] (r : α → α → α) := Σ W : Well_Ordered_Type, { f : α → W.β // ∀ a b, b = 0 ∨ @has_well_founded.r _ sorry (f(r a b)) (f b)}
-- probably easier to just use a structure at this point

structure Well_Ordered_Type := 
(β : Type)
(lt : β → β → Prop)
(w : is_well_order β lt)   -- TODO can β be made implicit in the defintion of is_well_order in mathlib?

/- very basic stuff (what to include in first PR) -/

definition euclidean_valuation {α} [has_zero α] (r : α → α → α) := { f : α → ℕ // ∀ a b, b = 0 ∨ has_well_founded.r (f(r a b)) (f b)}

class euclidean_domain (α : Type) extends integral_domain α :=
( quotient : α → α → α )
( remainder : α → α → α )
( witness : ∀ a b, (quotient a b) * b + (remainder a b) = a )
( valuation : euclidean_valuation remainder)

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
    sizeof := λ x, ed.valuation.val x,
}

definition gcd_decreasing  {α : Type} [ed:decidable_euclidean_domain α] (x y : α) (w : x ≠ 0) : has_well_founded.r (y % x) x := 
begin
cases ed.valuation.property y x,
                { contradiction },
                { exact h }
end

def gcd {α : Type} [ed : decidable_euclidean_domain α] : α → α → α
| x y := if x_zero : x = 0 then y
         else have h : has_well_founded.r (y % x) x := gcd_decreasing x y x_zero,
              gcd (y%x) x

/- end basic stuff -/

def lt_wf : well_founded (<) :=
begin
    have : is_well_order ℕ (<), by apply_instance,
    induction this,
    exact this_wf, -- why can't lean work this out itself?
end

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
                        cases decidable.em (c*b=0),
                            {
                                cases eq_zero_or_eq_zero_of_mul_eq_zero h_3,
                                    contradiction,
                                    contradiction,
                            },
                            {
                                exact h_3
                            },
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
            }
    end,
}


class has_well_order (β : Type) :=
(ordering : β → β → Prop)
(iwo : is_well_order β ordering)


def measure' {α} {β} [hwo : has_well_order β] : (α → β) → α → α → Prop :=
inv_image (hwo.ordering)

def measure_wf' {α} {β} [hwo : has_well_order β] (f : α → β) : well_founded (measure'  f) :=
inv_image.wf f hwo.iwo.wf

def has_well_founded_of_has_wo {α : Sort u} {β} [hwo : has_well_order β] (f: α → β) : has_well_founded α :=
{r := measure' f, wf := measure_wf' f}


instance has_well_order_nat : has_well_order ℕ :=
{
    ordering := (<), --nat.lt,
    iwo := by apply_instance
} 

instance ed_has_well_founded {α : Type} [ed: decidable_euclidean_domain α] : has_well_founded α :=
has_well_founded_of_has_wo ed.valuation.val


/- misc lemmas -/

@[simp] lemma mod_zero {α : Type} [ed : euclidean_domain α] (a : α)  : a % 0 = a :=
begin
    have := euclidean_domain.witness a 0,
    simp at this,
    exact this,
end

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




/- gcd lemmas -/

@[simp] theorem gcd_zero_left {α : Type} [decidable_euclidean_domain α] (x : α) : gcd 0 x = x := 
begin
    rw gcd,
    simp,
end


@[simp] theorem gcd_zero_right {α : Type} [decidable_euclidean_domain α]  (n : α) : gcd n 0 = n :=
begin
    cases decidable.em (n=0),
    {
        rw h,
        simp,
    },
    {
        rw gcd,
        simp [h],
    }
end

@[simp] theorem gcd_one_left {α : Type} [decidable_euclidean_domain α] (n : α) : gcd 1 n = 1 := 
begin
    rw [gcd],
    simp,
end

theorem gcd_next {α : Type} [decidable_euclidean_domain α] (x y : α) : gcd x y = gcd (y % x) x :=
begin
    cases decidable.em (x=0),
    {
        rw [h],
        simp,
    },
    {
        rw gcd,
        simp [h],
    }
end


@[simp] theorem gcd_self {α : Type} [decidable_euclidean_domain α] (n : α) : gcd n n = n :=
by rw [gcd_next n n, mod_self n, gcd_zero_left]

def zero_lt_nonzero {α : Type} [ed:decidable_euclidean_domain α] : ∀ a : α, a ≠ 0 → (ed.valuation.val (0:α)) < (ed.valuation.val a) :=
begin
    intros a aneq,
    have := zero_mod a,
    cases ed.valuation.property 0 a,
    { contradiction },
    {
        have hr := zero_mod a, dsimp [(%)] at hr,
        rw [hr] at h,
        exact  h,
    }
end

lemma mod_lt {α : Type} [ed: decidable_euclidean_domain α]  :
                     ∀ (x : α) {y : α}, ed.valuation.val y > ed.valuation.val 0 →  ed.valuation.val (x%y) < ed.valuation.val y :=
begin
    intros,
    cases decidable.em (y=0),
    {
        rw h at a,
        have := lt_irrefl ((euclidean_domain.valuation α).val 0),
        contradiction,
    },
    {
        cases ed.valuation.property x y with h h',
        { contradiction },
        { exact h' }
    }
end


lemma dvd_mod {α} [ed: decidable_euclidean_domain α] {a b c : α} : c ∣ a → c ∣ b → c ∣ a % b :=
begin
    intros dvd_a dvd_b,
    have : euclidean_domain.remainder a b = a - euclidean_domain.quotient a b * b, from
    calc 
        a%b = euclidean_domain.quotient a b * b + a%b - euclidean_domain.quotient a b * b : by ring
        ... = a - euclidean_domain.quotient a b * b : by {dsimp[(%)]; rw (euclidean_domain.witness a b)},
    dsimp [(%)], rw this,
    exact dvd_sub dvd_a (dvd_mul_of_dvd_right dvd_b (a/b)),
end

@[elab_as_eliminator]
theorem gcd.induction {α : Type} [ed: decidable_euclidean_domain α] 
                    {P : α → α → Prop}
                    (m n : α)
                    (H0 : ∀ x, P 0 x)
                    (H1 : ∀ m n, ed.valuation.val 0 < ed.valuation.val m → P (n%m) m → P m n) :
                P m n := 
@well_founded.induction _ _ (has_well_founded.wf α) (λm, ∀n, P m n) m (λk IH,
    by {cases decidable.em (k=0), rw h, exact H0,
        exact λ n, H1 k n (zero_lt_nonzero k h) (IH (n%k) (mod_lt n (zero_lt_nonzero k h)) k)}) n

-- def lcm (m n : ℕ) : ℕ := m * n / (gcd m n)

@[reducible] def coprime {α : Type} [ed: decidable_euclidean_domain α]  (a b : α) : Prop := gcd a b = 1


/- more gcd stuff (generalized mathlib/data/nat/gcd.lean) -/


theorem gcd_dvd {α : Type} [ed: decidable_euclidean_domain α] (a b : α) : (gcd a b ∣ a) ∧ (gcd a b ∣ b) :=
gcd.induction a b
    (λ b, by simp)
    (λ a b bpos,
    begin
        intro h_dvd,
        cases decidable.em (a=0),
        {
            rw h, simp,
        },
        {
            rw gcd_next,
            cases h_dvd,
            split,
                {exact h_dvd_right},
                {conv {for b [2] {rw ←(euclidean_domain.witness b a)}},
                have h_dvd_right_a:= dvd_mul_of_dvd_right h_dvd_right (b/a),
                exact dvd_add h_dvd_right_a h_dvd_left}
        }
    end )

theorem gcd_dvd_left {α : Type} [ed: decidable_euclidean_domain α] (a b : α) :
    gcd a b ∣ a := (gcd_dvd a b).left

theorem gcd_dvd_right {α : Type} [ed: decidable_euclidean_domain α] (a b : α) :
    gcd a b ∣ b := (gcd_dvd a b).right

/- Proof that the gcd is the top of the division hierarchy -/
theorem dvd_gcd {α : Type} [ed: decidable_euclidean_domain α] {a b c : α} : c ∣ a → c ∣ b → c ∣ gcd a b :=
gcd.induction a b
    (λ b,
    begin
        intros dvd_0 dvd_b,
        simp, exact dvd_b
    end)
    (λ a b bpos,
    begin
        intros d dvd_a dvd_b,
        rw gcd_next,
        exact d (dvd_mod dvd_b dvd_a) dvd_a,
    end)



-- theorem mod_eq_zero_of_dvd {α : Type} [ed: decidable_euclidean_domain α] {a b : α} (H : a ∣ b) :
--     b % a = 0 :=
-- dvd.elim H (λ z H1, by {rw [H1], sorry})

-- theorem gcd_comm (m n : ℕ) : gcd m n = gcd n m :=
-- dvd_antisymm
--   (dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n))
--   (dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m))
