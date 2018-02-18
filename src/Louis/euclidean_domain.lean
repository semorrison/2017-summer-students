import data.int.basic
import tactic.ring

universes u v
#check classical.some
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

/- gcd lemmas -/

@[simp] theorem gcd_zero_left {α : Type} [decidable_euclidean_domain α] (x : α) : gcd 0 x = x := 
begin
    rw gcd,
    simp,
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

lemma neq_zero_lt_mod_lt {α : Type} [ed: decidable_euclidean_domain α] : ∀ a b : α, b ≠ 0 → ed.valuation.val (a%b) < ed.valuation.val b :=
begin
    intros a b hnb,
    cases ed.valuation.property a b,
        {contradiction},
        {exact h}
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
                    (H1 : ∀ m n, m ≠ 0 → P (n%m) m → P m n) :
                P m n := 
@well_founded.induction _ _ (has_well_founded.wf α) (λm, ∀n, P m n) m (λk IH,
    by {cases decidable.em (k=0), rw h, exact H0,
        exact λ n, H1 k n (h) (IH (n%k) (neq_zero_lt_mod_lt n k h) k)}) n

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
            rw gcd, simp [h],
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
    (λ a b hna,
    begin
        intros d dvd_a dvd_b,
        rw gcd, simp [hna],
        exact d (dvd_mod dvd_b dvd_a) dvd_a,
    end)