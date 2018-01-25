/-
    Many of these basic definitions/proofs are modelled on similar definitions/proofs
    in mathlib's module.lean
-/

-- Needs reorganisation - current order is just the order it was written

import data.set.basic init.function mitchell.group_theory.homomorphism

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

class is_subgroup [group α] (s : set α) : Prop := 
    (one_closed : (1 : α) ∈ s)
    (inv_closed : ∀ {a}, a ∈ s → a⁻¹ ∈ s) 
    (mul_closed : ∀ {a b}, a ∈ s → b ∈ s → a * b ∈ s) 

attribute [simp] is_subgroup.one_closed 
                 is_subgroup.inv_closed 
                 is_subgroup.mul_closed
                 
namespace is_subgroup
variables [group α] [group β]
variables {s : set α} [is_subgroup s]

instance trivial : is_subgroup ({1} : set α) :=
    by refine {..}; by simp {contextual := tt}

instance image {f : α → β} (hf: is_hom f) : is_subgroup (f '' s) := {
    is_subgroup .
    mul_closed := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ * b₂, mul_closed hb₁ hb₂, by simp [eq₁, eq₂, hf.hom_mul]⟩,
    one_closed := ⟨1, one_closed s, hf.one⟩,
    inv_closed := assume a ⟨b, hb, eq⟩,
    ⟨b⁻¹, inv_closed hb, by simp [eq, hf.inv]⟩ 
}

instance preimage {f : β → α} (hf : is_hom f) : is_subgroup (f ⁻¹' s) :=
    by refine {..}; simp [hf.hom_mul, hf.one, hf.inv] {contextual:=tt}

def kernel {f : α → β} (hf: is_hom f) : set α := {a | f a = 1}

instance kernel_subg {f : α → β} (hf: is_hom f) : is_subgroup (kernel hf) := 
    by refine {..}; simp [kernel, hf.hom_mul, hf.one, hf.inv] {contextual:=tt}

def left_coset  (a : α) (s : set α) [is_subgroup s] : set α := {b | ∃ (g : s), b = a * g}
def right_coset (s : set α) [is_subgroup s] (a : α) : set α := {b | ∃ (g : s), b = g * a}

lemma kernel_iff_equiv {f : α → β} (hf: is_hom f) (a b : α) : f b = f a ↔ a⁻¹ * b ∈ kernel hf :=
begin
    split,
    { assume h, simp [kernel, hf.hom_mul, hf.inv, h] },
    { assume h, simp [kernel] at h,
    calc
        f b = f (a * a⁻¹ * b)   : by simp; rw [mul_assoc]; simp [hf.hom_mul, h]
        ... = f a               : by rw [mul_assoc]; simp [hf.hom_mul, h] }
end

theorem inj_iff_trivial_kernel {f : α → β} (hf: is_hom f) : 
    function.injective f ↔ kernel hf = {1} :=
begin
    split,
    {
        dsimp [function.injective, kernel],
        simp [set.set_eq_def, set.mem_set_of_eq],
        assume h x,
        split,
        { 
        assume hx, 
        have hi : f x = f 1 := by simp [hf.one, hx],
        simp [h hi, hf.one]
        },
        { assume hx, simp [hx, hf.one] }
    },
    {
        assume h a b,
        simp [kernel_iff_equiv hf b a, kernel, h],
        assume hbia,
        calc
            a   = b * b⁻¹ * a     : by simp 
            ... = b               : by rw mul_assoc; simp [hbia]
    }
end

class is_normal_subgroup (s : set α) : Prop :=
    (is_subgroup : is_subgroup s)
    (normal : ∀ n ∈ s, ∀ g : α, g * n * g⁻¹ ∈ s)

instance kernel_normal {f : α → β} (hf: is_hom f) : is_normal_subgroup (kernel hf) :=
    by refine {..};
    simp [kernel, hf.hom_mul, hf.one, hf.inv] {contextual:=tt};
    apply (is_subgroup.kernel_subg hf)

def center (α : Type u) [group α] : set α := {z | ∀ g, g * z = z * g}

instance center_subg : is_subgroup (center α) := {
    is_subgroup .
    one_closed := by simp [center],
    mul_closed := begin
    intros a b ha hb g,
    rw [center, set.mem_set_of_eq] at *,
    rw [←mul_assoc, ha g, mul_assoc, hb g, ←mul_assoc]
    end,
    inv_closed := begin
    assume a ha g,
    simp [center] at *,
    calc
        g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹     : by simp [ha g]
        ...     = a⁻¹ * g                 : by rw [←mul_assoc, mul_assoc]; simp
    end
}

instance center_normal : is_normal_subgroup (center α) := {
    is_normal_subgroup .
    is_subgroup := is_subgroup.center_subg,
    normal := begin
    simp [center, set.mem_set_of_eq],
    intros n ha g h,
    calc
        h * (g * n * g⁻¹) = h * n               : by simp [ha g, mul_assoc]
        ...               = g * g⁻¹ * n * h     : by rw ha h; simp
        ...               = g * n * g⁻¹ * h     : by rw [mul_assoc g, ha g⁻¹, ←mul_assoc]
    end
}



theorem normal_iff_eq_cosets (s : set α) [hs : is_subgroup s] : 
    is_normal_subgroup s ↔ ∀ g, left_coset g s = right_coset s g :=
begin
split, tactic.swap,
    {
    intros hg,
    split,
    { assumption },
    {  -- Can probably be cleaned further
        intros n hn g,
        have hl : g * n ∈ left_coset g s, {
            simp [left_coset],
            existsi n,
            split,
            assumption, trivial
        },
        rw hg at hl,
        simp [right_coset] at hl,
        cases hl with x hx,
        cases hx with hxl hxr,
        have : g * n * g⁻¹ = x, {
        calc
            g * n * g⁻¹ = x * (g * g⁻¹) : by rw [hxr, mul_assoc]
            ...         = x             : by simp [mul_right_inv g]
        },
        rw this,
        exact hxl
    }},
    {
        intros h g,
        apply set.eq_of_subset_of_subset,
        all_goals { simp [left_coset, right_coset], intros a n ha hn },
        existsi g * n * g⁻¹, tactic.swap, existsi g⁻¹ * n * (g⁻¹)⁻¹,
        all_goals {split, apply h.normal, assumption },
        { rw inv_inv g, rw [←mul_assoc, ←mul_assoc], simp, assumption },
        { simp, assumption }
    }
end

end is_subgroup
