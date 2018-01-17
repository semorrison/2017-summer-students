/-
    Many of these basic definitions/proofs are modelled on similar definitions/proofs
    in mathlib's module.lean
-/

-- Needs reorganisation - current order is just the order it was written

import data.set.basic
import init.function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}


structure is_hom [group α] [group β] (f : α → β) : Prop :=
    (hom_mul : ∀ a b, f (a * b) = (f a) * (f b))

attribute [simp] is_hom.hom_mul

namespace is_hom
variables [group α] [group β]
variables {f : α → β} {a : α}

section
variable (hf: is_hom f)
include hf

@[simp]
lemma one : f 1 = 1 :=
calc
    f 1     = (f 1)⁻¹ * (f 1 * f 1)    : by simp
    ...     = 1                        : by rw ← hom_mul hf; simp

@[simp]
lemma inv : f a⁻¹ = (f a)⁻¹ :=
calc
    f a⁻¹ = (f a)⁻¹ * (f a * f a⁻¹)      : by simp
    ...   = (f a)⁻¹ * f (a * a⁻¹)        : by rw hom_mul hf
    ...   = (f a)⁻¹                      : by simp [one hf]

end
end is_hom


class is_subgroup [group α] (s : set α) : Prop := 
    (one_closed : (1 : α) ∈ s)
    (inv_closed : ∀ {a}, a ∈ s → a⁻¹ ∈ s) 
    (mul_closed : ∀ {a b}, a ∈ s → b ∈ s → a * b ∈ s) 

attribute [simp] is_subgroup.one_closed 
                 is_subgroup.inv_closed 
                 is_subgroup.mul_closed

-- theorem int_subgroups (S : set ℤ) [group ℤ] [is_subgroup S] : ∃ a ∈ S, ∀ b ∈ S, a ∣ b := sorry

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
    {
        assume h,
        simp [kernel],
        simp [hf.hom_mul, hf.inv, h]
    },
    {
        assume h,
        simp [kernel] at h,
        calc
            f b = f (a * a⁻¹ * b)   : by simp; rw [mul_assoc]; simp [hf.hom_mul, h]
            ... = f a               : by rw [mul_assoc]; simp [hf.hom_mul, h]
    }
    -- struggling with simp [mul_assoc]
end

-- TODO: clean up proof
theorem inj_iff_trivial_kernel {f : α → β} (hf: is_hom f) : 
    function.injective f ↔ kernel hf = {1} :=
begin
    split,
    {
        unfold function.injective,
        assume h,
        have hx : ∃ x, x ∈ kernel hf := ⟨1, hf.one⟩,
        dsimp [kernel],
        rw set.set_eq_def,
        simp [set.mem_set_of_eq],
        assume x,
        split,
        {
        assume hx,
        have hi : f x = f 1 := by simp [hf.one, hx],
        simp [h hi, hf.one]
        },
        {
        assume hx,
        simp [hx, hf.one]
        }
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

-- Not a particularly pretty definition, feel as though it could be improved
-- Potentially by defining a normal subset first?
class is_normal_subgroup (s : set α) : Prop :=
    (is_subgroup : is_subgroup s)
    (normal : ∀ n ∈ s, ∀ g : α, g * n * g⁻¹ ∈ s)

instance kernel_normal {f : α → β} (hf: is_hom f) : is_normal_subgroup (kernel hf) :=
    by refine {..};
    simp [kernel, hf.hom_mul, hf.one, hf.inv] {contextual:=tt};
    apply (is_subgroup.kernel_subg hf)

def center (α : Type u) [group α] : set α := {z | ∀ g, g * z = z * g}

-- TODO: clean up proof
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
    simp [center] at *,  -- Should be possible to make this more compact
    calc
        g * a⁻¹ = a⁻¹ * (a * g) * a⁻¹     : by simp
        ...     = a⁻¹ * (g * a) * a⁻¹     : by simp [ha g]
        ...     = a⁻¹ * g * (a * a⁻¹)     : by rw [←mul_assoc, mul_assoc]
        ...     = a⁻¹ * g                 : by simp
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
        ...               = n * h               : by rw ha h
        ...               = g * g⁻¹ * n * h     : by simp
        ...               = g * n * g⁻¹ * h     : by rw [mul_assoc g, ha g⁻¹, ←mul_assoc]
    end
}


-- TODO: Terrible! Needs significant clean up
theorem normal_iff_eq_cosets (s : set α) [hs : is_subgroup s] : 
    is_normal_subgroup s ↔ ∀ g, left_coset g s = right_coset s g :=
    begin
    split,
    {
        intros h g,
        have hlr : left_coset g s ⊆ right_coset s g,
        {
            simp [left_coset, right_coset],
            intros a n ha hn,
            let n₁ := g * n * g⁻¹,
            existsi n₁,
            split,
            { apply h.normal, assumption },
            { simp, assumption },
        },
        have hrl : right_coset s g ⊆ left_coset g s, 
        {
            simp [right_coset, left_coset],
            intros a n ha hn,
            existsi g⁻¹ * n * (g⁻¹)⁻¹,
            split,
            { apply h.normal, assumption },
            { rw inv_inv g, rw [←mul_assoc, ←mul_assoc], simp, assumption },
        },
        show left_coset g s = right_coset s g, from set.eq_of_subset_of_subset hlr hrl,
    },
    {
        intros hg,
        refine {..},
        { assumption },
        {
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
            have : g * n * g⁻¹ = x,{
            calc
                g * n * g⁻¹ = x * (g * g⁻¹) : by rw [hxr, mul_assoc]
                ...         = x             : by simp [mul_right_inv g]
            },
            rw this,
            exact hxl
        }      
    }
    end
    


end is_subgroup

-- An alternative style:
-- structure group_homomorphism {α β} (G : group α) (H : group β) :=
--   ( map : α → β )

-- structure subgroup {α} (G : group α) := 
--   ( underlying_set : set α )
--   (one_closed : (1 : α) ∈ underlying_set)
--   (inv_closed : ∀ {a}, a ∈ underlying_set → a⁻¹ ∈ underlying_set) 
--   (mul_closed : ∀ {a b}, a ∈ underlying_set → b ∈ underlying_set → a * b ∈ underlying_set) 

-- def kernel {α β} {G : group α} {H : group β} (f: group_homomorphism G H) : subgroup G := {

-- }


