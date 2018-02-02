/-
    Many of these basic definitions/proofs are modelled on similar definitions/proofs
    in mathlib's module.lean
-/

-- Needs reorganisation - current order is just the order it was written

import data.set.basic init.function data.equiv init.logic 
import mitchell.group_theory.homomorphism

open set

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

class is_subgroup [group α] (s : set α) : Prop := 
    (one_mem : (1 : α) ∈ s)
    (inv_mem : ∀ {a}, a ∈ s → a⁻¹ ∈ s) 
    (mul_mem : ∀ {a b}, a ∈ s → b ∈ s → a * b ∈ s) 
                 
namespace is_subgroup

attribute [simp] is_subgroup.one_mem 
                 is_subgroup.inv_mem 
                 is_subgroup.mul_mem

-- Subgroup is a group
instance [group α] {s : set α} [is_subgroup s] : group s :=
{   mul := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, mul_mem hx hy⟩,
    mul_assoc := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ mul_assoc x y z,
    one := ⟨1, one_mem s⟩,
    one_mul := λ ⟨x, hx⟩, subtype.eq $ one_mul x,
    mul_one := λ ⟨x, hx⟩, subtype.eq $ mul_one x,
    inv := λ ⟨x, hx⟩, ⟨x⁻¹, inv_mem hx⟩,
    mul_left_inv := λ ⟨x, hx⟩, subtype.eq $ mul_left_inv x }

-- Examples of subgroups
def trivial [group α] : set α := {1}

end is_subgroup

namespace is_hom
variables [group α] [group β]

def image {f : α → β} (hf : is_hom f) (S : set α) : set β := f '' S

def preimage {f : α → β} (hf : is_hom f) (S : set β) : set α := f ⁻¹' S

def kernel {f : α → β} (hf : is_hom f) : set α := hf.preimage is_subgroup.trivial

end is_hom

namespace is_subgroup
variables [group α] [group β]

instance trivial_in : is_subgroup (@is_subgroup.trivial α _) :=
    by split; by simp [trivial] {contextual := tt}

instance image_in {f : α → β} (hf: is_hom f) (S : set α) [is_subgroup S] : is_subgroup (hf.image S) := {
    is_subgroup .
    mul_mem := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ * b₂, mul_mem hb₁ hb₂, by simp [eq₁, eq₂, hf.hom_mul]⟩,
    one_mem := ⟨1, one_mem S, hf.one⟩,
    inv_mem := assume a ⟨b, hb, eq⟩,
    ⟨b⁻¹, inv_mem hb, by rw hf.inv; simp *⟩ 
}

-- Should work, but simplifier refuses to unpack definition

-- instance preimage_in {f : β → α} (hf : is_hom f) (S : set α) [is_subgroup S] : is_subgroup (hf.preimage S) :=
--     by split; simp [hf.preimage S, hf.hom_mul, hf.one, hf.inv] {contextual:=tt};

-- instance kernel_in {f : α → β} (hf: is_hom f) : is_subgroup (hf.kernel) := 
--     by refine {..}; simp [hf.kernel, hf.preimage, hf.hom_mul, hf.one, hf.inv] {contextual:=tt}

-- lemma kernel_iff_equiv {f : α → β} (hf: is_hom f) (a b : α) : f b = f a ↔ a⁻¹ * b ∈ hf.kernel :=
-- begin
--     split,
--     { assume h, simp [hf.kernel, hf.hom_mul, hf.inv, h] },
--     { assume h, simp [kernel] at h,
--     calc
--         f b = f (a * a⁻¹ * b)   : by simp; rw [mul_assoc]; simp [hf.hom_mul, h]
--         ... = f a               : by rw [mul_assoc, hf.hom_mul]; simp [h] }
-- end

-- theorem inj_iff_trivial_kernel {f : α → β} (hf: is_hom f) : 
--     function.injective f ↔ hf.kernel = trivial :=
-- begin
--     split,
--     {
--         dsimp [function.injective, hf.kernel],
--         simp [set_eq_def, mem_set_of_eq],
--         assume h x,
--         split,
--         { 
--         assume hx, 
--         have hi : f x = f 1 := by simp [hf.one, hx],
--         simp [h hi, hf.one]
--         },
--         { assume hx, simp [hx, hf.one] }
--     },
--     {
--         assume h a b,
--         simp [kernel_iff_equiv hf b a, kernel, h],
--         assume hbia,
--         calc
--             a   = b * b⁻¹ * a     : by simp 
--             ... = b               : by rw mul_assoc; simp [hbia]
--     }
-- end

class is_normal_subgroup (s : set α) : Prop :=
    (subgroup : is_subgroup s)
    (normal : ∀ n ∈ s, ∀ g : α, g * n * g⁻¹ ∈ s)

attribute [instance] is_normal_subgroup.subgroup

-- instance kernel_normal {f : α → β} (hf: is_hom f) : is_normal_subgroup (hf.kernel) :=
--     by refine {..};
--     simp [hf.kernel, hf.hom_mul, hf.one, hf.inv] {contextual:=tt};
--     apply (is_subgroup.kernel_subg hf)

def center (α : Type u) [group α] : set α := {z | ∀ g, g * z = z * g}

instance center_subg : is_subgroup (center α) := {
    is_subgroup .
    one_mem := by simp [center],
    mul_mem := begin
    intros a b ha hb g,
    rw [center, mem_set_of_eq] at *,
    rw [←mul_assoc, ha g, mul_assoc, hb g, ←mul_assoc]
    end,
    inv_mem := begin
    assume a ha g,
    simp [center] at *,
    calc
        g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹     : by simp [ha g]
        ...     = a⁻¹ * g                 : by rw [←mul_assoc, mul_assoc]; simp
    end
}

instance center_normal : is_normal_subgroup (center α) := {
    is_normal_subgroup .
    subgroup := is_subgroup.center_subg,
    normal := begin
    simp [center, mem_set_of_eq],
    intros n ha g h,
    calc
        h * (g * n * g⁻¹) = h * n               : by simp [ha g, mul_assoc]
        ...               = g * g⁻¹ * n * h     : by rw ha h; simp
        ...               = g * n * g⁻¹ * h     : by rw [mul_assoc g, ha g⁻¹, ←mul_assoc]
    end
}

end is_subgroup
