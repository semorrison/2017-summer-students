/-
    Many of these basic definitions/proofs are modelled on similar definitions/proofs
    in mathlib's module.lean
-/

-- Needs reorganisation - current order is just the order it was written

-- Note to self: Don't use tactics in instances: they're definitions under the hood, so the proof isn't irrelevant
-- Move relevant lemma outside instance if necessary

import data.set.basic init.function data.equiv init.logic 
import mitchell.group_theory.homomorphism

open set

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

class is_subgroup [group α] (s : set α) : Prop := 
    (mul_mem : ∀ {a b}, a ∈ s → b ∈ s → a * b ∈ s) 
    (one_mem : (1 : α) ∈ s)
    (inv_mem : ∀ {a}, a ∈ s → a⁻¹ ∈ s) 

class is_normal_subgroup [group α] (s : set α) extends is_subgroup s : Prop :=
    (normal : ∀ n ∈ s, ∀ g : α, g * n * g⁻¹ ∈ s)
             
namespace is_subgroup

attribute [simp] is_subgroup.one_mem 
                 is_subgroup.inv_mem 
                 is_subgroup.mul_mem
                 is_normal_subgroup.normal

-- Subgroup is a group
lemma subgroup_group [group α] {s : set α} (hs : is_subgroup s) : group s :=
{   mul := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, mul_mem hx hy⟩,
    mul_assoc := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ mul_assoc x y z,
    one := ⟨1, one_mem s⟩,
    one_mul := λ ⟨x, hx⟩, subtype.eq $ one_mul x,
    mul_one := λ ⟨x, hx⟩, subtype.eq $ mul_one x,
    inv := λ ⟨x, hx⟩, ⟨x⁻¹, inv_mem hx⟩,
    mul_left_inv := λ ⟨x, hx⟩, subtype.eq $ mul_left_inv x }

-- Normal subgroup properties
lemma mem_norm_comm [group α] {a b : α} {S : set α} [is_normal_subgroup S] (hab : a * b ∈ S) : b * a ∈ S := 
    have h : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ S, from is_normal_subgroup.normal (a * b) hab a⁻¹,
    by simp at h; exact h

-- Examples of subgroups
@[simp]
def trivial (h : group α) : set α := {1}

-- Difference between refine and split - Refine works for extensions
lemma trivial_in [h : group α] : is_normal_subgroup (is_subgroup.trivial h) :=
    by refine {..}; simp {contextual := tt}

lemma univ_in [group α] : is_subgroup (@univ α) :=
    by split; simp

attribute [instance] subgroup_group trivial_in univ_in

def center (α : Type u) [group α] : set α := {z | ∀ g, g * z = z * g}

lemma center_normal_in [group α] : is_normal_subgroup (center α) := {
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
    end,
    normal := begin
    simp [center, mem_set_of_eq],
    intros n ha g h,
    calc
        h * (g * n * g⁻¹) = h * n               : by simp [ha g, mul_assoc]
        ...               = g * g⁻¹ * n * h     : by rw ha h; simp
        ...               = g * n * g⁻¹ * h     : by rw [mul_assoc g, ha g⁻¹, ←mul_assoc]
    end
}

attribute [instance] center_normal_in

end is_subgroup


-- Homomorphism subgroups
namespace is_hom
open is_subgroup
variables [G : group α] [H : group β]
include G H

@[simp]
def kernel {f : α → β} (hf : is_hom f) : set α := preimage f (trivial H)

lemma mem_ker_one {f : α → β} (hf : is_hom f) {x : α} (h : x ∈ hf.kernel) : f x = 1 := sorry

lemma ker_inv {f : α → β} (hf : is_hom f) {a b : α} (h : a * b⁻¹ ∈ hf.kernel) : f a = f b := sorry

lemma inv_ker {f : α → β} (hf : is_hom f) {a b : α} (h : f a = f b) : a * b⁻¹ ∈ hf.kernel := sorry

lemma inv_ker_one {f : α → β} (hf : is_hom f) {a b : α} (h : f a = f b) : f (a * b⁻¹) = 1 := mem_ker_one hf $ inv_ker hf h

lemma one_ker_inv {f : α → β} (hf : is_hom f) {a b : α} (h : f (a * b⁻¹) = 1) : f a = f b := sorry

lemma image_in {f : α → β} (hf: is_hom f) (S : set α) [is_subgroup S] : is_subgroup (f '' S) := {
    is_subgroup .
    mul_mem := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ * b₂, mul_mem hb₁ hb₂, by simp [eq₁, eq₂, hf.hom_mul]⟩,
    one_mem := ⟨1, one_mem S, hf.one⟩,
    inv_mem := assume a ⟨b, hb, eq⟩,
    ⟨b⁻¹, inv_mem hb, by rw hf.inv; simp *⟩ 
}

lemma preimage_in {f : α → β} (hf : is_hom f) (S : set β) [is_subgroup S] : is_subgroup (f ⁻¹' S) :=
    by refine {..}; simp [hf.hom_mul, hf.one, hf.inv] {contextual:=tt}

lemma preimage_norm_in {f : α → β} (hf : is_hom f) (S : set β) [is_normal_subgroup S] : is_normal_subgroup (f ⁻¹' S) :=
    by refine {..}; simp [hf.hom_mul, hf.one, hf.inv] {contextual:=tt}

lemma kernel_in {f : α → β} (hf: is_hom f) : is_normal_subgroup (hf.kernel) := 
    preimage_norm_in hf (trivial H)

attribute [instance] image_in preimage_in kernel_in

lemma kernel_iff_equiv {f : α → β} (hf: is_hom f) (a b : α) : f b = f a ↔ a⁻¹ * b ∈ hf.kernel :=
begin
    split,
    { assume h, simp [hf.hom_mul, hf.inv, h] },
    { assume h, simp at h,
    calc
        f b = f (a * a⁻¹ * b)   : by simp; rw [mul_assoc]; simp [hf.hom_mul, h]
        ... = f a               : by rw [mul_assoc, hf.hom_mul]; simp [h] }
end

lemma inj_iff_trivial_kernel {f : α → β} (hf: is_hom f) : 
    function.injective f ↔ hf.kernel = trivial G :=
begin
    split,
    {
        dsimp [function.injective],
        simp [set_eq_def, mem_set_of_eq],
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
        simp [kernel_iff_equiv hf b a, h],
        assume hbia,
        calc
            a   = b * b⁻¹ * a     : by simp 
            ... = b               : by rw mul_assoc; simp [hbia]
    }
end

end is_hom