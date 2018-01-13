/-
    Many of these basic definitions/proofs are modelled on similar definitions/proofs
    in mathlib's module.lean
-/

import data.set.basic

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

structure is_homomorphism [group α] [group β] (f : α → β) : Prop :=
    (hom_mul : ∀ a b, f (a * b) = (f a) * (f b))

attribute [simp] is_homomorphism.hom_mul

namespace is_homomorphism
variables [group α] [group β]
variables {f : α → β} {a : α}

section
variable (hf: is_homomorphism f)
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
end is_homomorphism


class subgroup [group α] (s : set α) : Prop := 
    (one_closed : (1 : α) ∈ s)
    (inv_closed : ∀ {a}, a ∈ s → a⁻¹ ∈ s) 
    (mul_closed : ∀ {a b}, a ∈ s → b ∈ s → a * b ∈ s) 

-- theorem int_subgroups (S : set ℤ) [group ℤ] [subgroup S] : ∃ a ∈ S, ∀ b ∈ S, a ∣ b := sorry

namespace subgroup
variables [group α] [group β]
variables {s : set α}[subgroup s]

instance trivial : subgroup ({1} : set α) :=
    by refine {..}; by simp {contextual := tt}

instance image {f : α → β} (hf: is_homomorphism f) : subgroup (f '' s) := {
    subgroup .
    mul_closed := assume c₁ c₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ * b₂, mul_closed hb₁ hb₂, by simp [eq₁, eq₂, hf.hom_mul]⟩,
    one_closed := ⟨1, one_closed s, hf.one⟩,
    inv_closed := assume a ⟨b, hb, eq⟩,
    ⟨b⁻¹, inv_closed hb, by simp [eq, hf.inv]⟩ 
}

instance preimage {f : β → α} (hf : is_homomorphism f) : subgroup (f ⁻¹' s) :=
    by refine {..}; simp [hf.hom_mul, hf.one, hf.inv, one_closed, inv_closed, mul_closed] {contextual:=tt}

instance kernel {f : α → β} (hf: is_homomorphism f) : subgroup (f ⁻¹' ({1} : set β)) := 
    preimage hf

end subgroup