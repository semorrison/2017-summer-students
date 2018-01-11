universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

class subgroup {α : Type u} [group α] (S : set α) : Prop := 
    (mul_closed : ∀ a b ∈ S, a * b ∈ S) (inv_closed : ∀ a ∈ S, a⁻¹ ∈ S) (one_closed : (1 : α) ∈ S)

-- theorem int_subgroups (S : set ℤ) [group ℤ] [subgroup S] : ∃ a ∈ S, ∀ b ∈ S, a ∣ b := sorry

structure is_homomorphism [group α] [group β] (f : α → β) : Prop :=
    (hom_mul : ∀ a b, f (a * b) = (f a) * (f b))

attribute [simp] is_homomorphism.hom_mul

namespace is_homomorphism
variables [group α] [group β] [group γ]
variables {f : α → β} {g : β → γ} {a : α}

section
variable (hf: is_homomorphism f)
include hf

@[simp]
lemma one : f (1 : α) = 1 :=
calc
    f 1     = (f 1)⁻¹ * (f 1 * f 1)    : by simp
    ...     = (f 1)⁻¹ * f (1*1)        : by rw ← hom_mul hf
    ...     = 1                        : by simp
end

end is_homomorphism