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


class subgroup [group α] (S : set α) : Prop := 
    (one_closed : (1 : α) ∈ S)
    (inv_closed : ∀ {a}, a ∈ S → a⁻¹ ∈ S) 
    (mul_closed : ∀ {a b}, a ∈ S → b ∈ S → a * b ∈ S) 

-- theorem int_subgroups (S : set ℤ) [group ℤ] [subgroup S] : ∃ a ∈ S, ∀ b ∈ S, a ∣ b := sorry

namespace subgroup
variables [group α] [group β]
variables {S : set α} [subgroup S]

section
variables {x y : α}

end


instance image {f : α → β} (hf: is_homomorphism f) : subgroup (f '' S) :=
    {
        subgroup .
        mul_closed := assume c₁ c₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
        ⟨b₁ * b₂, mul_closed hb₁ hb₂, by simp [eq₁, eq₂, hf.hom_mul]⟩,
        one_closed := ⟨1, one_closed S, hf.one⟩,
        inv_closed := assume a ⟨b, hb, eq⟩,
        ⟨b⁻¹, inv_closed hb, by simp [eq, hf.inv]⟩ 
    }

end subgroup