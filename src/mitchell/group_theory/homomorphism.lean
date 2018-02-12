/-
    Many of these basic definitions/proofs are modelled on similar definitions/proofs
    in mathlib's module.lean
-/

import data.set.basic init.function algebra.group

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

-- Structure or class?
class is_hom [group α] [group β] (f : α → β) : Prop :=
    (hom_mul : ∀ a b, f (a * b) = f a * f b)

attribute [simp] is_hom.hom_mul

namespace is_hom
variables [group α] [group β] [group γ]

section

@[simp]
lemma one {f : α → β} (hf : is_hom f) : f 1 = 1 := 
mul_self_iff_eq_one.1 $ by rw ← hom_mul f (1 : α) (1 : α); simp

@[simp]
lemma inv {f : α → β} (hf : is_hom f) (a : α)  : f a⁻¹ = (f a)⁻¹ :=
eq.symm $ inv_eq_of_mul_eq_one $ by rw ← hom_mul f a a⁻¹; simp [hf.one]

end

lemma comp {g : β → γ} {f : α → β} (hg : is_hom g) (hf : is_hom f) : is_hom (g ∘ f) :=
{   hom_mul := λ x y, calc
    g (f (x * y)) = g (f x * f y)       : by simp [hf.hom_mul]
    ...           = g (f x) * g (f y)   : by simp [hg.hom_mul]
}

end is_hom