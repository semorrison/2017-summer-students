/-
    Many of these basic definitions/proofs are modelled on similar definitions/proofs
    in mathlib's module.lean
-/

import data.set.basic
import init.function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

-- Structure or class?
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

class is_iso [group α] [group β] (f : α → β) : Prop :=
    (is_hom : is_hom f)
    (is_bij : function.bijective f)