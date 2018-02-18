/-
An alternative structure for group homomorphisms
-/

import data.set.basic
import init.function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

-- Structure or class?
-- Scott: no need for a class, for given groups G and H you'd never want to summon a mysterious instance of a homomorphism G → H
-- Scott: I'd also suggest calling this "group_homomorphism". "hom" could mean many things, and characters are cheap.
structure hom {α β} (G : group α) (H : group β) :=
    ( map : α → β )
    ( hom_mul : ∀ a b, map (a * b) = (map a) * (map b) )

attribute [simp] hom.hom_mul

namespace hom
variables [G : group α] [H : group β]
variables (f : hom G H) (a : α)

@[simp]
lemma one : f.map 1 = 1 :=
calc
    f.map 1 = (f.map 1)⁻¹ * (f.map 1 * f.map 1) : by simp
    ...     = 1                                 : by rw ← f.hom_mul; simp

@[simp]
lemma inv : f.map a⁻¹ = (f.map a)⁻¹ :=
calc
    f.map a⁻¹ = (f.map a)⁻¹ * (f.map a * f.map a⁻¹)      : by simp
    ...   = (f.map a)⁻¹ * f.map (a * a⁻¹)                : by rw f.hom_mul
    ...   = (f.map a)⁻¹                                  : by simp [f.one]

end hom

structure isom {α β} (G : group α) (H : group β) extends hom G H :=
    (is_bij : function.bijective map)