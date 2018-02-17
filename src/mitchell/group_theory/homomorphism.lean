import data.set.basic init.function algebra.group

universes u v w
variables {G : Type u} {H : Type v} {K : Type w}

class group_hom [group G] [group H] (f : G → H) : Prop :=
    (hom_mul : ∀ a b, f (a * b) = f a * f b)

attribute [simp] group_hom.hom_mul

namespace group_hom
variables [group G] [group H] [group K]

section
variables (f : G → H) [group_hom f]

@[simp]
lemma one : f 1 = 1 := 
mul_self_iff_eq_one.1 $ by rw ← hom_mul f (1 : G) (1 : G); simp

@[simp]
lemma inv (a : G)  : f a⁻¹ = (f a)⁻¹ :=
eq.symm $ inv_eq_of_mul_eq_one $ by rw ← hom_mul f a a⁻¹; simp [one f]

end

lemma comp (g : H → K) (f : G → H) [group_hom g] [group_hom f] : group_hom (g ∘ f) :=
{   hom_mul := λ x y, calc
    g (f (x * y)) = g (f x * f y)       : by simp [group_hom.hom_mul f]
    ...           = g (f x) * g (f y)   : by simp [group_hom.hom_mul g]
}

end group_hom