/-
An alternative structure for subgroups
-/

import data.set.basic init.function mitchell.group_theory.homomorphism2

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

class subgroup (G : group α) := 
    (set : set α)
    (one_closed : (1 : α) ∈ set)
    (inv_closed : ∀ {a}, a ∈ set → a⁻¹ ∈ set) 
    (mul_closed : ∀ {a b}, a ∈ set → b ∈ set → a * b ∈ set) 

attribute [simp] subgroup.one_closed 
                 subgroup.inv_closed 
                 subgroup.mul_closed

namespace subgroup

instance trivial (G : group α) : subgroup G := {
    subgroup .
    set := {(1 : α)},
    one_closed := by simp,
    inv_closed := by simp,
    mul_closed := by simp {contextual := tt}
}

instance image {G : group α} {H : group β} (f : hom G H) (G' : subgroup G) : subgroup H := {
    subgroup .
    set := (f.map '' G'.set),
    one_closed := ⟨1, G'.one_closed, f.one⟩,
    inv_closed := assume a ⟨b, hb, eq⟩,
    ⟨b⁻¹, inv_closed hb, by simp [eq, f.inv]⟩ ,
    mul_closed := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ * b₂, mul_closed hb₁ hb₂, by simp [eq₁, eq₂, f.hom_mul]⟩
}

instance preimage {G : group α} {H : group β} (f : hom G H) (H' : subgroup H) : subgroup G := {
    subgroup .
    set := (f.map ⁻¹' H'.set),
    one_closed := by simp,
    inv_closed := by simp {contextual := tt},
    mul_closed := by simp {contextual := tt}
}

instance kernel {G : group α} {H : group β} (f : hom G H) : subgroup G := subgroup.preimage f (subgroup.trivial H)

def left_coset  {G : group α} (a : α) (G' : subgroup G) := {b : α | ∃ (g : G'.set), b = a * g}
def right_coset {G : group α} (G' : subgroup G) (a : α) := {b : α | ∃ (g : G'.set), b = g * a}

class normal_subgroup (G : group α) extends subgroup G :=
    (normal : ∀ n ∈ set, ∀ g : α, g * n * g⁻¹ ∈ set)

variables {G : group α} {H : group β} (f : hom G H)

lemma kernel_iff_equiv {G : group α} {H : group β} (f : hom G H) (a b : α) : 
    f.map b = f.map a ↔ a⁻¹ * b ∈ (subgroup.kernel f).set :=
begin
    split,
    {
        assume h,
        simp [set],
        simp [f.hom_mul, f.inv, h]
    },
    {
        assume h,
        simp [set] at h,
        calc
            f.map b = f.map (a * a⁻¹ * b)   : by simp; rw [mul_assoc]; simp [f.hom_mul, h]
            ... = f.map a                   : by rw [mul_assoc]; simp [f.hom_mul, h]
    }
end

end subgroup