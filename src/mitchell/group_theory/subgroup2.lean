/-
An alternative structure for subgroups
-/

import data.set.basic init.function mitchell.group_theory.homomorphism2

open set

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


class normal_subgroup (G : group α) extends subgroup G :=
    (normal : ∀ n ∈ set, ∀ g : α, g * n * g⁻¹ ∈ set)

def left_coset  {G : group α} (a : α) (G' : subgroup G) := {b : α | ∃ (g : G'.set), b = a * g}
def right_coset {G : group α} (G' : subgroup G) (a : α) := {b : α | ∃ (g : G'.set), b = g * a}

instance trivial (G : group α) : normal_subgroup G := {
    set := {(1 : α)},
    one_closed := by simp,
    inv_closed := by simp,
    mul_closed := by simp {contextual := tt},
    normal := by simp
}

instance image {G : group α} {H : group β} (f : hom G H) (G' : subgroup G) : subgroup H := {
    set := (f.map '' G'.set),
    one_closed := ⟨1, G'.one_closed, f.one⟩,
    inv_closed := assume a ⟨b, hb, eq⟩,
    ⟨b⁻¹, inv_closed hb, by simp [eq, f.inv]⟩ ,
    mul_closed := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ * b₂, mul_closed hb₁ hb₂, by simp [eq₁, eq₂, f.hom_mul]⟩
}

instance preimage {G : group α} {H : group β} (f : hom G H) (H' : subgroup H) : subgroup G := {
    set := (f.map ⁻¹' H'.set),
    one_closed := by simp,
    inv_closed := by simp {contextual := tt},
    mul_closed := by simp {contextual := tt}
}

instance normal_preimage {G : group α} {H : group β} (f : hom G H) (H' : normal_subgroup H) : normal_subgroup G := { 
    set        := (f.map ⁻¹' H'.set),
    one_closed := by simp,
    inv_closed := by simp {contextual := tt},
    mul_closed := by simp {contextual := tt},
    normal     := by simp; intros a ha g; apply H'.normal; assumption
}

instance kernel {G : group α} {H : group β} (f : hom G H) : normal_subgroup G := subgroup.normal_preimage f (subgroup.trivial H)

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

lemma subgroup_setwise_equal {G : group α} (H H' : subgroup G) (h : H.set = H'.set) : H = H' :=
begin
induction H,
induction H',
have hs : H_set = H'_set := h,
subst hs
end

lemma normal_subgroup_setwise_equal {G : group α} (H H' : normal_subgroup G) (h : H.set = H'.set) : H = H' :=
begin
induction H, induction H__to_subgroup with H_set,
induction H', induction H'__to_subgroup with H'_set,
have hs : H_set = H'_set := h,
subst hs
end

theorem inj_iff_trivial_kernel {G : group α} {H : group β} (f : hom G H) : 
    function.injective f.map ↔ subgroup.kernel f = subgroup.trivial G :=
begin
    split,
    {
        unfold function.injective,
        assume h,
        simp [subgroup.kernel, subgroup.trivial, subgroup.normal_preimage, set.preimage],
        apply normal_subgroup_setwise_equal,
        rw set.set_eq_def,
        simp [set.mem_set_of_eq],
        assume x,
        split,
        {
        assume hx,
        have hi : f.map x = f.map 1 := by simp [f.one, hx],
        simp [h hi, f.one]
        },
        {
        assume hx,
        simp [hx, f.one]
        }
    },
    {   
        assume h a b,       
        simp [kernel_iff_equiv f b a, h],
        rw h,
        simp [subgroup.set],
        assume hbia,
        calc
            a   = b * b⁻¹ * a     : by simp 
            ... = b               : by rw mul_assoc; simp [hbia]
    }
end

end subgroup