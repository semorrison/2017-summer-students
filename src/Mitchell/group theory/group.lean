/-
    Many of these basic definitions/proofs are modelled on similar definitions/proofs
    in mathlib's module.lean
-/

import data.set.basic
import init.function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

-- Structure or class?
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


class is_subgroup [group α] (s : set α) : Prop := 
    (one_closed : (1 : α) ∈ s)
    (inv_closed : ∀ {a}, a ∈ s → a⁻¹ ∈ s) 
    (mul_closed : ∀ {a b}, a ∈ s → b ∈ s → a * b ∈ s) 

attribute [simp] is_subgroup.one_closed is_subgroup.inv_closed is_subgroup.mul_closed

-- theorem int_subgroups (S : set ℤ) [group ℤ] [is_subgroup S] : ∃ a ∈ S, ∀ b ∈ S, a ∣ b := sorry

namespace is_subgroup
variables [group α] [group β]
variables {s : set α} [is_subgroup s]

instance trivial : is_subgroup ({1} : set α) :=
    by refine {..}; by simp {contextual := tt}

instance image {f : α → β} (hf: is_homomorphism f) : is_subgroup (f '' s) := {
    is_subgroup .
    mul_closed := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ * b₂, mul_closed hb₁ hb₂, by simp [eq₁, eq₂, hf.hom_mul]⟩,
    one_closed := ⟨1, one_closed s, hf.one⟩,
    inv_closed := assume a ⟨b, hb, eq⟩,
    ⟨b⁻¹, inv_closed hb, by simp [eq, hf.inv]⟩ 
}

instance preimage {f : β → α} (hf : is_homomorphism f) : is_subgroup (f ⁻¹' s) :=
    by refine {..}; simp [hf.hom_mul, hf.one, hf.inv] {contextual:=tt}

def kernel {f : α → β} (hf: is_homomorphism f) : set α := {a | f a = 1}

instance kernel_subg {f : α → β} (hf: is_homomorphism f) : is_subgroup (kernel hf) := 
    by refine {..}; simp [kernel, hf.hom_mul, hf.one, hf.inv] {contextual:=tt}

def left_coset  (a : α) {s : set α} [is_subgroup s] : set α := {b | ∃ (g : s), b = a * g}
def right_coset {s : set α} [is_subgroup s] (a : α) : set α := {b | ∃ (g : s), b = g * a}

lemma kernel_iff_equiv {f : α → β} (hf: is_homomorphism f) (a b : α) : f b = f a ↔ a⁻¹ * b ∈ kernel hf :=
begin
    split,
    {
        assume h,
        simp [kernel, has_mem.mem, set.mem, set_of], -- Is there a tactic which does this?
        simp [hf.hom_mul, hf.inv, h]
    },
    {
        assume h,
        simp [kernel, has_mem.mem, set.mem, set_of] at h,
        calc
            f b = f (a * a⁻¹ * b)   : by simp; rw [mul_assoc]; simp [hf.hom_mul, h]
            ... = f a               : by rw [mul_assoc]; simp [hf.hom_mul, h]
    }
    -- struggling with simp [mul_assoc]
end

theorem inj_iff_trivial_kernel {f : α → β} (hf: is_homomorphism f) : 
    function.injective f ↔ kernel hf = {1} :=
begin
    split,
    {
        unfold function.injective,
        assume h,
        have hx : ∃ x, x ∈ kernel hf := ⟨1, hf.one⟩,
        dsimp [kernel],
        suffices ht : ∀ a, f a = 1 → a = 1, -- Doesn't work!
        tactic.swap, -- Not necessary once suffices is working
        assume a ha,
        have hi : f a = f 1 := by simp [hf.one, ha],
        simp [h hi, hf.one],
        admit
    },
    {
        assume h a b,
        simp [kernel_iff_equiv hf b a, kernel, h],
        assume hbia,
        calc
            a   = b * b⁻¹ * a     : by simp 
            ... = b               : by rw mul_assoc; simp [hbia]
    }
end

end is_subgroup