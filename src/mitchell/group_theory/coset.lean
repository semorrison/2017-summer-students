
import data.set.basic mitchell.group_theory.subgroup

open set

universe u
variable {α : Type u}

definition lcoset [has_mul α] (a : α) (S : set α) : set α := image (λ x, a * x) S
definition rcoset [has_mul α] (S : set α) (a : α) : set α := image (λ x, x * a) S

namespace coset_notation

infix * := lcoset
infix * := rcoset

end coset_notation

section coset_mul
open coset_notation
variable [has_mul α]

lemma mem_lcoset {S : set α} {x : α} (a : α) (hxS : x ∈ S) : a * x ∈ a * S :=
mem_image_of_mem (λ b : α, a * b) hxS

lemma mem_rcoset {S : set α} {x : α} (a : α) (hxS : x ∈ S) : x * a ∈ S * a :=
mem_image_of_mem (λ b : α, b * a) hxS

def lcoset_equiv (S : set α) (a b : α) := a * S = b * S

lemma lcoset_equiv_rel (S : set α) : equivalence (lcoset_equiv S) := 
    mk_equivalence (lcoset_equiv S) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
open coset_notation
variable [semigroup α]

lemma lcoset_assoc (S : set α) (a b : α) : a * (b * S) = (a * b) * S := sorry

lemma rcoset_assoc (S : set α) (a b : α) : S * a * b = S * (a * b) := sorry

lemma lcoset_rcoset (S : set α) (a b : α) : a * S * b = a * (S * b) := sorry

end coset_semigroup

section coset_monoid
open coset_notation
variable [monoid α]

lemma one_lcoset (S : set α) : 1 * S = S := sorry

lemma rcoset_one (S : set α) : S * 1 = S := sorry

end coset_monoid

section coset_group
open is_subgroup coset_notation
variable [group α]

lemma eq_of_lcoset {a : α} {S T : set α} (h : a * S = a * T) : S = T := sorry

lemma eq_of_rcoset {a : α} {S T : set α} (h : S * a = T * a) : S = T := sorry

theorem normal_iff_eq_cosets [group α] (S : set α) [hs : is_subgroup S] : 
    is_normal_subgroup S ↔ ∀ g, g * S = S * g :=
begin
split, tactic.swap,
    {
    intros hg,
    split,
    { assumption },
    {  -- Can probably be cleaned further
        intros n hn g,
        have hl : g * n ∈ g * S, from mem_lcoset g hn,
        rw hg at hl,
        simp [rcoset] at hl,
        cases hl with x hx,
        cases hx with hxl hxr,
        have : g * n * g⁻¹ = x, {
        calc
            g * n * g⁻¹ = x * g * g⁻¹ : by rw ←hxr
            ...         = x           : by simp
        },
        rw this,
        exact hxl
    }},
    {
        intros h g,
        apply eq_of_subset_of_subset,
        all_goals { simp [lcoset, rcoset, image], intros a n ha hn },
        existsi g * n * g⁻¹, tactic.swap, existsi g⁻¹ * n * (g⁻¹)⁻¹,
        all_goals {split, apply h.normal, assumption },
        { rw inv_inv g, rw [←mul_assoc, ←mul_assoc], simp, assumption },
        { simp, assumption }
    }
end

end coset_group