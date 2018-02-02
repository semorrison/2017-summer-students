
import data.set.basic init.function data.equiv init.logic 
import mitchell.group_theory.coset mitchell.group_theory.subgroup

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace quotient_group
open is_subgroup coset_notation
variable [group α]

def norm_equiv (N : set α) (a b : α) := a * b⁻¹ ∈ N

section norm_equiv
open is_subgroup coset_notation
variables [group α] (N : set α) [hn : is_normal_subgroup N] (a : α)
include hn

lemma norm_equiv_mul {a₁ a₂ b₁ b₂ : α} (ha : norm_equiv N a₁ a₂) (hb : norm_equiv N b₁ b₂)
    : norm_equiv N (a₁ * b₁) (a₂ * b₂) :=
    begin
    simp [norm_equiv] at *,
    have h : (a₁ * N) * a₂⁻¹ = N, {
        calc
            (a₁ * N) * a₂⁻¹ = (N * a₁) * a₂⁻¹   : by rw iff.elim_left (normal_iff_eq_cosets N) hn
            ...             = N * (a₁ * a₂⁻¹)   : by rw rcoset_assoc
            ...             = N                 : by rw rcoset_mem_rcoset N (a₁ * a₂⁻¹) (ha)
    },
    rw ←h,
    calc
        a₁ * b₁ * (b₂⁻¹ * a₂⁻¹) = a₁ * (b₁ * b₂⁻¹) * a₂⁻¹   : by simp
        ...                     ∈ (a₁ * N) * a₂⁻¹           : mem_rcoset a₂⁻¹ (mem_lcoset a₁ hb)
    end

end norm_equiv

lemma norm_equiv_rel (N : set α) [is_normal_subgroup N] : equivalence (norm_equiv N) :=
⟨ λ x, calc
        x * x⁻¹ = (1 : α) : mul_right_inv x
        ... ∈ N           : one_mem N,
    λ x y hxy, calc
      y * x⁻¹ = (x * y⁻¹)⁻¹         : by simp
      ...     ∈ N                   : inv_mem hxy,
    λ x y z hxy hyz, calc
      x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) : by rw [mul_assoc, inv_mul_cancel_left y z⁻¹]
      ...   ∈ N                       : mul_mem hxy hyz ⟩

definition quotient_group_setoid {α} [group α] (N : set α) [is_normal_subgroup N] : setoid α := {
    r := norm_equiv N,
    iseqv := norm_equiv_rel N
}

attribute [instance] quotient_group_setoid

def quotient_group {α} [group α] (N : set α) [h : is_normal_subgroup N] := quotient (quotient_group_setoid N)

notation G `/` N := quotient_group N



-- instance quotient_group_is_group {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] : group (G / N) := {
--     mul := quotient.lift₂ (λ x y : α, ⟦x*y⟧) (λ x₁ x₂ y₁ y₂ h₁ h₂, quot.sound $
--     calc
--         (x₁ * x₂) * (y₁ * y₂)⁻¹ = x₁ * x₂ * (y₂⁻¹ * y₁⁻¹)   : by rw [mul_inv_rev y₁ y₂]
--         ...                     = x₁ * (x₂ * y₂⁻¹) * y₁⁻¹   : by rw [←mul_assoc, mul_assoc x₁]
--         ...                     = x₁ * y₁⁻¹ * (x₂ * y₂⁻¹)   : 
--         ...                     ∈ N                         : sorry
    
-- }


end quotient_group

open is_subgroup
open quotient_group
open function

structure group_isomorphism (β : Type v) (γ : Type w) [group β] [group γ]
  extends equiv β γ :=
(hom_fun : is_hom to_fun)

infix ` ≃ₕ `:50 := group_isomorphism

def image' { α β } ( φ : α → β ) := φ '' univ


theorem fake_isomorphism_theorem {α} ( G : group α ) ( H : group α ) { φ : α → α } ( h : is_hom φ ) : (image' φ) ≃ₕ (kernel h) := sorry

theorem first_isomorphism_theorem {α β} ( G : group α ) ( H : group β ) { φ : α → β } ( h : is_hom φ ) : (image' φ) ≃ₕ quotient_group (set.univ) (kernel h) := sorry
