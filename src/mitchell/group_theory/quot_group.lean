
import data.set.basic init.function data.equiv init.logic 
import mitchell.group_theory.coset mitchell.group_theory.subgroup

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open set

namespace quotient_group
open is_subgroup coset_notation
variable [group α]

def norm_equiv (N : set α) (a b : α) := a * b⁻¹ ∈ N

section norm_equiv
open is_subgroup coset_notation
variables [hg : group α] (N : set α) [hn : is_normal_subgroup N] (a : α)
include hn hg

lemma norm_equiv_rel : equivalence (norm_equiv N) :=
⟨ λ x, calc
        x * x⁻¹ = (1 : α) : mul_right_inv x
        ... ∈ N           : one_mem N,
    λ x y hxy, calc
      y * x⁻¹ = (x * y⁻¹)⁻¹         : by simp
      ...     ∈ N                   : inv_mem hxy,
    λ x y z hxy hyz, calc
      x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) : by rw [mul_assoc, inv_mul_cancel_left y z⁻¹]
      ...   ∈ N                       : mul_mem hxy hyz ⟩

lemma norm_equiv_rfl (a : α) : norm_equiv N a a := (norm_equiv_rel N).left a

lemma norm_equiv_symm {a b} (h : norm_equiv N a b) : norm_equiv N b a := (norm_equiv_rel N).right.left h

lemma norm_equiv_trans {a b c} (hab : norm_equiv N a b) (hbc : norm_equiv N b c) : norm_equiv N a c := 
    (norm_equiv_rel N).right.right hab hbc

lemma norm_equiv_mul {a₁ a₂ b₁ b₂ : α} (ha : norm_equiv N a₁ a₂) (hb : norm_equiv N b₁ b₂)
    : norm_equiv N (a₁ * b₁) (a₂ * b₂) :=
    begin
    simp [norm_equiv] at *,
    have h : (a₁ * N) * a₂⁻¹ = N, {
        calc
            (a₁ * N) * a₂⁻¹ = (N * a₁) * a₂⁻¹   : by rw iff.elim_left (normal_iff_eq_cosets N) hn
            ...             = N * (a₁ * a₂⁻¹)   : by rw rcoset_assoc
            ...             = N                 : by rw [rcoset_mem_rcoset N ha]; assumption
    },
    rw ←h,
    calc
        a₁ * b₁ * (b₂⁻¹ * a₂⁻¹) = a₁ * (b₁ * b₂⁻¹) * a₂⁻¹   : by rw [mul_assoc, ←mul_assoc b₁, ←mul_assoc]
        ...                     ∈ (a₁ * N) * a₂⁻¹           : mem_rcoset a₂⁻¹ (mem_lcoset a₁ hb)
    end

lemma norm_equiv_inv {a₁ a₂ : α} (h : norm_equiv N a₁ a₂) : norm_equiv N a₁⁻¹ a₂⁻¹ :=
begin
    apply norm_equiv_symm N,
    simp [norm_equiv] at *,
    exact mem_norm_comm h
end

end norm_equiv

definition quotient_group_setoid {α} [group α] (N : set α) [is_normal_subgroup N] : setoid α := {
    r := norm_equiv N,
    iseqv := norm_equiv_rel N
}

attribute [instance] quotient_group_setoid

def quotient_group {α} [group α] (N : set α) [h : is_normal_subgroup N] := quotient (quotient_group_setoid N)

notation G `/` N := quotient_group N

lemma quotient_group_is_group {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] : group (G / N) := {
    one := ⟦ 1 ⟧,
    mul := quotient.lift₂ (λ x y : α, ⟦x*y⟧) (λ x₁ x₂ y₁ y₂ h₁ h₂, quot.sound (norm_equiv_mul N h₁ h₂)),
    inv := quotient.lift  (λ x : α, ⟦x⁻¹⟧)   (λ x₁ x₂ h, quot.sound (norm_equiv_inv N h)),
    mul_assoc := λ x y z, quotient.induction_on₂ x y (λ x y, quotient.induction_on z
        (λ z, show ⟦ x * y * z ⟧ = ⟦ x * (y * z) ⟧, by rw mul_assoc)),
    mul_one := λ x, quotient.induction_on x (λ x, show ⟦ x * 1 ⟧ = ⟦ x ⟧, by rw mul_one),
    one_mul := λ x, quotient.induction_on x (λ x, show ⟦ 1 * x ⟧ = ⟦ x ⟧, by rw one_mul),
    mul_left_inv := λ x, quotient.induction_on x (λ x, show ⟦ x⁻¹ * x ⟧ = ⟦ 1 ⟧, by rw mul_left_inv)
}

attribute [instance] quotient_group_is_group

end quotient_group

open is_subgroup
open quotient_group
open function
open is_hom

section extend
variables [group α] [group β]

def image' ( f : α → β ) := f '' univ

variables {N : set α} [hs : is_normal_subgroup N]
include hs

def q_em (a : α) := ⟦a⟧ 

variables {f : α → β} (resp_f : ∀ a₁ a₂, norm_equiv N a₁ a₂ → f a₁ = f a₂)

def extend : quotient_group N → β := quotient.lift f resp_f

lemma extend_quot (a : α) : extend resp_f ⟦a⟧ = f a := rfl

lemma extend_quot_comp : extend resp_f ∘ q_em = f := rfl

def extend_im : quotient_group N → image' f := λ x, quotient.lift_on x (λ x, ⟨f x, x, rfl⟩ : α → image' f)

end extend

section

theorem fun_resp_ker [group α] [group β] (f : α → β) [hf : is_hom f] : ∀ a₁ a₂, norm_equiv (hf.kernel) a₁ a₂ → f a₁ = f a₂ := sorry

structure group_isomorphism (β : Type v) (γ : Type w) [group β] [group γ]
  extends equiv β γ :=
(hom_fun : is_hom to_fun)

infix ` ≃ₕ `:50 := group_isomorphism

lemma image'_group [G : group α] [H : group β] (f : α → β) [h : is_hom f] : group (image' f) := 
    @subgroup_group β H (image' f) (@image_in α β G H f h univ univ_in)

attribute [instance] image'_group

end

-- set_option trace.class_instances true

-- instance {α β} ( G : group α ) ( H : group β ) { f : α → β } ( h : is_hom f ) : group (f '' univ) := @is_subgroup.subgroup_group β H (f '' univ) (@image_in α β G H f h univ univ_in)

#print subgroup_group

theorem first_isomorphism_theorem {α β} [G : group α] [H : group β] (f : α → β ) [h : is_hom f] 
    : @group_isomorphism (quotient_group h.kernel) (image' f) _ (@image'_group _ _ _ _ f h) := {
        to_fun := 
    }