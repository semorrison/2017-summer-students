
import data.set.basic init.function data.equiv init.logic 
import mitchell.group_theory.coset mitchell.group_theory.subgroup

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open set

namespace quotient_group
open is_subgroup coset_notation

def norm_equiv [group α] (N : set α) (a b : α) := a * b⁻¹ ∈ N

section norm_equiv
open is_subgroup coset_notation
-- Check that all of these lemmas need all of these variables
variables [group α] [hg : group α] (N : set α) [hn : is_normal_subgroup N] (a : α)
include hn hg

local notation a `∼` b := norm_equiv N a b

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

lemma norm_equiv_symm {a b} (h : a ∼ b) : b ∼ a := (norm_equiv_rel N).right.left h

lemma norm_equiv_trans {a b c} (hab : a ∼ b) (hbc : b ∼ c) : a ∼ c := 
    (norm_equiv_rel N).right.right hab hbc

lemma norm_equiv_mul {a₁ a₂ b₁ b₂ : α} (ha : a₁ ∼ a₂) (hb : b₁ ∼ b₂)
    : (a₁ * b₁) ∼ (a₂ * b₂) :=
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

lemma norm_equiv_inv {a₁ a₂ : α} (h : a₁ ∼ a₂) : a₁⁻¹ ∼ a₂⁻¹ :=
begin
    apply norm_equiv_symm N,
    simp [norm_equiv] at *,
    exact mem_norm_comm h
end

end norm_equiv

definition quotient_group_setoid [group α] (N : set α) [is_normal_subgroup N] : setoid α := {
    r := norm_equiv N,
    iseqv := norm_equiv_rel N
}

attribute [instance] quotient_group_setoid

def quotient_group (α) [group α] (N : set α) [h : is_normal_subgroup N] := quotient (quotient_group_setoid N)

notation G `/` N := quotient_group G N

instance quotient_group_is_group {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] : group (quotient (quotient_group_setoid N)) := {
    one := ⟦ 1 ⟧,
    mul := quotient.lift₂ (λ x y : α, ⟦x*y⟧) (λ x₁ x₂ y₁ y₂ h₁ h₂, quot.sound (norm_equiv_mul N h₁ h₂)),
    inv := quotient.lift  (λ x : α, ⟦x⁻¹⟧)   (λ x₁ x₂ h, quot.sound (norm_equiv_inv N h)),
    mul_assoc := λ x y z, quotient.induction_on₂ x y (λ x y, quotient.induction_on z
        (λ z, show ⟦ x * y * z ⟧ = ⟦ x * (y * z) ⟧, by rw mul_assoc)),
    mul_one := λ x, quotient.induction_on x (λ x, show ⟦ x * 1 ⟧ = ⟦ x ⟧, by rw mul_one),
    one_mul := λ x, quotient.induction_on x (λ x, show ⟦ 1 * x ⟧ = ⟦ x ⟧, by rw one_mul),
    mul_left_inv := λ x, quotient.induction_on x (λ x, show ⟦ x⁻¹ * x ⟧ = ⟦ 1 ⟧, by rw mul_left_inv)
}

instance quotient_group_is_group₁ {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] : group (α / N) := quotient_group.quotient_group_is_group N

@[simp] lemma quot_mul {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] (a b : α)
    : ⟦ a ⟧ * ⟦ b ⟧ = ⟦ a * b ⟧ := rfl
@[simp] lemma quot_inv {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] (a b : α)
    : ⟦ a ⟧⁻¹ = ⟦ a⁻¹ ⟧ := rfl
@[simp] lemma quot_one {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] (a b : α)
    : 1 = ⟦ (1:α) ⟧ := rfl

section

def image [group α] [group β] ( f : α → β ) : set β := f '' univ
lemma image_mem [group α] [group β] (f : α → β) (a : α) : f a ∈ image f := ⟨a, mem_univ a, rfl⟩

instance univ_image_in [group α] [group β] (f : α → β) [hf: is_hom f] : group (image f) :=  
    is_subgroup.subgroup_group (@is_hom.image_in _ _ _ _ _ hf univ _)

structure group_isomorphism (β : Type v) (γ : Type w) [group β] [group γ]
  extends equiv β γ :=
(hom_fun : is_hom to_fun)

infix ` ≃ₕ `:50 := group_isomorphism

def qgroup_lift [G : group α] [H : group β] (N : set α) [hs : is_normal_subgroup N] {f : α → β} (hf : is_hom f) (h : ∀ x ∈ N, f x = 1) (q : α / N) : β :=
quot.lift_on q f $ assume a b (hab : a * b⁻¹ ∈ N),
  have f a * (f b)⁻¹ = 1, by rw [←hf.inv, ←hf.hom_mul]; exact h _ hab,
  show f a = f b, by rw [←inv_inv (f b)]; exact eq_inv_of_mul_eq_one this

@[simp] lemma mul_val [group α] [group β] ( f : α → β ) (a b : image f) [hf : is_hom f] : (a * b).val = a.val * b.val := by cases a; cases b; refl
@[simp] lemma one_val [group α] [group β] ( f : α → β ) [hf : is_hom f] : (1 : image f).val = 1 := rfl
@[simp] lemma inv_val [group α] [group β] ( f : α → β ) (a : image f) [hf : is_hom f] : (a⁻¹).val = a.val⁻¹ := by cases a; refl

def im_lift [G : group α] [H : group β] {f : α → β} (hf : is_hom f) (c : α) : image f := ⟨f c, image_mem f c⟩

@[simp] lemma im_lift_val [G : group α] [H : group β] {f : α → β} (hf : is_hom f) (c : α) : (im_lift hf c).val = f c := rfl

lemma is_hom_image [G : group α] [H : group β] {f : α → β} (hf : is_hom f) : is_hom (λ c, im_lift hf c : α → image f) :=
    by refine {..};  intros; apply subtype.eq; simp [im_lift, hf.hom_mul]

lemma ker_equiv_im [G : group α] [H : group β] (f : α → β ) [h : is_hom f] : ∀ a b, (norm_equiv h.kernel) a b → f a = f b := begin
    intros a b hab,
    simp [norm_equiv] at hab,
    exact is_hom.one_ker_inv h hab
end

lemma ker_equiv_im_lift [G : group α] [H : group β] (f : α → β ) [h : is_hom f] 
    : ∀ a b, (norm_equiv h.kernel) a b → (im_lift h) a = (im_lift h) b := by simp [im_lift]; exact ker_equiv_im f

noncomputable theorem first_isomorphism_theorem [G : group α] [H : group β] (f : α → β ) [h : is_hom f]
    : α / h.kernel ≃ₕ image f := {
        to_fun := qgroup_lift h.kernel (is_hom_image h) (assume x hx, subtype.eq $ by simp [im_lift]; exact is_hom.mem_ker_one _ hx),
        inv_fun := λ b, @quotient.mk _ (quotient_group_setoid _) (classical.some b.2),
        left_inv := assume b', @quotient.induction_on _ (quotient_group_setoid _) _ b' $
            begin
                assume b,
                apply quotient.sound,
                simp [im_lift, qgroup_lift],
                have hz := @classical.some_spec _ (λ z, f z = f b) ⟨b, rfl⟩,
                unfold has_equiv.equiv,
                unfold setoid.r,
                unfold norm_equiv,
                simp,
                apply is_hom.inv_ker_one h hz,
            end,
        right_inv := 
            begin
                simp [function.right_inverse, function.left_inverse],
                intros x hx,
                apply subtype.eq,
                simp,
                induction hx,
                induction hx_h,
                induction hx_h_right,
                dsimp,
                let func := @classical.indefinite_description α (λ (a : α), f a = f hx_w) _,
                have p : @quotient.mk  _ (quotient_group_setoid _) func.val = @quotient.mk  _ (quotient_group_setoid _) (hx_w), {
                  apply quotient.sound,
                  dsimp [has_equiv.equiv, setoid.r],
                  apply is_hom.inv_ker h func.property
                },
                simp [func] at p,
                simp [classical.some],
                rw p,
                simp [qgroup_lift],
                apply quot.lift_beta f (ker_equiv_im f),
            end,
        hom_fun := ⟨λ x y, (@quotient.induction_on₂ _ _ (quotient_group_setoid _) (quotient_group_setoid _) _ x y (
            begin
                intros,
                rw [quot_mul],
                simp [qgroup_lift, quot.lift_on, quotient.mk],
                apply subtype.eq,
                simp [h.hom_mul]
            end))⟩
    }
end

end quotient_group