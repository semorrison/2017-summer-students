
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

lemma quotient_group_is_group {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] : group (α / N) := {
    one := ⟦ 1 ⟧,
    mul := quotient.lift₂ (λ x y : α, ⟦x*y⟧) (λ x₁ x₂ y₁ y₂ h₁ h₂, quot.sound (norm_equiv_mul N h₁ h₂)),
    inv := quotient.lift  (λ x : α, ⟦x⁻¹⟧)   (λ x₁ x₂ h, quot.sound (norm_equiv_inv N h)),
    mul_assoc := λ x y z, quotient.induction_on₂ x y (λ x y, quotient.induction_on z
        (λ z, show ⟦ x * y * z ⟧ = ⟦ x * (y * z) ⟧, by rw mul_assoc)),
    mul_one := λ x, quotient.induction_on x (λ x, show ⟦ x * 1 ⟧ = ⟦ x ⟧, by rw mul_one),
    one_mul := λ x, quotient.induction_on x (λ x, show ⟦ 1 * x ⟧ = ⟦ x ⟧, by rw one_mul),
    mul_left_inv := λ x, quotient.induction_on x (λ x, show ⟦ x⁻¹ * x ⟧ = ⟦ 1 ⟧, by rw mul_left_inv)
}

section

attribute [instance] quotient_group_is_group


def image [group α] [group β] ( f : α → β ) : set β := {x | ∃ y, f y = x}
lemma image_mem [group α] [group β] (f : α → β) (a : α) : f a ∈ image f := by sorry

instance [group α] [group β] ( f : α → β ) : has_mul (image f) := sorry
instance [group α] [group β] ( f : α → β ) : has_one (image f) := sorry
instance [group α] [group β] ( f : α → β ) : has_inv (image f) := sorry

@[simp] lemma mul_val [group α] [group β] ( f : α → β ) (a b : image f) : (a * b).val = a.val * b.val := sorry
@[simp] lemma one_val [group α] [group β] ( f : α → β ) : (1 : image f).val = 1 := sorry
@[simp] lemma inv_val [group α] [group β] ( f : α → β ) (a : image f) : (a⁻¹).val = a.val⁻¹ := sorry

lemma univ_image_in [group α] [group β] (f : α → β) [hf: is_hom f] : group (image f) := 
    by refine {mul := (*), one := 1, inv := has_inv.inv, ..};
        { intros, apply subtype.eq, simp [mul_assoc]}
    
attribute [instance] univ_image_in

structure group_isomorphism (β : Type v) (γ : Type w) [group β] [group γ]
  extends equiv β γ :=
(hom_fun : is_hom to_fun)

infix ` ≃ₕ `:50 := group_isomorphism

def ker_quot_lift [G : group α] [H : group β] {f : α → β} (hf : is_hom f) (q : α / hf.kernel) : β :=
quot.lift_on q f (begin
intros a b hs,
simp [setoid.r, norm_equiv] at hs,
simp [hf.hom_mul, hf.inv] at hs,
rw ←inv_inv (f b),
apply eq_inv_of_mul_eq_one hs
end)

noncomputable theorem first_isomorphism_theorem [G : group α] [H : group β] (f : α → β ) [h : is_hom f]
    : α / h.kernel ≃ₕ image f := {
        to_fun := ker_quot_lift h
    }

end

end quotient_group

-- After this point it just becomes a mess

-- instance quotient_group_mul {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] : has_mul (quotient (quotient_group_setoid N)) := sorry


/-

lemma quot_mul_norm {α} [G : group α] (N : set α) [hs : is_normal_subgroup N] {a b : α} 
    : @group.mul _ (quotient_group_is_group N) (@quotient.mk _ (quotient_group_setoid N) a) (@quotient.mk _ (quotient_group_setoid N) b) =
    (@quotient.mk _ (quotient_group_setoid N) (a * b))
    := sorry




open is_subgroup
open quotient_group
open function
open is_hom

def image [group α] [group β] ( f : α → β ) := f '' univ
lemma image_mem [group α] [group β] (f : α → β) (a : α) : f a ∈ image f := by sorry

section

-- theorem fun_resp_ker [group α] [group β] (f : α → β) [hf : is_hom f] : ∀ a₁ a₂, norm_equiv (hf.kernel) a₁ a₂ → f a₁ = f a₂ := sorry



lemma image'_group [G : group α] [H : group β] (f : α → β) [h : is_hom f] : group (image f) := 
    @subgroup_group β H (image f) (@image_in α β G H f h univ univ_in)

attribute [instance] image'_group

end

-- set_option trace.class_instances true

-- instance {α β} ( G : group α ) ( H : group β ) { f : α → β } ( h : is_hom f ) : group (f '' univ) := @is_subgroup.subgroup_group β H (f '' univ) (@image_in α β G H f h univ univ_in)

#print subgroup_group

-- set_option pp.implicit true
-- protected eliminator eq.rec : Π {α : Sort u} {a : α} {C : α → Sort l}, C a → Π {a_1 : α}, a = a_1 → C a_1

@[simp] lemma {u₁ u₂} parallel_transport_for_trivial_bundles {α : Sort u₁} {a b : α} {β : Sort u₂} (p : a = b) (x : β) : @eq.rec α a (λ a, β) x b p = x :=
begin
induction p,
simp,
end

lemma kernel_cosets {α β} [G : group α] [H : group β] (f : α → β ) [h : is_hom f] {a b} (hab : f a = f b) 
    : @quotient.mk _ (quotient_group_setoid h.kernel) a = @quotient.mk _ (quotient_group_setoid h.kernel) b :=
begin
apply quot.sound,
unfold setoid.r,
unfold norm_equiv,
simp,
sorry -- easy
end

variable {r : α → α → Prop}
variable {S : quot r → Sort v}

lemma quot.rec_eq
   (f : Π a, S (quot.mk r a)) (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (quot.sound p) : S (quot.mk r b)) = f b)
   (a : α) : @quot.rec α r S f h (quot.mk r a) = f a := by refl

noncomputable theorem first_isomorphism_theorem {α β} [G : group α] [H : group β] (f : α → β ) [h : is_hom f] 
    : @group_isomorphism (α / h.kernel) (image f) _ (@image'_group _ _ _ _ f h) := {
        to_fun := 
        begin 
                    intros, 
                    induction a,
                    split, 
                    exact image_mem f a, 
                    simp, 
                    induction a_p,
                    rw [h.hom_mul, h.inv] at a_p,
                    simp [eq_mul_inv_of_mul_eq a_p],
                    exfalso,
                    rw mem_empty_eq at a_p,
                    assumption
        end,
        inv_fun :=
        begin
            intros,
            induction a with b h,
            exact (@quotient.mk _ (quotient_group_setoid _) (classical.some h)),
        end,
        left_inv := begin
                        simp [left_inverse],
                        intro x,
                        induction x with y hy,
                        simp,
                        have hz := @classical.some_spec _ (λ z, f z = f y) ⟨y, rfl⟩,
                        exact @kernel_cosets _ _ _ _ f h _ _ hz,
                        simp,
                    end,
        right_inv := begin
                        
                        simp [function.right_inverse, left_inverse],
                        intros x hx,
                        apply subtype.eq,
                        simp,
                        induction hx,
                        induction hx_h,
                        induction hx_h_right,
                        dsimp,
                        have p : @quotient.mk  _ (quotient_group_setoid _) (@classical.some α (λ (a : α), f a = f hx_w) _) = @quotient.mk  _ (quotient_group_setoid _) (hx_w), {
                          sorry, -- not too hard
                        },
                        rw p,
                        erw quot.rec_eq,
                      end,
        hom_fun := {
            hom_mul := λ x y, (@quotient.induction_on₂ _ _ (quotient_group_setoid _) (quotient_group_setoid _) _ x y (begin
            intros,
            erw [quot.rec_eq, quot.rec_eq],
            sorry
            end))
        }
    }

-/

