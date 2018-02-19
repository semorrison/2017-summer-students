
import data.set.basic init.function data.equiv init.logic 
import mitchell.group_theory.coset mitchell.group_theory.subgroup

universes u v
variables {G : Type u} {H : Type v}

open set

namespace quotient_group
open subgroup coset_notation

def norm_equiv [group G] (N : set G) (a b : G) := a * b⁻¹ ∈ N

section norm_equiv
variables [group G] [group G] (N : set G) [normal_subgroup N]

local notation a `∼` b := norm_equiv N a b

lemma norm_equiv_rel : equivalence (norm_equiv N) :=
⟨ λ x, calc
        x * x⁻¹ = (1 : G) : mul_right_inv x
        ... ∈ N           : one_mem N,
    λ x y hxy, calc
      y * x⁻¹ = (x * y⁻¹)⁻¹         : by simp
      ...     ∈ N                   : inv_mem hxy,
    λ x y z hxy hyz, calc
      x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) : by rw [mul_assoc, inv_mul_cancel_left y z⁻¹]
      ...   ∈ N                       : mul_mem hxy hyz ⟩

lemma norm_equiv_rfl (a : G) : norm_equiv N a a := (norm_equiv_rel N).left a

lemma norm_equiv_symm {a b} (h : a ∼ b) : b ∼ a := (norm_equiv_rel N).right.left h

lemma norm_equiv_trans {a b c} (hab : a ∼ b) (hbc : b ∼ c) : a ∼ c := 
    (norm_equiv_rel N).right.right hab hbc

lemma norm_equiv_mul {a₁ a₂ b₁ b₂ : G} (ha : a₁ ∼ a₂) (hb : b₁ ∼ b₂)
    : (a₁ * b₁) ∼ (a₂ * b₂) :=
    begin
    simp [norm_equiv] at *,
    have h : (a₁ * N) * a₂⁻¹ = N, {
        calc
            (a₁ * N) * a₂⁻¹ = (N * a₁) * a₂⁻¹   : by rw normal_of_eq_cosets
            ...             = N * (a₁ * a₂⁻¹)   : by rw rcoset_assoc
            ...             = N                 : by rw [rcoset_mem_rcoset N ha]; assumption
    },
    rw ←h,
    calc
        a₁ * b₁ * (b₂⁻¹ * a₂⁻¹) = a₁ * (b₁ * b₂⁻¹) * a₂⁻¹   : by rw [mul_assoc, ←mul_assoc b₁, ←mul_assoc]
        ...                     ∈ (a₁ * N) * a₂⁻¹           : mem_rcoset a₂⁻¹ (mem_lcoset a₁ hb)
    end

lemma norm_equiv_inv {a₁ a₂ : G} (h : a₁ ∼ a₂) : a₁⁻¹ ∼ a₂⁻¹ :=
begin
    apply norm_equiv_symm N,
    simp [norm_equiv] at *,
    exact mem_norm_comm h
end

end norm_equiv

section quot_group
variables [group G]

instance (N : set G) [normal_subgroup N] : setoid G := {
    r := norm_equiv N,
    iseqv := norm_equiv_rel N
}

def quotient_group (G) [group G] (N : set G) [normal_subgroup N] := quotient (quotient_group.setoid N)

notation G `/` N := quotient_group G N

instance (N : set G) [normal_subgroup N] : group (quotient (quotient_group.setoid N)) :=  {
    one := ⟦ 1 ⟧,
    mul := quotient.lift₂ (λ x y : G, ⟦x*y⟧) (λ x₁ x₂ y₁ y₂ h₁ h₂, quot.sound (norm_equiv_mul N h₁ h₂)),
    inv := quotient.lift  (λ x : G, ⟦x⁻¹⟧)   (λ x₁ x₂ h, quot.sound (norm_equiv_inv N h)),
    mul_assoc := λ x y z, quotient.induction_on₂ x y (λ x y, quotient.induction_on z
        (λ z, show ⟦ x * y * z ⟧ = ⟦ x * (y * z) ⟧, by rw mul_assoc)),
    mul_one := λ x, quotient.induction_on x (λ x, show ⟦ x * 1 ⟧ = ⟦ x ⟧, by rw mul_one),
    one_mul := λ x, quotient.induction_on x (λ x, show ⟦ 1 * x ⟧ = ⟦ x ⟧, by rw one_mul),
    mul_left_inv := λ x, quotient.induction_on x (λ x, show ⟦ x⁻¹ * x ⟧ = ⟦ 1 ⟧, by rw mul_left_inv)
}

instance group₁ (N : set G) [normal_subgroup N] : group (G / N) := quotient_group.group N

@[simp] lemma quot_mul (N : set G) [normal_subgroup N] (a b : G) : ⟦ a ⟧ * ⟦ b ⟧ = ⟦ a * b ⟧ := rfl
@[simp] lemma quot_inv (N : set G) [normal_subgroup N] (a b : G) : ⟦ a ⟧⁻¹ = ⟦ a⁻¹ ⟧ := rfl
@[simp] lemma quot_one (N : set G) [normal_subgroup N] (a b : G) : 1 = ⟦ (1:G) ⟧ := rfl

end quot_group

class group_isomorphism (G : Type u) (H : Type v) [group G] [group H] extends equiv G H :=
    (hom_fun : group_hom to_fun)

infix `≅` :50 := group_isomorphism

section
open group_hom
variables [group G] [group H]

def image (f : G → H) : set H := f '' univ
lemma image_mem (f : G → H) (a : G) : f a ∈ image f := ⟨a, mem_univ a, rfl⟩

instance univ_image_in (f : G → H) [group_hom f] : group (image f) :=  
    @subgroup.group _ _ (image f) (@group_hom.image_in _ _ _ _ f _ univ subgroup.univ_in)

def qgroup_lift {N : set G} [normal_subgroup N] (f : G → H) [group_hom f] (h : ∀ x ∈ N, f x = 1) (q : G / N) : H :=
quotient.lift_on q f $ assume a b (hab : a * b⁻¹ ∈ N),
  have f a * (f b)⁻¹ = 1, by rw [←inv f, ←hom_mul f]; exact h _ hab,
  show f a = f b, by rw [←inv_inv (f b)]; exact eq_inv_of_mul_eq_one this

@[simp] lemma mul_val [group G] [group H] (f : G → H) (a b : image f) [hf : group_hom f] : (a * b).val = a.val * b.val := by cases a; cases b; refl
@[simp] lemma one_val [group G] [group H] ( f : G → H ) [hf : group_hom f] : (1 : image f).val = 1 := rfl
@[simp] lemma inv_val [group G] [group H] ( f : G → H ) (a : image f) [hf : group_hom f] : (a⁻¹).val = a.val⁻¹ := by cases a; refl

def im_lift (f : G → H) [group_hom f] (c : G) : image f := ⟨f c, image_mem f c⟩

@[simp] lemma im_lift_val (f : G → H) [group_hom f] (c : G) : (im_lift f c).val = f c := rfl

instance group_hom_image (f : G → H) [group_hom f] : group_hom (λ c, im_lift f c : G → image f) :=
    by refine {..};  intros; apply subtype.eq; simp [im_lift, hom_mul f]

lemma ker_equiv_im (f : G → H) [group_hom f] : ∀ a b, (norm_equiv (kernel f)) a b → f a = f b := begin
    intros a b hab,
    simp [norm_equiv] at hab,
    exact one_ker_inv hab
end

lemma ker_equiv_im_lift (f : G → H ) [group_hom f] 
    : ∀ a b, (norm_equiv (kernel f)) a b → (im_lift f) a = (im_lift f) b := by simp [im_lift]; exact ker_equiv_im f

noncomputable theorem first_isomorphism_theorem (f : G → H) [group_hom f]
    : G / kernel f ≅ image f := {
        to_fun := qgroup_lift (im_lift f) (assume x hx, subtype.eq $ by simp [im_lift]; exact mem_ker_one hx),
        inv_fun := λ b, ⟦classical.some b.property⟧,
        left_inv := assume b', quotient.induction_on b' $
            begin
                assume b,
                apply quotient.sound,
                simp [im_lift, qgroup_lift],
                have hz := @classical.some_spec _ (λ z, f z = f b) ⟨b, rfl⟩,
                unfold has_equiv.equiv,
                unfold setoid.r,
                unfold norm_equiv,
                simp,
                apply inv_ker_one hz,
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
                let func := @classical.indefinite_description G (λ (a : G), f a = f hx_w) _,
                have p : ⟦func.val⟧ = ⟦hx_w⟧, {
                  apply quotient.sound,
                  dsimp [has_equiv.equiv, setoid.r],
                  apply inv_ker func.property
                },
                simp [func] at p,
                simp [classical.some],
                rw p,
                simp [qgroup_lift],
                apply quot.lift_beta f (ker_equiv_im f),
            end,
        hom_fun := ⟨λ x y, (quotient.induction_on₂ x y $
            begin
                intros,
                rw [quot_mul],
                simp [qgroup_lift, quot.lift_on, quotient.mk],
                apply subtype.eq,
                simp [hom_mul f]
            end)⟩
    }
end

end quotient_group