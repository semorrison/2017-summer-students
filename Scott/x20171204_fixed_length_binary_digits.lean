import data.vector
import .x20171204_lemmas

definition fixed_length_binary_digits : Π (L : ℕ) (n : ℕ), vector bool L
| 0     _ := vector.nil
| (l+1) n := (n % 2 = 1) :: (fixed_length_binary_digits l (n/2))

definition from_fixed_length_binary_digits : Π { L : ℕ } ( v : vector bool L ), ℕ 
| 0     _ := 0
| (l+1) v := cond v.head 1 0 + 2 * (from_fixed_length_binary_digits v.tail)

lemma fixed_length_binary_digits_correct : Π (L : ℕ) (n : ℕ) (p : n < 2^L), from_fixed_length_binary_digits (fixed_length_binary_digits L n) = n
| 0 n p := begin
             have q : n = 0, { norm_num at p, cases p, refl, cases p_a },
             rw q,
             refl 
           end
| (l+1) n p := begin
                 -- we unfold some definitions and simplify vector.head and vector.tail
                 unfold fixed_length_binary_digits,
                 unfold from_fixed_length_binary_digits,
                 rw [ vector.head_cons, vector.tail_cons ], -- TODO why aren't these marked as simp?
                 -- and then use induction
                 rw fixed_length_binary_digits_correct l (n/2),
                 -- finally we have to discharge two annoying conditions.
                 { simp, exact p2 n },
                 {
                   rw nat.div_lt_iff_lt_mul,
                   exact p,
                   exact dec_trivial
                 }
               end

lemma p4 (b : bool) (x y n : ℕ) : cond b x y / n = cond b (x / n) (y / n) :=
begin
induction b,
simp, simp
end
lemma p5 (b : bool) : to_bool (cond b 1 0 % 2 = 1) = b :=
begin
induction b, simp, simp, refl
end

lemma to_bool_decidable_congr (p : Prop) (h₁ h₂ : decidable p) : @to_bool p h₁ = @to_bool p h₂ := by congr

lemma p6 (b : bool) (h : decidable (cond b 1 0 % 2 = 1)) : @to_bool (cond b 1 0 % 2 = 1) h = b :=
begin
rw to_bool_decidable_congr,
exact p5 b,
end

lemma fixed_length_binary_digits_correct' : Π (L : ℕ) (v : vector bool L), fixed_length_binary_digits L (from_fixed_length_binary_digits v) = v :=
begin
intros,
induction L with a ih,
unfold fixed_length_binary_digits,
rw vector.eq_nil v,

unfold fixed_length_binary_digits,
unfold from_fixed_length_binary_digits,
simp,
rw nat.add_mul_div_left,
have p : (cond v.head 1 0) / 2 = 0, { rw p4, simp, have r : 1/2 = 0, exact dec_trivial, rw r, simp },
rw p,
simp,
rewrite ih v.tail,
clear ih p,
rw p6 v.head, -- to_bool takes an implicit decidable instance, which we have to work around here!
apply vector.cons_head_tail,
-- finally, discharge an easy condition:
exact dec_trivial
end

lemma from_binary_digits_bound : Π { L : ℕ } ( v : vector bool L ), from_fixed_length_binary_digits v < 2^L :=
begin
  intros,
  induction L,
  unfold from_fixed_length_binary_digits,
  exact dec_trivial,
  unfold from_fixed_length_binary_digits,
  have p := L_ih v.tail,
  admit
end

definition fin_of_binary_digits { L : ℕ } ( v : vector bool L ) : fin (2^L) :=
⟨
  from_fixed_length_binary_digits v,
  from_binary_digits_bound v
⟩

structure Bijection ( U V : Type ) :=
  ( morphism : U → V )
  ( inverse  : V → U )
  ( witness_1 : ∀ u : U, inverse (morphism u) = u )
  ( witness_2 : ∀ v : V, morphism (inverse v) = v )

class Finite ( α : Type ) :=
  ( cardinality : nat )
  ( bijection : Bijection α (fin cardinality) )

definition binary_list_cardinality {n : ℕ} : Finite (vector bool n) := {
  cardinality := 2^n,
  bijection   := {
    morphism := fin_of_binary_digits,
    inverse  := λ p, fixed_length_binary_digits n p.val,
    witness_1 := begin
                   unfold fin_of_binary_digits, 
                   simp, 
                   exact fixed_length_binary_digits_correct' n
                 end,
    witness_2 := begin 
                   unfold fin_of_binary_digits, 
                   intros, 
                   apply fin.eq_of_veq, 
                   simp, 
                   exact fixed_length_binary_digits_correct n v.val v.is_lt
                 end
  }
}


definition compose_bijections { U V W : Type } ( f : Bijection U V ) ( g : Bijection V W ) : Bijection U W :=
{
  morphism := g.morphism ∘ f.morphism,
  inverse := f.inverse ∘ g.inverse,
  witness_1 := begin intros, unfold function.comp, rw g.witness_1, rw f.witness_1, end,
  witness_2 := begin intros, unfold function.comp, rw f.witness_2, rw g.witness_2, end,
}

definition decidable_set (α : Type) := Σ X : set α, decidable_pred X

definition powerset_bijection {n : ℕ} : Bijection (decidable_set (fin n)) (vector bool n)  := {
  morphism := λ v, ⟨ sorry, sorry ⟩,
  inverse  := sorry,
  witness_1 := sorry,
  witness_2 := sorry
}

definition powerset_finite {n : ℕ} : Finite (decidable_set (fin n)) := {
  cardinality := 2^n,
  bijection   := compose_bijections powerset_bijection binary_list_cardinality.bijection
}