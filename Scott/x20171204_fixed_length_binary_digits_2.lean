import data.vector
import .x20171204_lemmas

definition fixed_length_binary_digits : Π (L : ℕ) (n : fin (2^L)), vector bool L
| 0     _ := vector.nil
| (l+1) n := (n.val % 2 = 1) :: (fixed_length_binary_digits l ⟨ n.val/2 , sorry ⟩ )

definition from_fixed_length_binary_digits : Π { L : ℕ } ( v : vector bool L ), fin (2^L) 
| 0     _ := ⟨ 0, sorry ⟩ 
| (l+1) v := ⟨ cond v.head 1 0 + 2 * (from_fixed_length_binary_digits v.tail).val, sorry ⟩ 

lemma fixed_length_binary_digits_correct : Π (L : ℕ) (n : fin (2^L)), from_fixed_length_binary_digits (fixed_length_binary_digits L n) = n
| 0 (⟨ n, p ⟩) := begin
             have q : n = 0, { norm_num at p, cases p, refl, cases a },
             rw q,
             refl 
           end
| (l+1) (⟨ n, p ⟩) := begin
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
