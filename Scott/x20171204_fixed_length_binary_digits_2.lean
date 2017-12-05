import data.vector
import .x20171204_lemmas

definition fixed_length_binary_digits : Π (L : ℕ) (n : fin (2^L)), vector bool L
| 0     _ := vector.nil
| (l+1) n := (n.val % 2 = 1) :: (fixed_length_binary_digits l ⟨ n.val/2 , begin rw nat.div_lt_iff_lt_mul, exact n.is_lt, exact dec_trivial  end ⟩ )

definition add_fin_fin {k₁ k₂ : ℕ} (m₁ : fin k₁) (m₂ : fin k₂) : fin (k₁ + k₂ - 1) :=
⟨ 
  m₁.val + m₂.val,
  begin
    admit
  end
⟩

definition mul_nat_fin (n : ℕ) {k: ℕ} (m : fin k) : fin (n * (k - 1) + 1) := 
⟨
  n * m.val, 
  begin
    have q := m.is_lt,
    have q' : m.val ≤ k - 1, admit,
    have q'' := nat.mul_le_mul_left n q', 
    exact nat.lt_succ_of_le q''
  end
⟩ 

lemma nat.div_le_div {n m : ℕ}  (h : n ≤ m) (d : ℕ) : n/d ≤ m/d := sorry

definition div_fin_nat {k : ℕ} (m : fin k) (d : ℕ) : fin ((k-1) / d + 1) :=
⟨
  m.val / d,
  begin
    have q := m.is_lt,
    have q' : m.val ≤ k - 1, admit,
    have q'' := nat.div_le_div q' d,
    exact nat.lt_succ_of_le q''
  end
⟩ 


definition fin_of_bool (b : bool) : fin 2 := ⟨ cond b 1 0, begin induction b, exact dec_trivial, exact dec_trivial, end ⟩ 

lemma r1 (l : ℕ) : (2 + (2 * (2^(l + 1 - 1) - 1) + 1) - 1) = 2^(l+1) :=
begin
admit
end

lemma r2 (l : ℕ) : ((2^(l + 1) - 1) / 2 + 1) = 2^l := sorry

definition from_fixed_length_binary_digits : Π { L : ℕ } ( v : vector bool L ), fin (2^L) 
| 0     _ := ⟨ 0, dec_trivial ⟩ 
| (l+1) v := begin
               have q := add_fin_fin (fin_of_bool v.head) (mul_nat_fin 2 (from_fixed_length_binary_digits v.tail)),
               rw r1 at q,
               exact q
             end

lemma fixed_length_binary_digits_correct : Π (L : ℕ) (n : fin (2^L)), from_fixed_length_binary_digits (fixed_length_binary_digits L n) = n
| 0 (⟨ n, p ⟩) := begin
             unfold fixed_length_binary_digits,
             unfold from_fixed_length_binary_digits,
             apply fin.eq_of_veq,
             simp,     
             have q : n = 0, { norm_num at p, cases p, refl, cases a },
             rw q,
           end
| (l+1) (⟨ n, p ⟩) := begin
                 -- we unfold some definitions and simplify vector.head and vector.tail
                 unfold fixed_length_binary_digits,
                 unfold from_fixed_length_binary_digits,
                 rw [ vector.head_cons, vector.tail_cons ], -- TODO why aren't these marked as simp?
                 -- and then use induction
                --  let d := div_fin_nat ⟨ n, p ⟩ 2,
                --  rw r2 at d,
                 rw fixed_length_binary_digits_correct l _,
                 apply fin.eq_of_veq,
                 simp,
                 unfold add_fin_fin,
                 unfold mul_nat_fin,
                 unfold fin_of_bool,
                 simp,
                 admit
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
