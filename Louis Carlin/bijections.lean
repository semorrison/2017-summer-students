-- import tactic.norm_num

-- TODO
-- prove equivalent def of bijection?

-- Scott's definition 
class Bijection ( U V : Type ) :=
  ( morphism : U → V )
  ( inverse  : V → U )
  ( witness_1 : ∀ u : U, inverse (morphism u) = u )
  ( witness_2 : ∀ v : V, morphism (inverse v) = v )

class Finite ( α : Type ) := -- Finite set
  ( cardinality : nat )
  ( bijection : Bijection α (fin cardinality) )


def nat_id : nat → nat := λ n, n
#reduce nat_id 1

instance nat_nat_bijection : Bijection nat nat :=
{
    morphism := nat_id,
    inverse := nat_id,
    witness_1 :=
        begin 
            intro u,
            refl,
        end,
    witness_2 :=
        begin
            intro v,
            refl,
        end,
} 

def foo [bi : Bijection nat nat] : nat → nat := bi.morphism
#reduce foo 1 -- this requires Bijection to be a class not a structure

/-
def abs_value : int → nat 
| 0 := 0
| i := if (i<0) then abs_value (-i) else nat.succ (abs_value (i-1)) 
-- Describe a well-founded relation on the integers
-- |a| < |b|  (can't have reflexivity)

#reduce abs_value (-5)
-/

lemma geq_zero (u : nat) : (↑ u : int) ≥ 0 :=
begin
exact dec_trivial
end

#check nat.less_than_or_equal

#check lt_div_of_mul_lt
-- lemma geq_div_of_mul_lt



theorem bijection_composition {α β γ : Type}  [fab :Bijection α β] [fbg : Bijection β γ] : Bijection α γ :=
{
    morphism := λ x : α, @Bijection.morphism β γ fbg (@Bijection.morphism α β fab x),
    inverse := λ x : γ, @Bijection.inverse α β fab (@Bijection.inverse β γ fbg x),
    witness_1 := 
    begin
       intro,
       simp[@Bijection.witness_1], -- woah
    end,
    witness_2 := 
    begin
        intro,
        simp[@Bijection.witness_2],
    end
}

theorem bijection_reverse_order {α β : Type} [f : Bijection α β ] : Bijection β α :=
{
    morphism := f.inverse,
    inverse := f.morphism,
    witness_1 := f.witness_2,
    witness_2 := f.witness_1
}

-- int.mod_lt_of_pos
--/home/louis/school/2017/sem2/2017-summer-students/_target/deps/mathlib/data/int/basic.lean

#check nat.div_eq_of_lt


instance {n:ℕ} (h: n > 0): Bijection nat (nat × fin n) :=
{
    morphism := λ x : nat, ( x / n, ⟨ x % n, nat.mod_lt x h⟩ ),
    inverse := λ x : nat × fin n, x.1 * n + x.2.val,

    witness_1 := 
    begin
        intro,
        simp,
        rw mul_comm,
        simp[nat.mod_add_div ],
    end,

    witness_2 := 
    begin
        intro,
        simp,
        -- WTS (a + b*n) / n = a/n + b
        have h1 : v.snd.val/n = 0, from nat.div_eq_of_lt v.snd.is_lt, 
        have h2 : (v.snd.val + v.fst * n) / n = (v.snd).val/n + v.fst, from add_mul_div_left,
        rw [h2, h1, zero_add],
        have h3 : v.snd.val < n, from v.snd.is_lt,
        simp [nat.mod_eq_of_lt h3],
    end,
}

#check nat.mod_eq_of_lt

-- mod_eq_of_lt

-- int.mod_lt_of_pos


open int


instance int_natcrossfin_bijection : Bijection int (nat × fin 2) := {
    morphism := λ i : int, match i with 
                           | of_nat n := (n, ⟨0, dec_trivial⟩)
                           | neg_succ_of_nat n := (n, ⟨1, dec_trivial⟩ )
                           end,
    inverse := λ x : nat × fin 2, match x with
                            | (n, ⟨ 0 , _⟩ ) := of_nat n
                            | (n, ⟨ m, _⟩ ) := neg_succ_of_nat n -- why does this require you to match to m instead of realising 0 and 1 are the only cases?
                            end,
     -- see https://github.com/semorrison/lean-category-theory/blob/master/src/categories/util/finite.lean for an example of matching on fin n.
    witness_1 := 
                        begin
                            intro,
                            cases u,
                            simp [int_natcrossfin_bijection._match_1, int_natcrossfin_bijection._match_2],
                            simp [int_natcrossfin_bijection._match_1, int_natcrossfin_bijection._match_2],
                        end,
    witness_2 := sorry -- I am having trouble pattern matching with nat × fin 2 here
}


instance int_nat_bijection : Bijection int nat :=
begin
-- how do I get lean to work this out for itself with what I have
admit
end


-- set_option pp.all true

open classical

instance nat_int_bijection : Bijection nat int :=
{
    morphism := λ n : nat, if (2 ∣ n) then - (n/2) else (n+1)/2,
    inverse := λ i : int, if (i <= 0) then (nat_abs (2 * i)) else nat_abs (2*i - 1), -- how to convert int to nat
    witness_1 :=
        begin
            intro u,
            -- by_cases (2 ∣ u),
            -- {
            --     simp [h],
            -- }


            have h1 : 2 ∣ u ∨ ¬ 2 ∣ u, from em (2 ∣ u), 
            apply or.elim h1,
            {
                intro d,
                simp [d],
                have h2 : 0 ≤ (↑ u: int) , from geq_zero u,
                have h3 : 0 ≤ (↑ u: int)/2, from sorry,--div_le_div h1 h2 , -- int.le_div_iff_mul_le _,
                simp [h3],
                rw ← int.mul_div_assoc,
                rw int.mul_div_cancel_left,
                simp,
                norm_num,
                have p : (2:ℤ) = ↑(2:ℕ), by norm_num,
                rw p,
                rw coe_nat_dvd,
                assumption,
            },
            {
                intro nd,
                simp [nd],
                have : (1 + ↑u) / 2 ≥ 0, from sorry
            }

        end,
    witness_2 :=
        begin
            admit
        end
}



#check (1 : ℚ ) -- getting lag atm from importing stuff

-- this is hard
instance nat_rat_bijection : Bijection nat rat := sorry
