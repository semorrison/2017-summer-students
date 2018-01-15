import tactic.norm_num
-- import data.rat 

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


#reduce (2 ∣ 5)
#check  10 - 5

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

open int

instance bijection_composition {α β γ : Type}  [ab :Bijection α β] [bg : Bijection β γ] : Bijection α γ :=
{
    morphism := λ x : α, @Bijection.morphism β γ bg (@Bijection.morphism α β ab x),
    inverse := λ x : γ, @Bijection.inverse α β ab (@Bijection.inverse β γ bg x),
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

instance {n:ℕ} (n > 0): Bijection nat (nat × fin n) :=
begin
admit
end
instance int_bijection' : Bijection int (nat × fin 2) := {
    morphism := λ i : int, match i with 
                           | of_nat n := (n, 0)
                           | neg_succ_of_nat n := (n, 1)
                           end,
    inverse := sorry, -- see https://github.com/semorrison/lean-category-theory/blob/master/src/categories/util/finite.lean for an example of matching on fin n.
    witness_1 := sorry,
    witness_2 := sorry
}



-- set_option pp.all true
/-
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
                have h1 : (2:int) > 0, from dec_trivial,
                have h2 : 0 ≤ (↑ u: int) , from geq_zero u,
                have h3 : 0 ≤ (↑ u: int)/2, from int.div_le_div h1 h2 , -- int.le_div_iff_mul_le _,
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
-/


#check (1 : ℚ ) -- getting lag atm from importing stuff

-- this is hard
instance nat_rat_bijection : Bijection nat rat := sorry
