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

#reduce int.sizeof 5
#reduce int.sizeof (-6)
#check int.sizeof 5
#print int.sizeof -- How does  this work?



open classical

lemma geq_zero (u : nat) : (↑ u : int) ≥ 0 :=
begin
exact dec_trivial
end

example : 5 ≥ 0 :=
begin
have h1 : 0 < 5, from dec_trivial,
unfold ge,
exact assume h2 : 5 < 0, 
show false, from sorry
end

#check nat.less_than_or_equal

#check lt_div_of_mul_lt
-- lemma geq_div_of_mul_lt

#check 2 ∣ 3 


lemma div_mul_two  (u : int) : 2 ∣ u → 2 * (u / 2) = u :=
begin
    intro,
    
end

instance nat_int_bijection : Bijection nat int :=
{
    morphism := λ n : nat, if (2 ∣ n) then - (n/2) else (n+1)/2,
    inverse := λ i : int, if (i <= 0) then (int.sizeof (2 * i)) else int.sizeof (2*i - 1), -- how to convert int to nat
    witness_1 :=
        begin
            intro u,
            have h1 : 2 ∣ u ∨ ¬ 2 ∣ u, from em (2 ∣ u), 
            apply or.elim h1,
            {
                intro d,
                simp [d],
                have h2 : (↑ u: int) ≥ 0, from geq_zero u,
                have h3 : (↑ u: int)/2 ≥ 0, from sorry,
                have h4 : (-(↑u / 2) : int)  ≤ 0, from sorry,
                simp [h4],
                
                admit,
            },
            {
                intro nd,
                simp [nd],
                have : (1 + ↑u) / 2 ≤ 0, from sorry
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
