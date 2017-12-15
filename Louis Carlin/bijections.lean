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

def abs_value : int → nat 
| 0 := 0
| i := if (i<0) then abs_value (-i) else nat.succ (abs_value (i-1)) 

#reduce abs_value (-5)

instance nat_int_bijection : Bijection nat int :=
{
    morphism := λ n : nat, if (2 ∣ n) then - (n/2) else (n+1)/2,
    inverse := λ i : int, if (i <= 0) then (abs_value (2 * i)) else 2*i - 1, -- how to convert int to nat
    witness_1 :=
        begin
            intro u,

        end,
    witness_2 :=
        begin
            admit
        end
}

#check (1 : ℚ ) -- getting lag atm from importing stuff

-- this is hard
instance nat_rat_bijection : Bijection nat rat := sorry
