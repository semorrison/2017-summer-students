import tactic.norm_num
import data.vector

inductive decreasing_list : ℕ → Type 
| nil  : decreasing_list 0
| cons : Π (m : ℕ) {n : ℕ} (p : m ≥ n) (l : decreasing_list n), decreasing_list (m + 1)

namespace decreasing_list

def decreasing_list.to_list : Π { n : ℕ }, decreasing_list n → list ℕ
| 0 nil                := list.nil
| (n + 1) (cons m p l) := m :: decreasing_list.to_list l

end decreasing_list

open decreasing_list

#check decreasing_list.to_list

lemma decreasing_list_0_is_empty ( l : decreasing_list 0 ) : l = decreasing_list.nil :=
begin
  cases l, refl
end

structure Bijection ( U V : Type ) :=
  ( morphism : U → V )
  ( inverse  : V → U )
  ( witness_1 : ∀ u : U, inverse (morphism u) = u )
  ( witness_2 : ∀ v : V, morphism (inverse v) = v )

class Finite ( α : Type ) :=
  ( cardinality : nat )
  ( bijection : Bijection α (fin cardinality) )



def enumerate_decreasing_lists {n: ℕ} : Π (k : ℕ) (p : k < 2^n), decreasing_list n
| k p := sorry

definition decreasing_list_cardinality : Π {n : ℕ}, Finite (decreasing_list n)
| 0       := {
               cardinality := 1,
               bijection   := {
                morphism := λ l, 0,
                inverse  := λ n, decreasing_list.nil,
                witness_1 := begin intros, cases u, refl end,
                witness_2 := begin intros, cases v, cases is_lt, refl, cases a, end
               }
             }
| (n + 1) := sorry