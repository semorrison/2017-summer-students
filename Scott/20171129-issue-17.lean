inductive xnat 
| zero : xnat
| succ : xnat → xnat

namespace xnat
def one := succ zero

def add : xnat → xnat → xnat
| x zero := x
| x (succ y) := succ (add x y)
notation a + b := add a b
end xnat

open xnat

open interactive
open interactive.types

namespace tactic.interactive

meta def trivial_induction (p : parse texpr) : tactic unit := 
`[ induction %%p with t Ht, refl, unfold add, rw Ht ]

end tactic.interactive

theorem xnat.zero_add (n : xnat) : zero + n = n :=
begin
trivial_induction n,
end


