inductive xnat 
| zero : xnat
| succ : xnat → xnat

namespace xnat
def one := succ zero
def two := succ one

def add : xnat → xnat → xnat
| x zero := x
| x (succ y) := succ (add x y)
notation a + b := add a b
theorem add_zero (x : xnat) : x + zero = x := by refl

@[simp] theorem zero_add (n : xnat) : zero + n = n :=
begin
  induction n with t Ht,
  refl,
  unfold add,
  rw Ht
end

def less : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := less m p
notation a < b := less a b

theorem a_less_b_iff_add (a b : xnat) : a < b ↔ ∃ t : xnat, b = a + succ t :=
begin
  constructor,
  intro halb,
  induction a with a Ha,
  conv in (_ = _) {rw zero_add},
end

end xnat
