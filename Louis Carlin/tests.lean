example {p q : Prop} : p ∧ q → q ∧ p :=
begin
  intro hpq,
  induction hpq,
  split,
  exact hpq_right,
  exact hpq_left
end 
#check nat.gcd.induction