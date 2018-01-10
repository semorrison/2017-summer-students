open nat
variables (f : nat → nat) (k : nat)

example (H₁ : f 0 = 0) (H₂ : k = 0) : f k = 0 :=
begin
  rewrite H₂, -- replace k with 0
  rewrite H₁  -- replace f 0 with 0
  ,
end


theorem test (p q : Prop) (Hp : p) (Hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro,
  exact Hp,
  apply and.intro,
  exact Hq,
  exact Hp
end