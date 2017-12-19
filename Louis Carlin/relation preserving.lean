

class relation_preserving {α : Type} (r : α → α → Prop) (f : α → α) :=
(witness : ∀ a b : α,  r a b → r (f a) (f b) )

#check eq

instance eq_add_one_preserving  : relation_preserving eq (λ (x : nat), x + 1) :=
{
    witness :=
    begin
        intros,
        rw [a_1],
    end
}

instance eq_add_preserving (n : nat)  : relation_preserving eq (λ (x : nat), x + n) :=
{
    witness :=
    begin
        intros,
        rw [a_1],
    end
}

#check (nat.add_lt_add_right (h : 1 < 2) 4 )

instance lt_add_preserving (n : nat) : relation_preserving nat.lt (λ (x : nat), x + n) :=
{
    witness :=
    begin
        intros,
        exact nat.add_lt_add_right a_1 n,
    end
}

#check nat.add_le_add_right