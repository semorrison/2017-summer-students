open nat

def even : ℕ → Prop
| 0        := true
| (succ n) := ¬ (even n)

example : even 6 := by { unfold even, simp }

lemma not_not : ∀ p : Prop, p → ¬¬p :=
begin
  intro, intro, intro, contradiction
end

def infinitely_many_even_integers : ∀ n : ℕ, ∃ m ≥ n, even m :=
begin
intro n,
by_cases (even n), -- This doesn't work: we need to show that `even` is decidable.
admit
end

instance parity_decidable : decidable_pred even :=
begin
unfold decidable_pred,
intro n,
induction n,
{
    unfold even,
    exact decidable.true
},
{
  cases ih_1,
  {
    unfold even,
    exact decidable.is_true a_1
  },
  {
    unfold even,
    refine decidable.is_false _,
    apply not_not, assumption
  }
}
end

-- set_option pp.all true

def infinitely_many_even_integers_2 : ∀ n : ℕ, ∃ m ≥ n, even m :=
begin
  intro n,
  by_cases (even n),
  {
    existsi n,
    existsi _,
    assumption,
    unfold ge,
  },
  {
    existsi (n+1),
    existsi _,
    unfold even,
    assumption,
    -- how do we obtain a proof that n + 1 ≥ n? This is pretty gross.
    unfold ge,
    unfold has_le.le,
    exact less_than_or_equal.step (less_than_or_equal.refl n),
  }
end

inductive xnat 
| zero : xnat
| succ : xnat → xnat
open xnat

namespace xnat
def is_zero : xnat → Prop := (λ n, n = zero)

lemma zero_not_succ (n : xnat) : zero ≠ succ n := 
  by apply xnat.no_confusion
lemma succ_not_zero (n : xnat) : succ n ≠ zero := 
begin
  intro, 
  have : ¬(zero = succ n), from zero_not_succ n,
  exact this a.symm
end

instance zero_decidable : decidable_pred is_zero :=
begin
  unfold decidable_pred,
  intro a,
  induction a with a Ha,
  {
    unfold is_zero,
    simp,
    exact decidable.true
  },
  {
    unfold is_zero,
    have : ¬(succ a = zero), by apply succ_not_zero,
    simp [this],
    exact decidable.false
  }
end
end xnat