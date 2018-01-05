attribute [class] nat

instance nat_one : ℕ := 1
/- The command instance is syntax sugar for
def nat_one : ℕ := 1
attribute [instance, reducible] nat_one
-/

def foo [x : ℕ] : nat := x

#check @foo
#reduce foo

example : foo = 1 := rfl

instance nat_two : ℕ := 2

#reduce foo

example : foo ≠ 1 :=
λ h : 2 = 1, nat.no_confusion h (λ h : 1 = 0, nat.no_confusion h)

-- class inhabited (α : Type) :=
-- (value : α)
/- The command 'class' above is shorthand for

@[class] structure inhabited (α : Type) :=
(value : α)
-/

example : 1 ≠ 0 ∧ (5 < 2 ∨ 1 < 7) := dec_trivial
