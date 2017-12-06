theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
    apply and.intro,
    exact hp,
    apply and.intro,
    exact hq,
    exact hp,
end

-- 'apply' applies an expresion

#print test

variables {p q : Prop} (hp : p) (hq : q)

include hp hq -- includes indicated variables and those they depend on

example : p ∧ q ∧ p :=
begin
    apply and.intro hp,
    exact and.intro hq hp,
end

omit hp hq

example (α : Type) : ∀ x : α, x = x :=
begin
    intro x,
    exact eq.refl x,
end

example : ∀ a b c : ℕ , a = b → a = c → c = b :=
begin
    intros,
    apply eq.trans,
    apply eq.symm,
    repeat {assumption}
end

example : ∃ a : ℕ, a=a :=
begin
    fapply exists.intro, -- fapply is more aggressive in creating new subgoals
    exact 0,
    apply rfl
end

example (x : ℕ) : x = x :=
begin
    revert x,
    intro y,
    refl,
end
-- 'inverse' to revert (useless here)

example (x y : ℕ) (h : x = y) : y = x :=
begin
    revert x,
    intros,
    symmetry,
    assumption,
end

example : 3 = 3 :=
begin
    generalize : 3 = x,
    revert x,
    intro y, refl,
end
-- generalizes 3

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
    intro h,
    cases h with hp hq,
    constructor, exact hq, exact hp
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
    intro h,
    cases h with x px,
    constructor, left, exact px
end

-- from is sugar for exact

example (n : ℕ) : n + 1 = nat.succ n := 
begin
    show nat.succ n = nat.succ n,
    refl,
end

-- semicolon is a parallel version of sequencing
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
by split; assumption
-- useful when the resulting goals can be finished off in a uniform way

-- orelse <|>
-- applies one tactic, then backtracks and applies another one if the first fails
example (p q : Prop) (hq : q) : p ∨ q :=
by { left, assumption} <|> {right, assumption}

#check refl

-- 'try t' is sugar for 't <|> skip'

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ q ∧ r :=
begin
    split,
    all_goals {try {split}},
    all_goals {assumption}
end
-- applying a tactic to all goals

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ q ∧ r :=
begin
    split,
    any_goals {split},
    any_goals {assumption}
end
-- Fails unless it works for at least one

