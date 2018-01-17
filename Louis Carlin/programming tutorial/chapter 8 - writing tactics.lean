/- 8.1 - First look -/

open tactic

variables a b : Prop

example : a → b → a ∧ b :=
by _ -- lean expects something of type "tactic unit" to fill the underscore

-- tactic monad can be thought of as a combination of a state monad and an option monad

/-
do a ← r,
    b ← s,
    t

think of this as apply tactic r to the state, and store the return in a, apply tactic s to
the state, and store the return in b, then finally apply tactic t to the state

"s <|> t" = do s, if it fails undo it and do t 
-/

example : a → b → a ∧ b :=
by do trace "Hi, Mum!"

example : a → b → a ∧ b :=
by do trace "Hi, Mum!",
    trace_state

example : a → b → a ∧ b :=
by do eh1 ← intro `h1,
    eh2 ← intro `h2,
    skip

-- meta_constant target has type "tactic expr" and returns the type of the goal

example : a → b → a ∧ b :=
by do eh1 ← intro `h1,
    eh2 ← intro `h2,
    target >>= trace,
    local_context >>= trace

example : a → b → a ∧ b :=
by do intro `h1,
        intro `h2,
        ea ← get_local `a, -- ea : expre
        eb ← get_local `b, -- these are internal representations of the expressions
        trace (to_string ea ++ ", " ++ to_string eb),
        skip

example : a → b → a ∧ b :=
by do 
    eh1 ← intro `h1,
    eh2 ← intro `h2,
    mk_const ``and.intro >>= apply, -- builds an expr that reflects the and.intro declaration 
                                                          -- in the Lean environment and applies it
    exact eh1,
    exact eh2

example : a → b → a ∧ b :=
by do 
    eh1 ← intro `h1,
    eh2 ← intro `h2,
    applyc ``and.intro, -- combines these two steps
    exact eh1,
    exact eh2

example : a → b → a ∧ b :=
by do 
    eh1 ← intro `h1,
    eh2 ← intro `h2,
    e ← to_expr ```(and.intro h1 h2), -- ``` builds a "pre-expression", to_expre elaborates it and converts it to an
                                                          -- expression, and the exact tactic applies it
    exact e

meta def my_tactic : tactic unit :=
do 
    eh1 ← intro `h1,
    eh2 ← intro `h2,
    e ← to_expr ``(and.intro %%eh1 %%eh2),
    exact e

example : a → b → a ∧ b :=
by my_tactic