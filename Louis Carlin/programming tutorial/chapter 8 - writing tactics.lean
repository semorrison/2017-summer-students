/- 8.1 - First look -/

namespace one

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

end one

/- 8.2 - Names and Expressions -/
namespace two
open tactic

example (a b : Prop ) (h : a ∧ b) : b ∧ a :=
begin
   split,
   exact and.right h,
   exact and.left h 
end

example (a b : Prop ) (h : a ∧ b) : b ∧ a :=
by do split,
    to_expr ```(and.right h) >>= exact,
    to_expr ```(and.left h) >>= exact

/-
name - hierarchical names
expre - expressions
pexpr - pre-expressions
-/

-- names are used as identifiers that reference defined constants in Lean (also local variables, atrributes, and other objects)
namespace foo
theorem bar : true := trivial

meta def my_tac : tactic unit := mk_const `bar >>= exact

example : true := by my_tac -- problem is propper name is `foo.bar rather than `bar
-- we can also use double backtick to ask the parser to resolve the expression with the name of an object
-- in the environment at parse time

end foo

-- necessary to generate a fresh name
example (a : Prop) : a → a :=
by do n ← mk_fresh_name,
    intro n,
    hyp ← get_local n, -- what is going on?
    local_context >>= trace,
    exact hyp


-- the purpose of tactic mode is to construct expressions

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do
    split,
    eh ← get_local `h,
    mk_mapp ``and.right [none, none, some eh] >>= exact, -- mk_mapp retrieves the definition of and.right
    mk_mapp ``and.left [none, none, some eh] >>= exact -- first arg is a name, second is a "list (option expr)"
             -- none entries tell mk_mapp to treat that argument as implicit and infer it with type inference


example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do
    split,
    ea← get_local `a,
    eb ← get_local `b,
    eh ← get_local `h,
    mk_app ``and.right [ea, eb, eh] >>= exact, -- can only include explicit arguments?
    mk_app ``and.left [ea, eb, eh] >>= exact
end two

open tactic

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do
    split,
    eh ← get_local `h,
    mk_const ``and.right >>= apply,
    exact eh,
    -- target >>= trace, -- a
    mk_const ``and.left >>= apply,
    -- target >>= trace, -- a ∧ ?m_1
    exact eh

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do
    split,
    to_expr ```(and.right h) >>= exact, -- ```(...) constructs pexpr
    to_expr ```(and.left h) >>= exact

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do
    split,
    eh ← get_local `h,
    to_expr ``(and.right %%eh) >>= exact, -- insert expression eh intro pre-expression with %%
    to_expr ``(and.left%%eh) >>= exact

    -- ``(...) -- resolves names when tactic is defined
    -- ``(...) -- resolves names when tactic is executed

/- 8.3 - Examples -/