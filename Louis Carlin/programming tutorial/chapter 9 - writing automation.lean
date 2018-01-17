/- 9.1 - A Tableau Prover for Classical Propositional Logic 

Proof goes:
- negate the conclusion, so that the goal becomes "a, b, c, ¬ d → false" (how to I draw that symbol?)
- negation-normal form (eliminate → and ↔ in terms of the other connectives)
- all formulas are now built up frmo literals using only ∧ and ∨
- repeat
    - reduce a goal of the form a ∧ b → false to the goal a, b → false
    - reduce a goal of the form a ∨ b → false to the pair of goals a → false and b → false
    - prove any goal of the form a ¬ a → false in the usual way

At each step we decrease the number of connectives in the goal. If we face a goal where the first two rules 
don't apply then it must consist of literals. If the last rule doesn't apply, then no propositional variable 
appears with its negation and it is easy to cook up a truth assignment that falsifies the goal.

-/

open expr tactic classical

