import system.io
variable [io.interface]
open io

def hello_world : io unit :=
put_str "hi\n"

#eval hello_world

open nat io

def print_squares : ℕ → io unit
| 0 := return ()
| (succ n) := print_squares n >> put_str (to_string n ++ "^2 = " ++ to_string (n*n) ++ "\n")

#eval print_squares 100
-- #reduce print_squares 100

#print axioms hello_world

-- 'meta def' marks something as not meant to be trusted by the foundational framework
-- don't need to verify things terminate
-- cannot appear as part of ordinary definitions and theorems

meta def m91 : ℕ → ℕ
| n := if n > 100 then n - 10 else m91 (m91 (n + 11))

#eval m91 10
#eval m91 100
#eval m91 1000

meta def print_m91 : ℕ → io unit
| 0 := return ()
| (succ n) := print_m91 n >> put_str ("m91 " ++  to_string  n ++ " = " ++ to_string (m91 n) ++ "\n")

#eval print_m91 120

meta def foo : ℕ → ℕ
| n := foo n + 1

#reduce foo 0
-- #eval foo 0

open tactic

meta def destruct_conjunctions : tactic unit :=
repeat (do
    l <- tactic.local_context,
    first $ l^.for (λ h, do
        ht <- infer_type h >>= whnf,
        match ht with
        | `(and %%a %%b) := do
            n <- mk_fresh_name,
            tactic.mk_mapp ``and.left [none, none, some h] >>= tactic.assertv n a,
            n <- mk_fresh_name,
            mk_mapp ``and.right [none, none, some h] >>= assertv n b,
            clear h
        | _ := failed
        end))

/-
        example (a b c : Prop) (h : (a ∧ b) ∧ (c ∧ a)) : c :=
        begin destruct_conjunctions >> assumption end
        -/
