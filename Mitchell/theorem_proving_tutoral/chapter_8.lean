open function

#print surjective

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variable x : γ
open function

lemma injective_comp {g : β → γ} {f : α → β} 
  (hg : injective g) (hf : injective f) : injective (g ∘ f) :=
  assume a b,
  assume h, hf (hg h)

lemma surjective_comp {g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) : surjective (g ∘ f) :=
  assume z,
  exists.elim (hg z) (
  assume y (hy : g y = z),
  exists.elim (hf y) (
  assume x (hx : f x = y),
  begin
  unfold comp,
  existsi x,
  rw [hx, hy]
  end ))

-- Scott : Exercise 8.1 asks to do this using pattern matching -- I don't know what
-- to pattern match against

-- Exercise 8.6
inductive aexpr : Type
| const : ℕ → aexpr
| var : ℕ → aexpr
| plus : aexpr → aexpr → aexpr
| times : aexpr → aexpr → aexpr

open aexpr

def sample_aexpr : aexpr :=
plus (times (var 0) (const 7)) (times (const 2) (var 1))
-- Here sample_aexpr represents (v₀ * 7) + (2 * v₁).

-- BEGIN
def aeval (v : ℕ → ℕ) : aexpr → ℕ
| (const n)    := n
| (var n)      := v n
| (plus e₁ e₂)  := (aeval e₁) + (aeval e₂)
| (times e₁ e₂) := (aeval e₁) * (aeval e₂)

def sample_val : ℕ → ℕ
| 0 := 5
| 1 := 6
| _ := 0

-- Try it out. You should get 47 here.
#eval aeval sample_val sample_aexpr
-- END

def sample2_aexpr : aexpr :=
plus (times (const 5) (const 7)) (times (const 2) (const 6))

/-
Implement “constant fusion,” a procedure that simplifies subterms like 4 + 7 to 12. 
Using the auxiliary function simp_const, define a function “fuse”: to simplify a plus or a times, 
first simplify the arguments recursively, and then apply simp_const to try to simplify the result.
-/

-- BEGIN
def simp_const : aexpr → aexpr
| (plus (const n₁) (const n₂))  := const (n₁ + n₂)
| (times (const n₁) (const n₂)) := const (n₁ * n₂)
| e                             := e

def fuse : aexpr → aexpr
| (plus e₁ e₂)  := simp_const (plus (fuse e₁) (fuse e₂))
| (times e₁ e₂) := simp_const (times (fuse e₁) (fuse e₂))
| e  := e

#reduce fuse sample2_aexpr

theorem simp_const_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (simp_const e) = aeval v e
| (plus (const n₁) (const n₂))  := rfl
| (times (const n₁) (const n₂)) := rfl
| e                             := sorry

-- SCOTT: I don't know how to match the general pattern here


theorem fuse_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (fuse e) = aeval v e :=
sorry
-- END