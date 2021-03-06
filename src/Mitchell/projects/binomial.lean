import tactic.norm_num

@[simp]
def fact : ℕ → ℕ
| 0 := 1
| (n+1) := (n+1)*(fact n)

notation a `!!` := fact a

#reduce fact 5

@[simp]
def binom (n : ℕ) (k : ℕ) : ℕ := (n!!) / (((n-k)!!) * (k!!))

-- notation a `choose` b := binom a b

-- #reduce 5 choose 3

def summation (f : ℕ → ℕ) : ℕ → ℕ
| 0 := f 0
| (n+1) := (f (n+1)) + (summation n) 

lemma ex : binom 5 3 = 10 :=
begin
  norm_num,
end

theorem binom_sum {n : ℕ} : summation (binom n) n = 2 ^ n :=
    begin
    induction n with n hn,
    case nat.zero {
      unfold summation,
      simp,
    },
    case nat.succ {
      unfold summation,
      simp,
      admit
    }
    end


namespace set

def fin_set : ℕ → set ℕ
| 0 := {}
| (n+1) := insert (n+1) (fin_set n)

notation `[` n `]` := fin_set n

#reduce powerset [3]

end set