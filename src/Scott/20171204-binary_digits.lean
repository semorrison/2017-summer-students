import .x20171204_lemmas

def div_2_decreasing : Π n : ℕ, (n + 1) / 2 < n + 1
| 0 := dec_trivial
| (n+1) := begin
             have q := div_2_decreasing n,
             rw nat.div_lt_iff_lt_mul,
             rw nat.div_lt_iff_lt_mul at q,
             rw nat.right_distrib,
             transitivity (n + 1) * 2 + 1,
             apply nat.add_lt_add_right,
             assumption,
             apply nat.add_lt_add_left,
             repeat { exact dec_trivial }
           end

def binary_digits : ℕ → list bool
| 0 := [ ff ]
| 1 := [ tt ]
| (n+2) := 
          have (n+2)/2 < n+2, from div_2_decreasing (n + 1),
          (n % 2 = 1) :: binary_digits ((n+2)/2)

def from_binary_digits : list bool → ℕ
| [] := 0
| (b :: t) := 2 * (from_binary_digits t) + cond b 1 0

#eval binary_digits 1234567
#eval from_binary_digits [tt,tt,tt,ff,tt]



lemma binary_digits_correct : Π n : ℕ, from_binary_digits (binary_digits n) = n
| 0 := begin refl end
| 1 := begin refl end
| (n+2) := begin
             unfold binary_digits,
             unfold from_binary_digits,
             rw [ 
              have q : (n+2)/2 < n+2 := div_2_decreasing (n + 1), -- the evidence of well-foundedness needs to be right before the recursive call
              binary_digits_correct ((n+2)/2)
             ],
             exact p3 n
           end

lemma binary_digits_correct' : Π l : list bool, binary_digits (from_binary_digits l) = l :=
sorry -- actually, this won't work: we need trim trailing zeros. instead, let's go work with fixed length binary strings.
