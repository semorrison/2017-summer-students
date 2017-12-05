-- What does "absurd" actually give?

open classical

variable p : Prop

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, show p, from hp)
  (assume hnp : ¬p, show p, from absurd hnp h)

#print absurd
#print false.rec

#print or.elim
#print em
#print dne

-- I get everything except for the last line. How do we show p from absurd hnp h?
-- In other words, how does absurd make a proof of a proposition?
