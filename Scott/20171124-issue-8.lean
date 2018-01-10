inductive my_nat : Type
| zero : my_nat
| succ : my_nat -> my_nat

def one : my_nat := my_nat.succ my_nat.zero

def add : my_nat -> my_nat -> my_nat
| m my_nat.zero := m
| m (my_nat.succ n) := my_nat.succ (add m n)

#eval add one one