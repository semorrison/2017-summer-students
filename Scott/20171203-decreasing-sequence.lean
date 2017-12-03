inductive decreasing_list : ℕ → Type 
| nil  : decreasing_list 0
| cons : Π (m : ℕ) {n : ℕ} (p : m ≥ n) (l : decreasing_list n), decreasing_list (m + 1)

namespace decreasing_list

def decreasing_list.to_list : Π { n : ℕ }, decreasing_list n → list ℕ
| 0 nil                := list.nil
| (n + 1) (cons m p l) := m :: decreasing_list.to_list l

end decreasing_list

open decreasing_list

#check decreasing_list.to_list

lemma decreasing_list_0_is_empty ( l : decreasing_list 0 ) : l = decreasing_list.nil :=
begin
  cases l, refl
end
