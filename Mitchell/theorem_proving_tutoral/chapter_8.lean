open function

#print surjective

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variable x : γ
open function

lemma surjective_comp {g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) : surjective (g ∘ f) := sorry

namespace hide

end hide