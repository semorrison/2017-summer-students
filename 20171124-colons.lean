variables p q : Prop

example : (p → q) → p → p := λ _ (hp : p), hp -- fine
example (p → q) → p → p := λ _ (hp : p), hp -- not fine

example : p → q → p → p := λ _ _ (hp : p), hp -- fine
example p → q → p → p := λ _ _ (hp : p), hp -- not fine
example p → q → p → p := λ (_ : p) (_ : q) (hp : p), hp -- fine

example p → q → (p → p) := λ (_ : p) (_ : q) (hp : p), hp -- fine
example (p → q) → p → p := λ (_ : p → q) (hp : p), hp -- not fine
example : (p → q) → p → p := λ (_ : p → q) (hp : p), hp -- fine