import CollatzConjecture.Forward

namespace CollatzConjecture

def Avoids {α : Type*} (f : α → α) (terminal x : α) : Prop :=
  ∀ k : Nat, iter f k x ≠ terminal

def InfiniteSimple {α : Type*} (f : α → α) (x : α) : Prop :=
  ∀ ⦃i j : Nat⦄, i < j → iter f i x ≠ iter f j x

def HasRepeat {α : Type*} (f : α → α) (x : α) : Prop :=
  ∃ i j : Nat, i < j ∧ iter f i x = iter f j x

theorem repeat_or_infiniteSimple {α : Type*} (f : α → α) (x : α) :
    HasRepeat f x ∨ InfiniteSimple f x := by
  classical
  by_cases h : HasRepeat f x
  · exact Or.inl h
  · right
    intro i j hij heq
    exact h ⟨i, j, hij, heq⟩

theorem nonterminal_dichotomy {α : Type*} (f : α → α) (terminal x : α)
    (havoid : Avoids f terminal x) :
    (HasRepeat f x ∧ Avoids f terminal x) ∨
      (InfiniteSimple f x ∧ Avoids f terminal x) := by
  rcases repeat_or_infiniteSimple f x with hrep | hsimple
  · exact Or.inl ⟨hrep, havoid⟩
  · exact Or.inr ⟨hsimple, havoid⟩

end CollatzConjecture
