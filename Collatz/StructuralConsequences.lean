import Collatz.Basic

namespace Collatz

/-- A forward orbit never hits the designated terminal state. -/
def Avoids {α : Type*} (f : α → α) (terminal x : α) : Prop :=
  ∀ k : ℕ, iter f k x ≠ terminal

/-- A full infinite forward orbit is injective in its time index. -/
def InfiniteSimple {α : Type*} (f : α → α) (x : α) : Prop :=
  ∀ ⦃i j : ℕ⦄, i < j → iter f i x ≠ iter f j x

/-- A forward orbit has a repeated vertex. -/
def HasRepeat {α : Type*} (f : α → α) (x : α) : Prop :=
  ∃ i j : ℕ, i < j ∧ iter f i x = iter f j x

/-- The elementary deterministic alternative used in the paper:
    every orbit either repeats or is injective. -/
theorem repeat_or_infiniteSimple {α : Type*} (f : α → α) (x : α) :
    HasRepeat f x ∨ InfiniteSimple f x := by
  classical
  by_cases h : HasRepeat f x
  · exact Or.inl h
  · right
    intro i j hij heq
    exact h ⟨i, j, hij, heq⟩

/-- Therefore an orbit that does not hit a terminal state is either a repeated
    nonterminal orbit or an infinite simple orbit avoiding the terminal. -/
theorem nonterminal_dichotomy {α : Type*} (f : α → α) (terminal x : α)
    (havoid : Avoids f terminal x) :
    (HasRepeat f x ∧ Avoids f terminal x) ∨
      (InfiniteSimple f x ∧ Avoids f terminal x) := by
  rcases repeat_or_infiniteSimple f x with hrep | hsimple
  · exact Or.inl ⟨hrep, havoid⟩
  · exact Or.inr ⟨hsimple, havoid⟩

/-- A repeated vertex really gives a periodic tail, not just a graph-theoretic
    collision. -/
theorem hasRepeat_gives_periodic_tail {α : Type*} (f : α → α) {x : α}
    (h : HasRepeat f x) :
    ∃ i j : ℕ, i < j ∧
      ∀ t : ℕ, iter f (i + t) x = iter f (j + t) x := by
  rcases h with ⟨i, j, hij, heq⟩
  exact ⟨i, j, hij, repeat_forces_periodic_tail f heq⟩

/-- Every actual hit has a least hit time. -/
theorem hits_has_firstHit {α : Type*} (f : α → α) {terminal x : α}
    (h : Hits f x terminal) :
    ∃ k : ℕ, FirstHit f terminal x k := by
  classical
  let k := Nat.find h
  refine ⟨k, Nat.find_spec h, ?_⟩
  intro i hi hPi
  have hki : k ≤ i := Nat.find_min' h hPi
  omega

/-- Hence every terminating orbit has a simple first-hit prefix. -/
theorem hits_has_simple_firstHit {α : Type*} (f : α → α) {terminal x : α}
    (h : Hits f x terminal) :
    ∃ k : ℕ, FirstHit f terminal x k ∧ SimplePrefix f x k := by
  rcases hits_has_firstHit f h with ⟨k, hk⟩
  exact ⟨k, hk, firstHit_simple f hk⟩

end Collatz
