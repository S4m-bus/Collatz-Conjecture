import CollatzConjecture.Forward

namespace CollatzConjecture

def Coalesces {α : Type*} (f : α → α) (a b : α) : Prop :=
  ∃ i j : Nat, iter f i a = iter f j b

theorem coalesces_refl {α : Type*} (f : α → α) (a : α) :
    Coalesces f a a := by
  exact ⟨0, 0, rfl⟩

theorem coalesces_symm {α : Type*} (f : α → α) {a b : α}
    (h : Coalesces f a b) : Coalesces f b a := by
  rcases h with ⟨i, j, hij⟩
  exact ⟨j, i, hij.symm⟩

theorem coalesces_trans {α : Type*} (f : α → α) {a b c : α}
    (hab : Coalesces f a b) (hbc : Coalesces f b c) :
    Coalesces f a c := by
  rcases hab with ⟨i, j, hij⟩
  rcases hbc with ⟨p, q, hpq⟩
  rcases le_total j p with hjp | hpj
  · refine ⟨i + (p - j), q, ?_⟩
    calc
      iter f (i + (p - j)) a = iter f (p - j) (iter f i a) := iter_add f i (p-j) a
      _ = iter f (p - j) (iter f j b) := by rw [hij]
      _ = iter f p b := by
        rw [← iter_add]
        congr 1
        omega
      _ = iter f q c := hpq
  · refine ⟨i, q + (j - p), ?_⟩
    calc
      iter f i a = iter f j b := hij
      _ = iter f (j - p) (iter f p b) := by
        rw [← iter_add]
        congr 1
        omega
      _ = iter f (j - p) (iter f q c) := by rw [hpq]
      _ = iter f (q + (j - p)) c := by rw [iter_add]

theorem coalesces_equivalence {α : Type*} (f : α → α) :
    Equivalence (Coalesces f) where
  refl := coalesces_refl f
  symm := coalesces_symm f
  trans := coalesces_trans f

def Hits {α : Type*} (f : α → α) (x z : α) : Prop :=
  ∃ k : Nat, iter f k x = z

def HittingSet {α : Type*} (f : α → α) (z : α) : Set α :=
  {x | Hits f x z}

theorem hittingSet_laminar {α : Type*} (f : α → α) {x y : α}
    (hne : (HittingSet f x ∩ HittingSet f y).Nonempty) :
    HittingSet f x ⊆ HittingSet f y ∨ HittingSet f y ⊆ HittingSet f x := by
  rcases hne with ⟨a, ⟨⟨i, hix⟩, ⟨j, hjy⟩⟩⟩
  rcases le_total i j with hij | hji
  · left
    intro c hc
    rcases hc with ⟨m, hmc⟩
    have hstep : iter f (j - i) x = y := by
      calc
        iter f (j - i) x = iter f (j - i) (iter f i a) := by rw [hix]
        _ = iter f (i + (j - i)) a := by rw [iter_add]
        _ = iter f j a := by congr 1 <;> omega
        _ = y := hjy
    refine ⟨m + (j - i), ?_⟩
    calc
      iter f (m + (j - i)) c = iter f (j - i) (iter f m c) := iter_add f m (j-i) c
      _ = iter f (j - i) x := by rw [hmc]
      _ = y := hstep
  · right
    intro c hc
    rcases hc with ⟨m, hmc⟩
    have hstep : iter f (i - j) y = x := by
      calc
        iter f (i - j) y = iter f (i - j) (iter f j a) := by rw [hjy]
        _ = iter f (j + (i - j)) a := by rw [iter_add]
        _ = iter f i a := by congr 1 <;> omega
        _ = x := hix
    refine ⟨m + (i - j), ?_⟩
    calc
      iter f (m + (i - j)) c = iter f (i - j) (iter f m c) := iter_add f m (i-j) c
      _ = iter f (i - j) y := by rw [hmc]
      _ = x := hstep

end CollatzConjecture
