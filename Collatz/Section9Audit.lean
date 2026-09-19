import Collatz.Basic

namespace Collatz

/-- Pointwise Collatz statement for the stopped map. -/
def ReachesOne (n : ℕ) : Prop := Hits C n 1

/-- The Section 9 "path intersects P_1" statement. -/
def MergesWithTerminalPath (n : ℕ) : Prop := Coalesces C n 1

/-- Because 1 is absorbing, coalescing with P_1 is exactly the same proposition
    as reaching 1. This is a purely internal audit of the manuscript's Section 9. -/
theorem mergesWithTerminalPath_iff_reachesOne (n : ℕ) :
    MergesWithTerminalPath n ↔ ReachesOne n := by
  constructor
  · rintro ⟨i, j, hij⟩
    refine ⟨i, ?_⟩
    simpa [MergesWithTerminalPath, ReachesOne] using hij.trans (iter_C_one j)
  · rintro ⟨i, hi⟩
    exact ⟨i, 0, by simpa [MergesWithTerminalPath, ReachesOne] using hi⟩

/-- The global stopped-map Collatz proposition used by the paper. -/
def CollatzStopped : Prop :=
  ∀ n : ℕ, 0 < n → ReachesOne n

/-- The assertion "every positive forward path belongs to the merged family containing P_1". -/
def GlobalTerminalMerger : Prop :=
  ∀ n : ℕ, 0 < n → MergesWithTerminalPath n

/-- Formal audit of Section 9: the purported global-terminal-merger premise is
    logically equivalent to the Collatz conclusion for the stopped map. -/
theorem globalTerminalMerger_iff_collatzStopped :
    GlobalTerminalMerger ↔ CollatzStopped := by
  constructor
  · intro h n hn
    exact (mergesWithTerminalPath_iff_reachesOne n).mp (h n hn)
  · intro h n hn
    exact (mergesWithTerminalPath_iff_reachesOne n).mpr (h n hn)

/-- The final deduction in Section 9 is valid *conditional on* global terminal merger. -/
theorem section9_closure (h : GlobalTerminalMerger) : CollatzStopped :=
  globalTerminalMerger_iff_collatzStopped.mp h

/-- Conversely, Collatz itself gives the global merged-terminal statement. -/
theorem collatz_gives_section9_global_merge (h : CollatzStopped) :
    GlobalTerminalMerger :=
  globalTerminalMerger_iff_collatzStopped.mpr h

end Collatz
