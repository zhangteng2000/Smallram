import ModifiedCartan.RowFiltrationRelabel

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngSpechtRowRank (μ : YoungDiagram) (a : YoungBoxes μ) (r : ℕ) : ℕ :=
  Module.finrank ℂ (youngSpechtRowFiltration μ a r).toSubmodule

theorem youngSpechtRowRank_mono (μ : YoungDiagram) (a : YoungBoxes μ) :
    Monotone (youngSpechtRowRank μ a) := by
  intro r s hrs
  exact Submodule.finrank_mono (youngSpechtRowFiltration_mono μ a hrs)

@[simp] theorem youngSpechtRowRank_zero (μ : YoungDiagram) (a : YoungBoxes μ) :
    youngSpechtRowRank μ a 0 = 0 := by
  rw [youngSpechtRowRank, youngSpechtRowFiltration_zero]
  change Module.finrank ℂ (⊥ : Submodule ℂ (YoungPermutationModule μ)) = 0
  simp

theorem youngSpechtRowRank_height (μ : YoungDiagram) (a : YoungBoxes μ) :
    youngSpechtRowRank μ a (μ.colLen 0) = Module.finrank ℂ (YoungSpechtModule μ) := by
  rw [youngSpechtRowRank, youngSpechtRowFiltration_height]
  rfl

theorem youngSpechtRowRank_letter_independent (μ : YoungDiagram) (a b : YoungBoxes μ) (r : ℕ) :
    youngSpechtRowRank μ a r = youngSpechtRowRank μ b r :=
  youngSpechtRowFiltration_finrank_letter_independent μ a b r

def youngSpechtRowIncrement (μ : YoungDiagram) (a : YoungBoxes μ) (r : ℕ) : ℕ :=
  youngSpechtRowRank μ a (r + 1) - youngSpechtRowRank μ a r

/-- The finite sum of the actual filtration increments is the full Specht dimension. -/
theorem youngSpechtRowIncrement_sum (μ : YoungDiagram) (a : YoungBoxes μ) :
    (∑ r ∈ Finset.range (μ.colLen 0), youngSpechtRowIncrement μ a r) =
      Module.finrank ℂ (YoungSpechtModule μ) := by
  have hs : ∀ n : ℕ, (∑ r ∈ Finset.range n, youngSpechtRowIncrement μ a r) +
      youngSpechtRowRank μ a 0 = youngSpechtRowRank μ a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hmono := youngSpechtRowRank_mono μ a (Nat.le_succ n)
      change youngSpechtRowRank μ a n ≤ youngSpechtRowRank μ a (n + 1) at hmono
      change (∑ r ∈ Finset.range n, youngSpechtRowIncrement μ a r) +
        (youngSpechtRowRank μ a (n + 1) - youngSpechtRowRank μ a n) +
          youngSpechtRowRank μ a 0 = youngSpechtRowRank μ a (n + 1)
      omega
  simpa only [youngSpechtRowRank_zero, add_zero, youngSpechtRowRank_height] using hs (μ.colLen 0)

end
end ModifiedCartan


