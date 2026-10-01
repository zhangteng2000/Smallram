import ModifiedCartan.DiskAverageApproximation

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- A compactly supported Lipschitz cutoff, constructed from metric thickening. -/
theorem exists_lipschitz_cutoff {K V : Set ℂ} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ (χ : ℂ → ℝ) (L : ℝ≥0), LipschitzWith L χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ V ∧ (∀ z, 0 ≤ χ z) ∧ (∀ z, ‖χ z‖ ≤ 1) ∧
      (∀ z ∈ K, χ z = 1) := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : ℂ → ℝ := fun z => (thickenedIndicator hδ K z : ℝ)
  have hL : LipschitzWith δ.toNNReal⁻¹ χ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [χ, NNReal.dist_eq, Real.dist_eq] using
      (lipschitzWith_thickenedIndicator hδ K).dist_le_mul x y
  have hsupp : Function.support χ ⊆ thickening δ K := by
    intro z hz
    by_contra hnot
    apply hz
    dsimp [χ]
    rw [thickenedIndicator_zero hδ K hnot]
    rfl
  have hts : tsupport χ ⊆ cthickening δ K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening δ K)
  have hcompact : HasCompactSupport χ :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport χ) hts
  refine ⟨χ, δ.toNNReal⁻¹, hL, hcompact, hts.trans hδV, ?_, ?_, ?_⟩
  · intro z
    exact (thickenedIndicator hδ K z).coe_nonneg
  · intro z
    change ‖(thickenedIndicator hδ K z : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (thickenedIndicator hδ K z).coe_nonneg]
    exact_mod_cast thickenedIndicator_le_one hδ K z
  · intro z hz
    dsimp [χ]
    rw [thickenedIndicator_one hδ K hz]
    rfl


end ModifiedCartan
