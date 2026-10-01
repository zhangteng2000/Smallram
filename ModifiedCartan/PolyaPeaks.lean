import ModifiedCartan.ApproximateGrowthPeaks
import ModifiedCartan.MultiplicativePeak

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section
namespace Paper

/-- LaTeX `lem:peaks`, including finite positive endpoints of the strong-index
interval. LaTeX `eq:peak` holds with its exact multiplicative error and exponent.
The interval-supremum proof is recorded in FORMALIZATION_MAP.md. -/
theorem lem_peaks (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) (hm : MonotoneOn T (Ioi 0))
    (_hunbounded : ∀ M, ∃ r, 0 < r ∧ M < T r)
    {μ : ℝ} (hμ : 0 < μ)
    (hlower : strongLowerIndex T ≤ (μ : EReal))
    (hupper : (μ : EReal) ≤ strongUpperIndex T) :
    ∃ r ε : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop atTop ∧
      (∀ n, 0 < ε n) ∧ StrictAnti ε ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n t, ε n ≤ t → t ≤ (ε n)⁻¹ →
        T (t * r n) ≤ (1 + ε n) * t ^ μ * T (r n) := by
  have h : ∀ n : ℕ, ∃ x : ℝ, (n : ℝ) ≤ x ∧
      ∀ y, x - ((n : ℝ) + 1) ≤ y → y ≤ x + ((n : ℝ) + 1) →
        logGrowthProfile T y - μ * y ≤
          logGrowthProfile T x - μ * x + Real.log (1 + polyaPeakEpsilon n) := by
    intro n
    exact exists_logarithmic_growth_peak T hT hm hμ.le hlower hupper
      (by positivity) (Real.log_pos (by linarith [polyaPeakEpsilon_pos n])) n
  choose x hx hpeak using h
  have hxto : Tendsto x atTop atTop :=
    tendsto_atTop_mono hx
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  refine ⟨fun n => Real.exp (x n), polyaPeakEpsilon, fun n => Real.exp_pos _,
    Real.tendsto_exp_atTop.comp hxto, polyaPeakEpsilon_pos,
    polyaPeakEpsilon_strictAnti, polyaPeakEpsilon_tendsto, ?_⟩
  intro n t ht0 ht1
  obtain ⟨ht, hl0, hl1⟩ := logarithmic_window_of_polyaPeakEpsilon ht0 ht1
  exact multiplicative_peak_of_logarithmic_peak T hT (polyaPeakEpsilon_pos n)
    (hpeak n) ht hl0 hl1

end Paper
end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.lem_peaks
