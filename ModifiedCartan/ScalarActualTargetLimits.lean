import ModifiedCartan.ScalarActualTargetBasics
import ModifiedCartan.AnalyticLogApproximation

open scoped Topology ENNReal Matrix
open Filter Set Metric MeasureTheory Matrix
set_option autoImplicit false
namespace ModifiedCartan

/-- The same fixed-target limit is attained by the original gauged
holomorphic components, not only by their Taylor polynomials. Analyticity,
nontriviality and the subsequence are constructed. Auxiliary to `thm:A` (b). -/
theorem ScalarTargetLogLimitData.exists_actual_target_log_limit
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β)
    (hρ : 1 ≤ ρ) (hr : Tendsto r atTop atTop)
    (hA : (Real.pi / 2) * (2 : ℝ) ^ ρ ≤ d.A) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ ν, AnalyticOnNhd ℂ
        (scalarActualTarget f β (r (d.subseq (ns ν))) (d.gauge (ns ν))) (ball (0 : ℂ) 2) ∧
        ∃ z ∈ ball (0 : ℂ) 2,
          scalarActualTarget f β (r (d.subseq (ns ν))) (d.gauge (ns ν)) z ≠ 0) ∧
      LocalLpConvergence 1 (ball (0 : ℂ) 2)
        (fun ν z => (characteristic f (r (d.subseq (ns ν))))⁻¹ *
          Real.log ‖scalarActualTarget f β (r (d.subseq (ns ν))) (d.gauge (ns ν)) z‖)
        (fun z => (e.u z).toReal) := by
  have h24 : ball (0 : ℂ) 2 ⊆ ball (0 : ℂ) 4 := ball_subset_ball (by norm_num)
  have hX := e.real_convergence.restrict h24
  have hXne (ν : ℕ) : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 2),
      (polynomialMatrixGauge (d.polynomial ν)
        (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) 0).eval z ≠ 0 :=
    (e.convergence.normalizedLog_ae_ne_zero (d.scale_pos ν)).filter_mono
      (ae_mono (Measure.restrict_mono_set _ h24))
  have hu : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 2), -d.A < (e.u z).toReal := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hb := (d.scalar_norm_lt_explicit_bound hρ hr hz).trans_le hA
    exact (neg_lt_neg hb).trans_le (e.bounds z (h24 hz)).1
  have hY : ∀ᶠ ν in atTop,
      AnalyticOnNhd ℂ (scalarActualTarget f β (r (d.subseq ν)) (d.gauge ν)) (ball (0 : ℂ) 2) ∧
      ∀ z ∈ ball (0 : ℂ) 2,
        ‖scalarActualTarget f β (r (d.subseq ν)) (d.gauge ν) z‖ ≤
          Real.exp ((5 * d.C + 1) * characteristic f (r (d.subseq ν))) := by
    filter_upwards [d.replacement.gauge_analytic, d.replacement.gauge_norm] with ν hH hN
    exact ⟨scalarActualTarget_analyticOnNhd f β _ (hH.mono (ball_subset_ball (by norm_num))),
      fun z hz => (scalarActualTarget_norm_le f β _ _ z).trans
        (hN z ((ball_subset_ball (by norm_num : (2 : ℝ) ≤ 32)) hz))⟩
  exact exists_analytic_log_limit_of_exponential_approximation isOpen_ball
    (convex_ball (0 : ℂ) 2).isPreconnected (nonempty_ball.mpr (by norm_num))
    d.scale_tendsto d.scale_pos hX hXne hu hY
    (d.replacement.scalar_actual_target_approximation β)

end ModifiedCartan
#print axioms ModifiedCartan.ScalarTargetLogLimitData.exists_actual_target_log_limit
