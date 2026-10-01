import ModifiedCartan.ReplacementSubsequence
import ModifiedCartan.LogLimitRepresentatives
import ModifiedCartan.NormalizedNormLimit
import ModifiedCartan.FiniteLogMax
import ModifiedCartan.EventualWronskianSum

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual coordinate and Euclidean norm limits for the same gauges
and Taylor polynomials constructed in `lem:replacement`. -/
theorem PolynomialReplacementData.exists_log_limits {n : ℕ} {f : Curve n}
    (hlin : f.linearlyNonDegenerate) (hf0 : ∀ j, f.coord j 0 ≠ 0)
    {t s : ℕ → ℝ} {C A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f t s C A L H p a η)
    (ht : Tendsto t atTop atTop) (hs : Tendsto s atTop atTop)
    (hN : Tendsto (fun ν => ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
      (0 : WithTop ℂ) (256 * t ν) / s ν) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ (∀ ν, 0 < s (ns ν)) ∧
      ∃ (u : Index n → ℂ → EReal) (v : Index n → ℂ → ℝ),
        (∀ j, IsSubharmonicOn (ball (0 : ℂ) 4) (u j) ∧
          (∃ z ∈ ball (0 : ℂ) 4, u j z ≠ ⊥) ∧
          u j =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v j z : EReal)) ∧
          LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
            (fun ν => normalizedExtendedLog (s (ns ν))
              (rescaledRepresentation f (t (ns ν)) (H (ns ν)) j)) (v j)) ∧
        LocalLpConvergence 1 (ball (0 : ℂ) 4)
          (fun ν z => (s (ns ν))⁻¹ * Real.log (euclideanNorm
            (fun j => rescaledRepresentation f (t (ns ν)) (H (ns ν)) j z)))
          (fun z => Finset.univ.sup' Finset.univ_nonempty (fun j => v j z)) ∧
        (∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), 0 ≤ ∑ j, v j z) ∧
        IsSubharmonicOn (ball (0 : ℂ) 4) (fun z => Finset.univ.sup (fun j => u j z)) ∧
        (fun z => Finset.univ.sup (fun j => u j z)) =ᵐ[volume.restrict (ball (0 : ℂ) 4)]
          (fun z => ((Finset.univ.sup' Finset.univ_nonempty (fun j => v j z) : ℝ) : EReal)) ∧
        ∀ z ∈ ball (0 : ℂ) 4, 0 ≤ Finset.univ.sup (fun j => u j z) := by
  let F := fun ν => rescaledRepresentation f (t ν) (H ν)
  have hfcenter (ν : ℕ) (j : Index n) : F ν j 0 ≠ 0 := by
    simpa only [F, rescaledRepresentation, mul_zero] using
      mul_ne_zero (Complex.exp_ne_zero _) (hf0 j)
  have hd : ∀ᶠ ν in atTop, ∀ j, AnalyticOnNhd ℂ (F ν j) (ball 0 4) ∧
      F ν j 0 ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 4, ‖F ν j z‖ ≤ Real.exp ((5 * C + 1) * s ν) := by
    filter_upwards [h.gauge_analytic, h.gauge_norm] with ν hH hbound j
    refine ⟨fun z hz => rescaledRepresentation_analyticAt f (t ν)
      (hH z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) hz)) j, hfcenter ν j, ?_⟩
    intro z hz
    exact (norm_le_pi_norm (fun k => F ν k z) j).trans ((norm_le_euclideanNorm _).trans
      (hbound z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 32)) hz)))
  obtain ⟨ns, hns, hdata, u, v, hv⟩ :=
    exists_common_log_limits_with_representatives_eventual hs hd h.coordinate_centers
  have hsource (ν : ℕ) (j : Index n) : AnalyticOnNhd ℂ (F (ns ν) j) (ball 0 4) :=
    ((hdata ν).2 j).1
  have hnonzero (ν : ℕ) (j : Index n) : ∃ z ∈ ball (0 : ℂ) 4, F (ns ν) j z ≠ 0 :=
    ⟨0, mem_ball_self (by norm_num), hfcenter (ns ν) j⟩
  have hreal (j : Index n) := (hv j).2.2.2.normalizedLog_real
  have hpos (ν : ℕ) := (hdata ν).1
  have hsum : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), 0 ≤ ∑ j, v j z := by
    apply log_sum_nonneg_of_monic_wronskians hsource hnonzero hpos (hs.comp hns.tendsto_atTop)
      hreal (fun ν => rescaledWronskianPolynomial_monic f (t (ns ν)))
    · intro ν z hz
      exact (show ‖z‖ < 64 by simpa only [mem_ball, dist_zero_right] using
        rescaledWronskianPolynomial_roots_mem f (t (ns ν)) hz).le
    · exact (rescaledWronskianPolynomial_degree_small f hlin ht hs hN).comp hns.tendsto_atTop
    · filter_upwards [hns.tendsto_atTop.eventually h.gauge_wronskian] with ν hν
      intro z hz
      exact hν z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) hz)
  have hmax := subharmonic_coordinate_max_nonneg isOpen_ball
    (fun j => (hv j).1) (fun j => (hv j).2.2.1) hsum
  exact ⟨ns, hns, hpos, u, v, hv,
    normalized_euclidean_log_localL1_limit isOpen_ball (convex_ball (0 : ℂ) 4).isPreconnected
      hsource hnonzero hpos (hs.comp hns.tendsto_atTop) hreal, hsum, hmax⟩

end ModifiedCartan
#print axioms ModifiedCartan.PolynomialReplacementData.exists_log_limits
