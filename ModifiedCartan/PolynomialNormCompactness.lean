import ModifiedCartan.VectorLogIntegrability
import ModifiedCartan.FiniteLogCompactness
import ModifiedCartan.NormalizedNormLimit
import ModifiedCartan.LocalMeasureUniqueness
import Mathlib.Analysis.Analytic.Polynomial

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- For polynomial vectors with the actual center normalization and
exponential bound, a measure limit of the normalized vector logarithms
is necessarily their local L1 limit. -/
theorem polynomial_norm_localL1_of_measure {n : ℕ}
    {p : ℕ → Index n → Polynomial ℂ} {s : ℕ → ℝ} {C : ℝ} {u : ℂ → ℝ}
    (hspos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop)
    (hp0 : ∀ ν j, (p ν j).eval 0 ≠ 0)
    (hb : ∀ᶠ ν in atTop, ∀ j z, z ∈ ball (0 : ℂ) 4 →
      ‖(p ν j).eval z‖ ≤ Real.exp (C * s ν))
    (hc : ∀ j, Tendsto (fun ν => Real.log ‖(p ν j).eval 0‖ / s ν) atTop (𝓝 0))
    (hm : LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => (s ν)⁻¹ * Real.log (euclideanNorm (fun j => (p ν j).eval z))) u) :
    LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (s ν)⁻¹ * Real.log (euclideanNorm (fun j => (p ν j).eval z))) u := by
  have han (ν : ℕ) (j : Index n) :
      AnalyticOnNhd ℂ (fun z => (p ν j).eval z) (ball 0 4) :=
    (AnalyticOnNhd.eval_polynomial (p ν j)).mono (subset_univ _)
  have hnz (ν : ℕ) (j : Index n) : ∃ z ∈ ball (0 : ℂ) 4, (p ν j).eval z ≠ 0 :=
    ⟨0, mem_ball_self (by norm_num), hp0 ν j⟩
  apply localLpConvergence_of_subseq
  · intro K hK hKU ν
    exact (memLp_one_iff_integrable.mpr
      (integrableOn_log_euclideanNorm_on_compact isOpen_ball
        (convex_ball (0 : ℂ) 4).isPreconnected (han ν) (hnz ν) hK hKU)).const_mul (s ν)⁻¹
  · intro ns hns
    have hd : ∀ᶠ ν in atTop, ∀ j,
        AnalyticOnNhd ℂ (fun z => (p (ns ν) j).eval z) (ball 0 4) ∧
        (p (ns ν) j).eval 0 ≠ 0 ∧ ∀ z ∈ ball (0 : ℂ) 4,
          ‖(p (ns ν) j).eval z‖ ≤ Real.exp (C * s (ns ν)) := by
      filter_upwards [hns.eventually hb] with ν hν j
      exact ⟨han (ns ν) j, hp0 (ns ν) j, hν j⟩
    obtain ⟨ms, hms, _, v, hv⟩ := exists_common_normalized_log_subsequence_eventual
      (hs.comp hns) hd (fun j => (hc j).comp hns)
    have hlim := normalized_euclidean_log_localL1_limit isOpen_ball
      (convex_ball (0 : ℂ) 4).isPreconnected
      (fun ν j => han (ns (ms ν)) j) (fun ν j => hnz (ns (ms ν)) j)
      (fun ν => hspos (ns (ms ν))) (hs.comp (hns.comp hms.tendsto_atTop)) hv
    have heq := (hlim.inMeasure (by norm_num)).ae_unique isOpen_ball
      (hm.comp (hns.comp hms.tendsto_atTop))
    exact ⟨ms, hlim.congr_ae (fun _ => EventuallyEq.rfl) heq⟩

end ModifiedCartan
#print axioms ModifiedCartan.polynomial_norm_localL1_of_measure
