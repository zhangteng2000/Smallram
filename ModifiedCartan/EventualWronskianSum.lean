import ModifiedCartan.WronskianSumLimit
import ModifiedCartan.SmallPolynomialLog
import ModifiedCartan.MeasureLimitTransfer
import ModifiedCartan.RescaledZeroCoefficients

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem log_sum_nonneg_of_convergence_eventual {n : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → Index n → ℂ → ℂ} {s : ℕ → ℝ} {v : Index n → ℂ → ℝ}
    (hf : ∀ ν j, AnalyticOnNhd ℂ (f ν j) U)
    (hnz : ∀ ν j, ∃ z ∈ U, f ν j z ≠ 0)
    (hWnz : ∀ᶠ ν in atTop, ∃ z ∈ U, FewInflection.wronskian n (f ν) z ≠ 0)
    (hpos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop)
    (hv : ∀ j, LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν j z‖) (v j))
    (hW : LocalMeasureConvergence U
      (fun ν z => (s ν)⁻¹ * Real.log ‖FewInflection.wronskian n (f ν) z‖) (fun _ => 0)) :
    ∀ᵐ z ∂volume.restrict U, 0 ≤ ∑ j, v j z := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hWnz
  exact log_sum_nonneg_of_convergence hU hUc (fun ν => hf (ν + N))
    (fun ν => hnz (ν + N)) (fun ν => hN (ν + N) (by omega)) (fun ν => hpos (ν + N))
    (hs.comp (tendsto_add_atTop_nat N))
    (fun j => (hv j).comp_tendsto (tendsto_add_atTop_nat N))
    (hW.comp (tendsto_add_atTop_nat N))

/-- A monic Wronskian with degree negligible relative to the scale
supplies the actual zero logarithm limit needed for the sum inequality. -/
theorem log_sum_nonneg_of_monic_wronskians {n : ℕ}
    {f : ℕ → Index n → ℂ → ℂ} {s : ℕ → ℝ} {v : Index n → ℂ → ℝ}
    {P : ℕ → Polynomial ℂ}
    (hf : ∀ ν j, AnalyticOnNhd ℂ (f ν j) (ball 0 4))
    (hnz : ∀ ν j, ∃ z ∈ ball (0 : ℂ) 4, f ν j z ≠ 0)
    (hpos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop)
    (hv : ∀ j, LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (s ν)⁻¹ * Real.log ‖f ν j z‖) (v j))
    (hP : ∀ ν, (P ν).Monic)
    (hroots : ∀ ν a, (P ν).eval a = 0 → ‖a‖ ≤ 64)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    (hW : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 4,
      FewInflection.wronskian n (f ν) z = (P ν).eval z) :
    ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), 0 ≤ ∑ j, v j z := by
  have hlog := ((Paper.eq_small_polynomial_log P hP hroots hs hm).restrict
    (subset_univ (ball (0 : ℂ) 4))).inMeasure one_ne_zero
  have hmeasure : LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => (s ν)⁻¹ * Real.log ‖FewInflection.wronskian n (f ν) z‖) (fun _ => 0) := by
    intro K hK hKU
    apply (hlog K hK hKU).congr' _ EventuallyEq.rfl
    filter_upwards [hW] with ν hν
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    rw [hν z (hKU hz), div_eq_mul_inv, mul_comm]
  have hWnz : ∀ᶠ ν in atTop, ∃ z ∈ ball (0 : ℂ) 4,
      FewInflection.wronskian n (f ν) z ≠ 0 := by
    filter_upwards [hW] with ν hν
    have hpoly : ∃ z ∈ ball (0 : ℂ) 4, (P ν).eval z ≠ 0 :=
      Measure.exists_mem_of_measure_ne_zero_of_ae
        (isOpen_ball.measure_ne_zero volume ⟨0, mem_ball_self (by norm_num : (0 : ℝ) < 4)⟩)
        (ae_restrict_of_ae (monic_polynomial_eval_ne_zero_ae (P ν) (hP ν)))
    obtain ⟨z, hz, hPz⟩ := hpoly
    exact ⟨z, hz, by simpa only [hν z hz] using hPz⟩
  exact log_sum_nonneg_of_convergence_eventual isOpen_ball (convex_ball (0 : ℂ) 4).isPreconnected
    hf hnz hWnz hpos hs hv hmeasure

end ModifiedCartan
#print axioms ModifiedCartan.log_sum_nonneg_of_monic_wronskians
