import ModifiedCartan.ArbitraryRadiusData
import ModifiedCartan.UnitaryPolynomialBounds
import ModifiedCartan.EventualWronskianSum
import ModifiedCartan.NormalizedNormLimit
import ModifiedCartan.FiniteLogMax
import ModifiedCartan.LocalMeasureUniqueness

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Exact preservation of the previously fixed limiting norm and the
nonnegative coordinate sum under the actual unitary polynomial changes. -/
theorem ArbitraryRadiusLimitData.unitary_norm_and_sum_limits {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (a : ℂ) (ha : a ∈ d.good_centers.centers) {ns : ℕ → ℕ} (hns : StrictMono ns)
    (V : ℕ → Matrix.unitaryGroup (Index n) ℂ)
    {u : Index n → ℂ → EReal} {v : Index n → ℂ → ℝ}
    (hu : ∀ j, IsSubharmonicOn (ball (0 : ℂ) 4) (u j))
    (hrep : ∀ j, u j =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v j z : EReal)))
    (hconv : ∀ j, LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index n) (Index n) ℂ) j).eval z)) (v j)) :
    EqOn d.U (fun z => Finset.univ.sup (fun j => u j z)) (ball (0 : ℂ) 4) ∧
      (∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), 0 ≤ ∑ j, u j z) := by
  let s : ℕ → ℝ := fun ν => characteristic f (r (d.subseq (ns ν)))
  let F : ℕ → Index n → ℂ → ℂ := fun ν j z =>
    (polynomialMatrixGauge (d.polynomial (ns ν)) (V ν : Matrix (Index n) (Index n) ℂ) j).eval z
  have hspos (ν : ℕ) : 0 < s ν := d.scale_pos (ns ν)
  have hs : Tendsto s atTop atTop := d.scale_tendsto.comp hns.tendsto_atTop
  have hf (ν : ℕ) (j : Index n) : AnalyticOnNhd ℂ (F ν j) (ball 0 4) :=
    (AnalyticOnNhd.eval_polynomial (polynomialMatrixGauge (d.polynomial (ns ν))
      (V ν : Matrix (Index n) (Index n) ℂ) j)).mono (subset_univ _)
  have hnz (ν : ℕ) (j : Index n) : ∃ z ∈ ball (0 : ℂ) 4, F ν j z ≠ 0 :=
    (hconv j).normalizedLog_nontrivial isOpen_ball ⟨0, mem_ball_self (by norm_num)⟩ (hspos ν)
  have hw (ν : ℕ) (z : ℂ) : ‖FewInflection.wronskian n (F ν) z‖ =
      ‖(FewInflection.polynomialWronskian (d.polynomial (ns ν))).eval z‖ := by
    dsimp only [F]
    rw [← polynomialWronskian_eval_eq_wronskian, polynomialMatrixGauge_unitary_wronskian_norm]
  have hwconv : LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => (s ν)⁻¹ * Real.log ‖FewInflection.wronskian n (F ν) z‖) (fun _ => 0) := by
    simpa only [hw, s, div_eq_mul_inv, mul_comm] using
      (d.replacement.log_wronskian.comp_tendsto hns.tendsto_atTop).inMeasure one_ne_zero
  have hwnz : ∀ᶠ ν in atTop, ∃ z ∈ ball (0 : ℂ) 4, FewInflection.wronskian n (F ν) z ≠ 0 := by
    apply Eventually.of_forall
    intro ν
    refine ⟨a, (ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4)) (d.good_centers.subset ha).1, ?_⟩
    apply norm_ne_zero_iff.mp
    rw [hw]
    exact norm_ne_zero_iff.mpr (d.good_centers.wronskian_ne_zero a ha (ns ν))
  have hreal (j : Index n) := (hconv j).normalizedLog_real
  have hsum := log_sum_nonneg_of_convergence_eventual isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected hf hnz hwnz hspos hs hreal hwconv
  have hmax := subharmonic_coordinate_max_nonneg isOpen_ball hu hrep hsum
  have hnew := normalized_euclidean_log_localL1_limit isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected hf hnz hspos hs hreal
  have hold : LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (s ν)⁻¹ * Real.log (euclideanNorm (fun j => F ν j z))) d.V := by
    simpa only [s, F, polynomialMatrixGauge_unitary_norm] using
      d.polynomial_norm_limit.comp_tendsto hns.tendsto_atTop
  have heq := (hold.inMeasure one_ne_zero).ae_unique isOpen_ball (hnew.inMeasure one_ne_zero)
  constructor
  · apply d.subharmonic.eqOn_of_ae_eq hmax.1 isOpen_ball
    filter_upwards [d.representative, hmax.2.1, heq] with z hzold hznew hzeq
    rw [hzold, hznew, hzeq]
  · filter_upwards [hsum, ae_all_iff.mpr hrep] with z hz hzr
    have he : (∑ j, u j z) = ((∑ j, v j z : ℝ) : EReal) := by
      rw [ereal_coe_finset_sum]
      exact Finset.sum_congr rfl (fun j _ => hzr j)
    rw [he]
    exact_mod_cast hz

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_norm_and_sum_limits
