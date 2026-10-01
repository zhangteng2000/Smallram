import ModifiedCartan.CanonicalGauge
import ModifiedCartan.LogDerivativePartitions
import ModifiedCartan.LogDerivativeLimit
import ModifiedCartan.PolynomialGaugeSmallness

open scoped Topology Classical BigOperators
open Filter MeasureTheory Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem logarithmicJet_eq_partition {U : Set ℂ} (hU : IsOpen U)
    {a η : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a U) (hη : AnalyticOnNhd ℂ η U)
    (hη0 : ∀ z ∈ U, η z ≠ 0)
    (hd : ∀ z ∈ U, deriv η z = a z * η z) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    logarithmicJet a k z = logDerivativePartitionPolynomial k
      (fun j => iteratedDeriv j a z) := by
  have hlog : logDeriv η =ᶠ[𝓝 z] a := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [logDeriv_apply, hd w hw, mul_div_cancel_right₀ _ (hη0 w hw)]
  have hp := iteratedDeriv_div_eq_partition (hη z hz) (hη0 z hz) k
  rw [iteratedDeriv_eq_logarithmicJet_mul hU ha hη hd k z hz,
    mul_div_cancel_right₀ _ (hη0 z hz)] at hp
  rw [hp]
  congr 1
  funext j
  exact (hlog.iteratedDeriv j).eq_of_nhds

theorem canonical_logarithmicJet_eq_partition {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0) (k : ℕ) :
    logarithmicJet (canonicalLogDerivative n g) k z =
      logDerivativePartitionPolynomial k (fun j => iteratedDeriv j (canonicalLogDerivative n g) z) := by
  obtain ⟨η, hη, hη0, hroot⟩ := exists_canonical_gauge_nhds hg hW
  have he := ((Filter.eventually_all.mpr (fun j => (hg j).eventually_analyticAt)).and
    hη.eventually_analyticAt).and hroot
  obtain ⟨U, hsub, hU, hz⟩ := _root_.eventually_nhds_iff.mp he
  have hgU (j : Index n) : AnalyticOnNhd ℂ (g j) U := fun w hw => (hsub w hw).1.1 j
  have hηU : AnalyticOnNhd ℂ η U := fun w hw => (hsub w hw).1.2
  have hrU : ∀ w ∈ U, η w ^ (n + 1) * FewInflection.wronskian n g w = 1 :=
    fun w hw => (hsub w hw).2
  have haU : AnalyticOnNhd ℂ (canonicalLogDerivative n g) U := by
    intro w hw
    apply analyticAt_canonicalLogDerivative (fun j => hgU j w hw)
    intro hw0
    have hr := hrU w hw
    simp only [hw0, mul_zero, zero_ne_one] at hr
  exact logarithmicJet_eq_partition hU haU hηU (fun w _ => hη0 w)
    (fun w hw => normalizing_factor_deriv hU hgU hηU (fun w _ => hη0 w) hrU hw) k hz

theorem canonical_logarithmicJet_normalized_eq_partition {n : ℕ}
    {g : Index n → ℂ → ℂ} {z : ℂ} (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hW : FewInflection.wronskian n g z ≠ 0) (k : ℕ) (s : ℝ) :
    logarithmicJet (canonicalLogDerivative n g) k z / (s : ℂ) ^ k =
      logDerivativePartitionPolynomial k
        (fun j => iteratedDeriv j (canonicalLogDerivative n g) z / (s : ℂ) ^ (j + 1)) := by
  rw [canonical_logarithmicJet_eq_partition hg hW, partitionPolynomial_div_pow]

theorem monic_polynomial_eval_ne_zero_ae (P : Polynomial ℂ) (hP : P.Monic) :
    ∀ᵐ z : ℂ, P.eval z ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_normalized_polynomial_root_list P hP.ne_zero
  rw [hP.normalize_eq_self] at ha
  have he (z : ℂ) : P.eval z = ∏ i, (z - a i) := by
    simpa [Polynomial.eval_prod] using congrArg (Polynomial.eval z) ha
  simpa only [he] using linear_root_product_ne_zero_ae a

theorem canonicalLogDerivative_jet_normalized_eq_polynomial {n : ℕ} {U : Set ℂ}
    (hU : IsOpen U) {g : Index n → ℂ → ℂ} (P : Polynomial ℂ)
    (hW : ∀ z ∈ U, FewInflection.wronskian n g z = P.eval z) {z : ℂ}
    (hz : z ∈ U) (j : ℕ) (s : ℝ) :
    iteratedDeriv j (canonicalLogDerivative n g) z / (s : ℂ) ^ (j + 1) =
      (-(n + 1 : ℂ)⁻¹) * (iteratedDeriv j (logDeriv (fun w => P.eval w)) z /
        (s : ℂ) ^ (j + 1)) := by
  have he : canonicalLogDerivative n g =ᶠ[𝓝 z]
      (fun w => (-(n + 1 : ℂ)⁻¹) * logDeriv (fun t => P.eval t) w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [canonicalLogDerivative_eq_polynomial hU P hW hw]
    ring
  rw [(he.iteratedDeriv j).eq_of_nhds, iteratedDeriv_const_mul_field]
  ring

theorem partitionPolynomial_zero_of_pos {k : ℕ} (hk : 1 ≤ k) :
    logDerivativePartitionPolynomial k (fun _ => 0) = 0 := by
  simpa only [ite_self, zero_pow (by omega : k ≠ 0)] using partitionPolynomial_constant_jet k 0

/-- All positive-order normalized logarithmic jets of the actual canonical
normalizing factor vanish. The factor is identified locally and no choice
of branch occurs in the statement. Auxiliary to `eq:gaugecomparison`. -/
theorem canonical_logarithmicJet_localMeasure_zero {n : ℕ}
    (g : ℕ → Index n → ℂ → ℂ) (P : ℕ → Polynomial ℂ) {s : ℕ → ℝ}
    (hg : ∀ ν j, AnalyticOnNhd ℂ (g ν j) (ball 0 32))
    (hP : ∀ ν, (P ν).Monic)
    (hW : ∀ ν z, z ∈ ball (0 : ℂ) 32 → FewInflection.wronskian n (g ν) z = (P ν).eval z)
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    {k : ℕ} (hk : 1 ≤ k) :
    LocalMeasureConvergence (ball (0 : ℂ) 4)
      (fun ν z => logarithmicJet (canonicalLogDerivative n (g ν)) k z / (s ν : ℂ) ^ k)
      (fun _ => 0) := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  let c : ℂ := -(n + 1 : ℂ)⁻¹
  let F := fun (j ν : ℕ) (z : ℂ) => c *
    (iteratedDeriv j (logDeriv (fun w => (P ν).eval w)) z / (s ν : ℂ) ^ (j + 1))
  have hFm (j ν : ℕ) : AEStronglyMeasurable (F j ν) (volume.restrict K) := by
    exact (normalized_logDeriv_jet_aestronglyMeasurable
      (AnalyticOnNhd.eval_polynomial (P ν)) hK (subset_univ K) j (s ν)).const_mul c
  have hFlim (j : ℕ) : TendstoInMeasure (volume.restrict K) (F j) atTop (fun _ => 0) := by
    have hp := polynomial_logDeriv_jet_localMeasure_zero P hP hs hm j
    have hsub : K ⊆ ball (0 : ℂ) 6 := hKU.trans (ball_subset_ball (by norm_num))
    have hc := tendstoInMeasure_continuous_map
      (fun ν => normalized_logDeriv_jet_aestronglyMeasurable
        (AnalyticOnNhd.eval_polynomial (P ν)) hK (subset_univ K) j (s ν))
      (hp K hK hsub) (show Continuous (fun x : ℂ => c * x) by fun_prop)
    simpa only [mul_zero] using hc
  have hp := tendstoInMeasure_partitionPolynomial hFm hFlim k
  simp only [partitionPolynomial_zero_of_pos hk] at hp
  apply hp.congr_left
  intro ν
  have hnz : ∀ᵐ z ∂volume.restrict K, (P ν).eval z ≠ 0 :=
    (monic_polynomial_eval_ne_zero_ae (P ν) (hP ν)).filter_mono
    (ae_mono Measure.restrict_le_self)
  filter_upwards [hnz, ae_restrict_mem hK.measurableSet] with z hz hzK
  have hz32 : z ∈ ball (0 : ℂ) 32 :=
    (ball_subset_ball (by norm_num : (4 : ℝ) ≤ 32)) (hKU hzK)
  have hWz : FewInflection.wronskian n (g ν) z ≠ 0 := by rw [hW ν z hz32]; exact hz
  symm
  rw [canonical_logarithmicJet_normalized_eq_partition (fun i => hg ν i z hz32) hWz]
  congr 1
  funext j
  exact canonicalLogDerivative_jet_normalized_eq_polynomial isOpen_ball (P ν) (hW ν) hz32 j (s ν)

end
end ModifiedCartan
#print axioms ModifiedCartan.canonical_logarithmicJet_normalized_eq_partition
#print axioms ModifiedCartan.canonical_logarithmicJet_localMeasure_zero
