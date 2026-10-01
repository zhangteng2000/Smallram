import ModifiedCartan.PolynomialNegativeArea
import ModifiedCartan.LocalJetDeterminantBounds
import ModifiedCartan.LocalConvergenceAlgebra

open scoped Topology BigOperators ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem localL1_zero_of_integral_norm {f : ℕ → ℂ → ℝ} {U : Set ℂ}
    (hint : ∀ K, IsCompact K → K ⊆ U → ∀ ν, IntegrableOn (f ν) K)
    (hlim : ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun ν => ∫ z in K, ‖f ν z‖) atTop (𝓝 0)) :
    LocalLpConvergence 1 U f (fun _ => 0) := by
  refine ⟨fun K hK hKU ν => memLp_one_iff_integrable.mpr (hint K hK hKU ν),
    fun _ _ _ => MemLp.zero', ?_⟩
  intro K hK hKU
  have he (ν : ℕ) : eLpNorm (f ν - (fun _ => 0)) 1 (volume.restrict K) =
      ENNReal.ofReal (∫ z in K, ‖f ν z‖) := by
    simp only [Pi.sub_def, sub_zero, eLpNorm_one_eq_lintegral_enorm]
    exact (ofReal_integral_norm_eq_lintegral_enorm (hint K hK hKU ν)).symm
  simp_rw [he]
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hlim K hK hKU)

theorem norm_monic_polynomial_le_of_roots_bounded (P : Polynomial ℂ) (hP : P.Monic)
    (hroots : ∀ a, P.eval a = 0 → ‖a‖ ≤ 64) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : z ∈ closedBall 0 R) : ‖P.eval z‖ ≤ (R + 64) ^ P.natDegree := by
  obtain ⟨a, ha⟩ := monic_polynomial_eval_root_product P hP
  have hroot (i : Fin P.natDegree) : ‖a i‖ ≤ 64 := by
    apply hroots
    rw [ha]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (a i))
  have hzn : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  rw [ha]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    norm_finset_prod_le_pow Finset.univ (fun i => z - a i) (by linarith : 0 ≤ R + 64)
      (fun i _ => (norm_sub_le z (a i)).trans (by linarith [hroot i]))

theorem log_norm_monic_polynomial_le_of_roots_bounded (P : Polynomial ℂ) (hP : P.Monic)
    (hroots : ∀ a, P.eval a = 0 → ‖a‖ ≤ 64) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    Real.log ‖P.eval z‖ ≤ (P.natDegree : ℝ) * Real.log (R + 64) := by
  by_cases hpz : P.eval z = 0
  · simp only [hpz, norm_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  · have h := Real.log_le_log (norm_pos_iff.mpr hpz)
      (norm_monic_polynomial_le_of_roots_bounded P hP hroots hR hz)
    rwa [Real.log_pow] at h

theorem integral_norm_log_monic_polynomial_le (P : Polynomial ℂ) (hP : P.Monic)
    (hroots : ∀ a, P.eval a = 0 → ‖a‖ ≤ 64)
    {K : Set ℂ} (hK : IsCompact K) {R : ℝ} (hR : 0 ≤ R) (hKR : K ⊆ closedBall 0 R) :
    (∫ z in K, ‖Real.log ‖P.eval z‖‖) ≤
      ((volume K).toReal * Real.log (R + 64) + Real.pi) * P.natDegree := by
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  have hi := integrableOn_log_norm_on_compact
    (fun z _ => AnalyticOnNhd.eval_polynomial P z (mem_univ z)) (subset_univ K) hK
  have hn := (integrable_negativeLogNorm_monic P hP).integrableOn (s := K)
  have hb := integral_mono_ae hi.norm
    ((integrable_const ((P.natDegree : ℝ) * Real.log (R + 64))).add (hn.const_mul 2)) (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      have hl := log_norm_monic_polynomial_le_of_roots_bounded P hP hroots hR (hKR hz)
      change |Real.log ‖P.eval z‖| ≤ (P.natDegree : ℝ) * Real.log (R + 64) +
        2 * max 0 (-Real.log ‖P.eval z‖)
      by_cases hp : 0 ≤ Real.log ‖P.eval z‖
      · rw [abs_of_nonneg hp, max_eq_left (neg_nonpos.mpr hp)]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp), max_eq_right (by linarith : 0 ≤ -Real.log ‖P.eval z‖)]
        linarith)
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const _) (hn.const_mul 2), integral_const_mul,
    setIntegral_const, smul_eq_mul] at hb
  simp only [integral_const_mul, Measure.real] at hb
  have hneg := Paper.eq_polynomial_negative_area P hP K
  nlinarith

/-- LaTeX `eq:small-polynomial-log`, including all polynomial zeros through
their integrable log-modulus representatives. -/
theorem Paper.eq_small_polynomial_log (P : ℕ → Polynomial ℂ) (hP : ∀ ν, (P ν).Monic)
    (hroots : ∀ ν a, (P ν).eval a = 0 → ‖a‖ ≤ 64) {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0)) :
    LocalLpConvergence 1 univ (fun ν z => Real.log ‖(P ν).eval z‖ / s ν) (fun _ => 0) := by
  apply localL1_zero_of_integral_norm
  · intro K hK _ ν
    exact (integrableOn_log_norm_on_compact
      (fun z _ => AnalyticOnNhd.eval_polynomial (P ν) z (mem_univ z)) (subset_univ K) hK).div_const _
  · intro K hK _
    obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    let A := (volume K).toReal * Real.log (R + 64) + Real.pi
    have hl := hm.const_mul A
    simp only [mul_zero] at hl
    apply squeeze_zero' (Eventually.of_forall (fun ν => integral_nonneg (fun z => norm_nonneg _))) _ hl
    filter_upwards [hs.eventually_gt_atTop 0] with ν hsν
    have he : (∫ z in K, ‖Real.log ‖(P ν).eval z‖ / s ν‖) =
        (∫ z in K, ‖Real.log ‖(P ν).eval z‖‖) / s ν := by
      simp_rw [norm_div, Real.norm_eq_abs, abs_of_pos hsν]
      rw [integral_div]
    rw [he]
    calc
      _ ≤ (A * ((P ν).natDegree : ℝ)) / s ν := div_le_div_of_nonneg_right
        (integral_norm_log_monic_polynomial_le (P ν) (hP ν) (hroots ν) hK hR.le hKR) hsν.le
      _ = _ := by ring

end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_small_polynomial_log
