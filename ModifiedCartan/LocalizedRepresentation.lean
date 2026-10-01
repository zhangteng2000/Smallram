import ModifiedCartan.LocalizedMeasures

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric MeromorphicOn InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Harmonic remainders after smooth localization, for Step 1 of
`lem:logderivlimit`. The correction is an explicit finite weighted sum of log
kernels. Every potentially singular coefficient vanishes where the cutoff is
one, so the remainder is classically harmonic there. -/

theorem integral_localizedMeasure (ν : Measure ℂ) [IsFiniteMeasure ν]
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ a, 0 ≤ χ a) (φ : ℂ → ℝ) :
    (∫ a, φ a ∂(localizedMeasure ν χ hχ hχc : Measure ℂ)) = ∫ a, χ a * φ a ∂ν := by
  change (∫ a, φ a ∂ν.withDensity (fun a => ENNReal.ofReal (χ a))) = _
  simpa only [smul_eq_mul, ENNReal.toReal_ofReal (hχ0 _)] using
    integral_withDensity_eq_integral_toReal_smul (μ := ν) hχ.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) φ

theorem logPotential_localizedZeroMeasure {f : ℂ → ℂ} {c : ℂ} {R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hs : 0 ≤ s)
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ a, 0 ≤ χ a) (z : ℂ) :
    logPotential (localizedZeroMeasure hf s χ hχ hχc) z =
      ∑ a ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        (s⁻¹ * χ a) * ((divisor f (ball c R) a : ℝ) * Real.log ‖z - a‖) := by
  rw [logPotential, localizedZeroMeasure, integral_localizedMeasure _ _ _
    (fun a => mul_nonneg (inv_nonneg.mpr hs) (hχ0 a)),
    integral_finiteZeroCountingMeasure (hf.mono ball_subset_closedBall)]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem harmonicOnNhd_finsetSum {ι : Type*} (s : Finset ι) {U : Set ℂ}
    {f : ι → ℂ → ℝ} (hf : ∀ a ∈ s, HarmonicOnNhd (f a) U) :
    HarmonicOnNhd (fun z => ∑ a ∈ s, f a z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (harmonicOnNhd_const (s := U) (0 : ℝ))
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha, Pi.add_apply] using!
      (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem harmonicOnNhd_weighted_log_sum {U : Set ℂ} (s : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ a ∈ s, a ∈ U → w a = 0) :
    HarmonicOnNhd (fun z => ∑ a ∈ s, w a * Real.log ‖z - a‖) U := by
  apply harmonicOnNhd_finsetSum
  intro a ha z hz
  by_cases hw0 : w a = 0
  · simpa only [hw0, zero_mul] using (harmonicAt_const (x := z) (0 : ℝ))
  · have hza : z - a ≠ 0 := by
      intro hh
      have hza : z = a := sub_eq_zero.mp hh
      exact hw0 (hw a ha (hza ▸ hz))
    have hl := (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm hza
    convert! hl.const_smul (c := w a) using 1

theorem logNorm_eq_localized_potential_add_harmonic {f : ℂ → ℂ} {c b : ℂ} {R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : b ∈ ball c R) (hb0 : f b ≠ 0)
    (hs : 0 ≤ s) {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ a, 0 ≤ χ a) {V : Set ℂ} (hVU : V ⊆ ball c R)
    (hχV : ∀ a ∈ V, χ a = 1) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H V ∧
      (fun z => s⁻¹ * Real.log ‖f z‖) =ᵐ[volume.restrict V]
        (fun z => logPotential (localizedZeroMeasure hf s χ hχ hχc) z + H z) := by
  obtain ⟨H₀, hH₀, heq⟩ := logNorm_eq_logPotential_add_harmonic_on_ball hf hb hb0
  let S := hf.meromorphicOn.divisor_ball_support_finite.toFinset
  let w (a : ℂ) : ℝ := s⁻¹ * (1 - χ a) * (divisor f (ball c R) a : ℝ)
  let H (z : ℂ) : ℝ := s⁻¹ * H₀ z + ∑ a ∈ S, w a * Real.log ‖z - a‖
  have hsum : HarmonicOnNhd (fun z => ∑ a ∈ S, w a * Real.log ‖z - a‖) V := by
    apply harmonicOnNhd_weighted_log_sum
    intro a _ haV
    simp only [w, hχV a haV, sub_self, mul_zero, zero_mul]
  refine ⟨H, ?_, ?_⟩
  · exact ((hH₀.mono hVU).const_smul (c := s⁻¹)).add hsum
  · have heqV := heq.filter_mono (ae_mono (Measure.restrict_mono_set _ hVU))
    filter_upwards [heqV] with z hz
    rw [hz, logPotential_finiteZeroCountingMeasure (hf.mono ball_subset_closedBall),
      logPotential_localizedZeroMeasure hf hs hχ hχc hχ0]
    dsimp only [H, S, w]
    rw [mul_add, Finset.mul_sum]
    have hsplit : (∑ a ∈ S, s⁻¹ * ((divisor f (ball c R) a : ℝ) * Real.log ‖z - a‖)) =
        (∑ a ∈ S, (s⁻¹ * χ a) * ((divisor f (ball c R) a : ℝ) * Real.log ‖z - a‖)) +
        ∑ a ∈ S, (s⁻¹ * (1 - χ a) * (divisor f (ball c R) a : ℝ)) * Real.log ‖z - a‖ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    dsimp only [S] at hsplit
    rw [hsplit]
    ring


end ModifiedCartan
