import ModifiedCartan.LogRiesz
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Localized normalized zero-counting measures for Step 1 of `lem:logderivlimit`.
Compact smooth cutoffs and the proved distributional Laplacian identity give
mass convergence and uniform bounds directly from local L1 convergence. -/

noncomputable def localizedMeasure (ν : Measure ℂ) [IsFiniteMeasure ν]
    (χ : ℂ → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) : FiniteMeasure ℂ :=
  ⟨ν.withDensity (fun a => ENNReal.ofReal (χ a)),
    isFiniteMeasure_withDensity_ofReal (hχ.integrable_of_hasCompactSupport hχc).hasFiniteIntegral⟩

theorem localizedMeasure_real_univ (ν : Measure ℂ) [IsFiniteMeasure ν]
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ a, 0 ≤ χ a) :
    (localizedMeasure ν χ hχ hχc : Measure ℂ).real univ = ∫ a, χ a ∂ν := by
  change (ν.withDensity (fun a => ENNReal.ofReal (χ a))).real univ = _
  have h := integral_withDensity_eq_integral_toReal_smul (μ := ν)
    hχ.measurable.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
    (fun _ : ℂ => (1 : ℝ))
  simpa only [integral_const, smul_eq_mul, mul_one, ENNReal.toReal_ofReal (hχ0 _),
    localizedMeasure] using h

theorem localizedMeasure_ae_mem (ν : Measure ℂ) [IsFiniteMeasure ν]
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    ∀ᵐ a ∂(localizedMeasure ν χ hχ hχc : Measure ℂ), a ∈ tsupport χ := by
  apply (ae_withDensity_iff hχ.measurable.ennreal_ofReal).mpr
  apply Eventually.of_forall
  intro a ha
  apply subset_closure
  intro hz
  exact ha (by simp only [hz, ENNReal.ofReal_zero])

theorem localizedMeasure_restrict (ν : Measure ℂ) [IsFiniteMeasure ν]
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    {S : Set ℂ} (hS : MeasurableSet S) (hχS : ∀ a ∈ S, χ a = 1) :
    (localizedMeasure ν χ hχ hχc : Measure ℂ).restrict S = ν.restrict S := by
  change (ν.withDensity _).restrict S = _
  rw [restrict_withDensity hS]
  calc
    _ = (ν.restrict S).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hS] with a ha
      simp only [hχS a ha, ENNReal.ofReal_one, Pi.one_apply]
    _ = _ := withDensity_one

theorem exists_smooth_disk_cutoff (c : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ ball c R ∧ (∀ a, 0 ≤ χ a ∧ χ a ≤ 1) ∧
      ∀ a ∈ closedBall c r, χ a = 1 := by
  let χ : ContDiffBump c := ⟨r, (r + R) / 2, hr, by linarith⟩
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, ?_, ?_⟩
  · rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by dsimp [χ]; linarith)
  · intro a
    exact ⟨χ.nonneg, χ.le_one⟩
  · intro a ha
    exact χ.one_of_mem_closedBall ha


noncomputable def localizedZeroMeasure {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (s : ℝ)
    (χ : ℂ → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) : FiniteMeasure ℂ :=
  localizedMeasure (finiteZeroCountingMeasure f (ball c R)
    hf.meromorphicOn.divisor_ball_support_finite) (fun a => s⁻¹ * χ a)
    (continuous_const.mul hχ) hχc.mul_left

theorem localizedZeroMeasure_ae_mem {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (s : ℝ)
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    ∀ᵐ a ∂(localizedZeroMeasure hf s χ hχ hχc : Measure ℂ), a ∈ tsupport χ := by
  filter_upwards [localizedMeasure_ae_mem
    (finiteZeroCountingMeasure f (ball c R) hf.meromorphicOn.divisor_ball_support_finite)
    (continuous_const.mul hχ) (show HasCompactSupport (fun a => s⁻¹ * χ a) from hχc.mul_left)]
    with a ha
  exact (tsupport_mul_subset_right (f := fun _ : ℂ => s⁻¹) (g := χ)) ha

theorem localizedZeroMeasure_mass_eq {f : ℂ → ℂ} {c b : ℂ} {R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : b ∈ ball c R) (hb0 : f b ≠ 0)
    (hs : 0 ≤ s) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ ball c R) (hχ0 : ∀ a, 0 ≤ χ a) :
    (localizedZeroMeasure hf s χ hχ.continuous hχc : Measure ℂ).real univ =
      (2 * Real.pi)⁻¹ * ∫ z, (s⁻¹ * Real.log ‖f z‖) * Laplacian.laplacian χ z := by
  rw [localizedZeroMeasure, localizedMeasure_real_univ _ _ _
    (fun a => mul_nonneg (inv_nonneg.mpr hs) (hχ0 a)), integral_const_mul]
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_logNorm_mul_laplacian_on_ball hf hb hb0 hχ hχc hχU]
  field_simp

theorem LocalLpConvergence.localizedZeroMeasure_mass_tendsto {U : Set ℂ}
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hball : ball c R ⊆ U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 ≤ s n)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ ball c R) (hχ0 : ∀ a, 0 ≤ χ a) :
    Tendsto (fun n => (localizedZeroMeasure (hf n) (s n) χ hχ.continuous hχc :
      Measure ℂ).real univ) atTop
      (𝓝 ((2 * Real.pi)⁻¹ * ∫ z, u z * Laplacian.laplacian χ z)) := by
  have heq (n : ℕ) :
      (localizedZeroMeasure (hf n) (s n) χ hχ.continuous hχc : Measure ℂ).real univ =
        (2 * Real.pi)⁻¹ * ∫ z, ((s n)⁻¹ * Real.log ‖f n z‖) * Laplacian.laplacian χ z := by
    obtain ⟨b, hb, hb0⟩ := hnonzero n
    exact localizedZeroMeasure_mass_eq (hf n) hb hb0 (hs n) hχ hχc hχU hχ0
  simp_rw [heq]
  exact (hu.laplacian_test_integral hχ hχc (hχU.trans hball)).const_mul _

theorem LocalLpConvergence.localizedZeroMeasure_mass_bounded {U : Set ℂ}
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : LocalLpConvergence 1 U (fun n z => (s n)⁻¹ * Real.log ‖f n z‖) u)
    (hball : ball c R ⊆ U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hnonzero : ∀ n, ∃ b ∈ ball c R, f n b ≠ 0) (hs : ∀ n, 0 ≤ s n)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ ball c R) (hχ0 : ∀ a, 0 ≤ χ a) :
    ∃ M : ℝ, 0 < M ∧ ∀ n,
      (localizedZeroMeasure (hf n) (s n) χ hχ.continuous hχc : Measure ℂ).real univ ≤ M := by
  have ht := hu.localizedZeroMeasure_mass_tendsto hball hf hnonzero hs hχ hχc hχU hχ0
  obtain ⟨M, hM0, hM⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_pos_norm_le
  refine ⟨M, hM0, fun n => ?_⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM _ (mem_range_self n))


end ModifiedCartan
