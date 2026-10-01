import ModifiedCartan.HarmonicWeak
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.MeasureTheory.Topology

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric MeromorphicOn

namespace ModifiedCartan

/-! Zero-counting Riesz measures and local logarithmic-potential representation
for Step 1 of `lem:logderivlimit`. The existing meromorphic zero/pole extraction
is converted to an almost-everywhere harmonic decomposition. The kernel and
harmonic distribution identities then prove the exact Laplacian formula.
On a closed disk, finiteness of the zero divisor and finite local orders are
derived from analyticity and one nonzero value in its interior. -/

theorem logNorm_eq_finite_sum_add_harmonic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : MeromorphicOn f U)
    (horder : ∀ z : U, meromorphicOrderAt f z ≠ ⊤)
    (hfinite : (divisor f U).support.Finite) :
    ∃ H : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd H U ∧
      (fun z => Real.log ‖f z‖) =ᵐ[volume.restrict U]
        (fun z => (∑ a ∈ hfinite.toFinset, (divisor f U a : ℝ) * Real.log ‖z - a‖) + H z) := by
  classical
  obtain ⟨g, hg, hg0, heq⟩ := hf.extract_zeros_poles horder hfinite
  refine ⟨fun z => Real.log ‖g z‖, ?_, ?_⟩
  · intro z hz
    exact (hg z hz).harmonicAt_log_norm (hg0 ⟨z, hz⟩)
  · have hlog := ae_restrict_le_codiscreteWithin (μ := volume) hU.measurableSet
      (MeromorphicOn.extract_zeros_poles_log hg0 heq)
    have hs : Function.support (fun a : ℂ => fun z : ℂ =>
        (divisor f U a : ℝ) * Real.log ‖z - a‖) ⊆ (hfinite.toFinset : Set ℂ) := by
      intro a ha
      apply hfinite.mem_toFinset.mpr
      by_contra hzero
      have hz : divisor f U a = 0 := by simpa only [Function.mem_support, not_not] using hzero
      apply ha
      simp only [hz, Int.cast_zero, zero_mul]
      rfl
    rw [finsum_eq_sum_of_support_subset _ hs] at hlog
    filter_upwards [hlog] with z hz
    simpa only [Pi.add_apply, Finset.sum_apply] using hz

theorem integrable_finite_log_sum_mul_test (s : Finset ℂ) (c : ℂ → ℝ)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun z => (∑ a ∈ s, c a * Real.log ‖z - a‖) * ψ z) := by
  have hi (a : ℂ) : Integrable (fun z => Real.log ‖z - a‖ * ψ z) :=
    (locallyIntegrable_logKernel a).integrable_smul_right_of_hasCompactSupport hψ hψc
  simp_rw [Finset.sum_mul, mul_assoc]
  exact integrable_finsetSum s (fun a _ => (hi a).const_mul (c a))

theorem integral_finite_log_sum_mul_laplacian (s : Finset ℂ) (c : ℂ → ℝ)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ z, (∑ a ∈ s, c a * Real.log ‖z - a‖) * Laplacian.laplacian φ z) =
      2 * Real.pi * ∑ a ∈ s, c a * φ a := by
  have hi (a : ℂ) : Integrable (fun z => Real.log ‖z - a‖ * Laplacian.laplacian φ z) :=
    (locallyIntegrable_logKernel a).integrable_smul_right_of_hasCompactSupport
      (continuous_laplacian_complex hφ) (hasCompactSupport_laplacian_complex hφ hφc)
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum s (fun a _ => (hi a).const_mul (c a))]
  simp_rw [integral_const_mul, integral_logKernel_mul_laplacian _ hφ hφc]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem integral_logNorm_mul_laplacian_eq_divisor {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : MeromorphicOn f U)
    (horder : ∀ z : U, meromorphicOrderAt f z ≠ ⊤)
    (hfinite : (divisor f U).support.Finite)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ z, Real.log ‖f z‖ * Laplacian.laplacian φ z) =
      2 * Real.pi * ∑ a ∈ hfinite.toFinset, (divisor f U a : ℝ) * φ a := by
  obtain ⟨H, hH, heq⟩ := logNorm_eq_finite_sum_add_harmonic hU hf horder hfinite
  have hLapU : tsupport (Laplacian.laplacian φ) ⊆ U :=
    (tsupport_laplacian_complex_subset hφ).trans hφU
  have hglobal : (fun z => Real.log ‖f z‖ * Laplacian.laplacian φ z) =ᵐ[volume]
      (fun z => ((∑ a ∈ hfinite.toFinset, (divisor f U a : ℝ) * Real.log ‖z - a‖) + H z) *
        Laplacian.laplacian φ z) := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp heq] with z hz
    by_cases hzU : z ∈ U
    · rw [hz hzU]
    · have hz0 : Laplacian.laplacian φ z = 0 := by
        by_contra hh
        exact hzU (hLapU (subset_closure hh))
      simp only [hz0, mul_zero]
  rw [integral_congr_ae hglobal]
  simp_rw [add_mul]
  rw [integral_add
    (integrable_finite_log_sum_mul_test hfinite.toFinset (fun a => (divisor f U a : ℝ))
      (continuous_laplacian_complex hφ) (hasCompactSupport_laplacian_complex hφ hφc))
    (integrable_mul_test_of_continuousOn hU hH.contDiffOn.continuousOn
      (continuous_laplacian_complex hφ) (hasCompactSupport_laplacian_complex hφ hφc) hLapU),
    integral_harmonic_mul_laplacian_test hU hH hφ hφc hφU, add_zero]
  exact integral_finite_log_sum_mul_laplacian _ _ hφ hφc

noncomputable def finiteZeroCountingMeasure (f : ℂ → ℂ) (U : Set ℂ)
    (hfinite : (divisor f U).support.Finite) : Measure ℂ :=
  ∑ a ∈ hfinite.toFinset, ENNReal.ofReal (divisor f U a : ℝ) • Measure.dirac a

instance finiteZeroCountingMeasure_isFinite (f : ℂ → ℂ) (U : Set ℂ)
    (hfinite : (divisor f U).support.Finite) : IsFiniteMeasure (finiteZeroCountingMeasure f U hfinite) := by
  refine ⟨?_⟩
  simp only [finiteZeroCountingMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)

theorem finiteZeroCountingMeasure_ae_mem {f : ℂ → ℂ} {U S : Set ℂ}
    (hfinite : (divisor f U).support.Finite)
    (hS : ∀ a ∈ hfinite.toFinset, a ∈ S) :
    ∀ᵐ a ∂finiteZeroCountingMeasure f U hfinite, a ∈ S := by
  rw [ae_iff, finiteZeroCountingMeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  have hn : a ∉ {z : ℂ | ¬z ∈ S} := by simpa only [mem_ofPred_eq, not_not] using hS a ha
  rw [Measure.smul_apply, Measure.dirac_apply, indicator_of_notMem hn]
  exact mul_zero _

theorem finiteZeroCountingMeasure_ae_mem_domain {f : ℂ → ℂ} {U : Set ℂ}
    (hfinite : (divisor f U).support.Finite) :
    ∀ᵐ a ∂finiteZeroCountingMeasure f U hfinite, a ∈ U :=
  finiteZeroCountingMeasure_ae_mem hfinite fun _a ha =>
    (divisor f U).supportWithinDomain (hfinite.mem_toFinset.mp ha)

theorem finiteZeroCountingMeasure_ae_mem_compact {f : ℂ → ℂ} {U : Set ℂ}
    (hfinite : (divisor f U).support.Finite) :
    ∃ S : Set ℂ, IsCompact S ∧ S ⊆ U ∧
      ∀ᵐ a ∂finiteZeroCountingMeasure f U hfinite, a ∈ S := by
  refine ⟨(divisor f U).support, hfinite.isCompact, ?_, ?_⟩
  · exact (divisor f U).supportWithinDomain
  · exact finiteZeroCountingMeasure_ae_mem hfinite fun _a ha => hfinite.mem_toFinset.mp ha
theorem integral_finiteZeroCountingMeasure {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hfinite : (divisor f U).support.Finite) (φ : ℂ → ℝ) :
    (∫ a, φ a ∂finiteZeroCountingMeasure f U hfinite) =
      ∑ a ∈ hfinite.toFinset, (divisor f U a : ℝ) * φ a := by
  unfold finiteZeroCountingMeasure
  rw [integral_finsetSum_measure (fun a _ =>
    (integrable_dirac (f := φ) (a := a) (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_ofReal (by exact_mod_cast hf.divisor_nonneg a)]

theorem integral_logNorm_mul_laplacian_eq_zeroCounting {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (horder : ∀ z : U, meromorphicOrderAt f z ≠ ⊤)
    (hfinite : (divisor f U).support.Finite)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ z, Real.log ‖f z‖ * Laplacian.laplacian φ z) =
      2 * Real.pi * ∫ a, φ a ∂finiteZeroCountingMeasure f U hfinite := by
  rw [integral_finiteZeroCountingMeasure hf hfinite]
  exact integral_logNorm_mul_laplacian_eq_divisor hU hf.meromorphicOn horder hfinite hφ hφc hφU

theorem integral_logNorm_mul_laplacian_on_ball {f : ℂ → ℂ} {c b : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : b ∈ ball c R) (hb0 : f b ≠ 0)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ ball c R) :
    (∫ z, Real.log ‖f z‖ * Laplacian.laplacian φ z) =
      2 * Real.pi * ∫ a, φ a ∂finiteZeroCountingMeasure f (ball c R)
        hf.meromorphicOn.divisor_ball_support_finite := by
  have horderb : meromorphicOrderAt f b ≠ ⊤ := by
    rw [(hf b (ball_subset_closedBall hb)).meromorphicOrderAt_eq,
      (hf b (ball_subset_closedBall hb)).analyticOrderAt_eq_zero.mpr hb0]
    simp
  have horder : ∀ z : ball c R, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    exact hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected (ball_subset_closedBall hb)
      (ball_subset_closedBall z.property) horderb
  exact integral_logNorm_mul_laplacian_eq_zeroCounting isOpen_ball
    (hf.mono ball_subset_closedBall) horder hf.meromorphicOn.divisor_ball_support_finite hφ hφc hφU

theorem logPotential_finiteZeroCountingMeasure {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hfinite : (divisor f U).support.Finite) (z : ℂ) :
    logPotential (finiteZeroCountingMeasure f U hfinite) z =
      ∑ a ∈ hfinite.toFinset, (divisor f U a : ℝ) * Real.log ‖z - a‖ :=
  integral_finiteZeroCountingMeasure hf hfinite (fun a => Real.log ‖z - a‖)

theorem logNorm_eq_logPotential_add_harmonic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (horder : ∀ z : U, meromorphicOrderAt f z ≠ ⊤)
    (hfinite : (divisor f U).support.Finite) :
    ∃ H : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd H U ∧
      (fun z => Real.log ‖f z‖) =ᵐ[volume.restrict U]
        (fun z => logPotential (finiteZeroCountingMeasure f U hfinite) z + H z) := by
  simpa only [logPotential_finiteZeroCountingMeasure hf hfinite] using
    logNorm_eq_finite_sum_add_harmonic hU hf.meromorphicOn horder hfinite

theorem logNorm_eq_logPotential_add_harmonic_on_ball {f : ℂ → ℂ} {c b : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : b ∈ ball c R) (hb0 : f b ≠ 0) :
    ∃ H : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd H (ball c R) ∧
      (fun z => Real.log ‖f z‖) =ᵐ[volume.restrict (ball c R)]
        (fun z => logPotential (finiteZeroCountingMeasure f (ball c R)
          hf.meromorphicOn.divisor_ball_support_finite) z + H z) := by
  have horderb : meromorphicOrderAt f b ≠ ⊤ := by
    rw [(hf b (ball_subset_closedBall hb)).meromorphicOrderAt_eq,
      (hf b (ball_subset_closedBall hb)).analyticOrderAt_eq_zero.mpr hb0]
    simp
  have horder : ∀ z : ball c R, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    exact hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected (ball_subset_closedBall hb)
      (ball_subset_closedBall z.property) horderb
  exact logNorm_eq_logPotential_add_harmonic isOpen_ball
    (hf.mono ball_subset_closedBall) horder hf.meromorphicOn.divisor_ball_support_finite


end ModifiedCartan








