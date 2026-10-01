import ModifiedCartan.LogLaplacian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Local integration by parts for the Riesz representation in `lem:logderivlimit`.
All derivatives of the function are only required on the open domain; compact
tests justify integrability. Classical harmonic functions have zero weak
Laplacian, and local L1 convergence passes to Laplacian test integrals. -/

theorem continuous_mul_test_of_continuousAt {u φ : ℂ → ℝ}
    (hu : ∀ z ∈ tsupport φ, ContinuousAt u z) (hφ : Continuous φ) :
    Continuous (fun z => u z * φ z) :=
  continuous_of_tsupport fun z hz =>
    (hu z (tsupport_mul_subset_right hz)).mul hφ.continuousAt

theorem integrable_mul_test_of_continuousOn {U : Set ℂ} (hU : IsOpen U)
    {u φ : ℂ → ℝ} (hu : ContinuousOn u U) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun z => u z * φ z) :=
  (continuous_mul_test_of_continuousAt
    (fun _z hz => hu.continuousAt (hU.mem_nhds (hφU hz))) hφ).integrable_of_hasCompactSupport
    hφc.mul_left

theorem integral_mul_test_fderiv_of_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {u φ : ℂ → ℝ} (hu : ContDiffOn ℝ 1 u U) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : ℂ) :
    (∫ z, u z * fderiv ℝ φ z v) = -(∫ z, fderiv ℝ u z v * φ z) := by
  have hdu : ContinuousOn (fun z => fderiv ℝ u z v) U :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hdφ : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_test_of_continuousOn hU hdu hφ.continuous hφc hφU)
    (integrable_mul_test_of_continuousOn hU hu.continuousOn hdφ (hφc.fderiv_apply ℝ v)
      ((tsupport_fderiv_apply_subset ℝ v).trans hφU))
    (integrable_mul_test_of_continuousOn hU hu.continuousOn hφ.continuous hφc hφU)
    (fun z hz => (hu.contDiffAt (hU.mem_nhds (hφU hz))).differentiableAt one_ne_zero)
    (fun z _ => hφ.differentiable_one z)

theorem integral_mul_test_second_fderiv_of_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {u φ : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u U) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : ℂ) :
    (∫ z, u z * fderiv ℝ (fun w => fderiv ℝ φ w v) z v) =
      ∫ z, fderiv ℝ (fun w => fderiv ℝ u w v) z v * φ z := by
  have hu1 : ContDiffOn ℝ 1 u U := hu.of_le (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hdu : ContDiffOn ℝ 1 (fun z => fderiv ℝ u z v) U :=
    (hu.fderiv_of_isOpen hU (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply contDiffOn_const
  have hdφ : ContDiff ℝ 1 (fun z => fderiv ℝ φ z v) :=
    (contDiff_one_fderiv_of_two hφ).clm_apply contDiff_const
  rw [integral_mul_test_fderiv_of_contDiffOn hU hu1 hdφ (hφc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hφU),
    integral_mul_test_fderiv_of_contDiffOn hU hdu hφ1 hφc hφU, neg_neg]

theorem laplacian_complex_eq_coordinate_derivatives_on {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u U) {z : ℂ} (hz : z ∈ U) :
    Laplacian.laplacian u z = fderiv ℝ (fun w => fderiv ℝ u w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ u w Complex.I) z Complex.I := by
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ u) U :=
    hu.fderiv_of_isOpen hU (by norm_num)
  have heq (v : ℂ) : fderiv ℝ (fun w => fderiv ℝ u w v) z v =
      fderiv ℝ (fderiv ℝ u) z v v := by
    rw [fderiv_clm_apply ((hdf.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
      (differentiableAt_const v)]
    simp
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply, heq]
  rfl

theorem integral_mul_laplacian_test {U : Set ℂ} (hU : IsOpen U)
    {u φ : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u U) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ z, u z * Laplacian.laplacian φ z) = ∫ z, Laplacian.laplacian u z * φ z := by
  have hdφ (v : ℂ) : ContDiff ℝ 1 (fun z => fderiv ℝ φ z v) :=
    (contDiff_one_fderiv_of_two hφ).clm_apply contDiff_const
  have hdu (v : ℂ) : ContDiffOn ℝ 1 (fun z => fderiv ℝ u z v) U :=
    (hu.fderiv_of_isOpen hU (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply contDiffOn_const
  have hleft (v : ℂ) :
      Integrable (fun z => u z * fderiv ℝ (fun w => fderiv ℝ φ w v) z v) := by
    apply integrable_mul_test_of_continuousOn hU hu.continuousOn
      (((hdφ v).continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const))
      ((hφc.fderiv_apply ℝ v).fderiv_apply ℝ v)
    exact (tsupport_fderiv_apply_subset ℝ v).trans
      ((tsupport_fderiv_apply_subset ℝ v).trans hφU)
  have hright (v : ℂ) :
      Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ u w v) z v * φ z) := by
    apply integrable_mul_test_of_continuousOn hU _ hφ.continuous hφc hφU
    exact ((hdu v).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  calc
    _ = (∫ z, u z * fderiv ℝ (fun w => fderiv ℝ φ w 1) z 1) +
        ∫ z, u z * fderiv ℝ (fun w => fderiv ℝ φ w Complex.I) z Complex.I := by
      simp_rw [laplacian_complex_eq_coordinate_derivatives hφ, mul_add]
      exact integral_add (hleft 1) (hleft Complex.I)
    _ = (∫ z, fderiv ℝ (fun w => fderiv ℝ u w 1) z 1 * φ z) +
        ∫ z, fderiv ℝ (fun w => fderiv ℝ u w Complex.I) z Complex.I * φ z := by
      rw [integral_mul_test_second_fderiv_of_contDiffOn hU hu hφ hφc hφU,
        integral_mul_test_second_fderiv_of_contDiffOn hU hu hφ hφc hφU]
    _ = ∫ z, (fderiv ℝ (fun w => fderiv ℝ u w 1) z 1 +
        fderiv ℝ (fun w => fderiv ℝ u w Complex.I) z Complex.I) * φ z := by
      simp_rw [add_mul]
      exact (integral_add (hright 1) (hright Complex.I)).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only
      by_cases hz : φ z = 0
      · simp only [hz, mul_zero]
      · rw [laplacian_complex_eq_coordinate_derivatives_on hU hu (hφU (subset_closure hz))]

theorem integral_harmonic_mul_laplacian_test {U : Set ℂ} (hU : IsOpen U)
    {u φ : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ z, u z * Laplacian.laplacian φ z) = 0 := by
  rw [integral_mul_laplacian_test hU hu.contDiffOn hφ hφc hφU]
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  by_cases hz : φ z = 0
  · exact mul_eq_zero.mpr (Or.inr hz)
  · have hl := (hu z (hφU (subset_closure hz))).2.eq_of_nhds
    change Laplacian.laplacian u z = 0 at hl
    simp only [hl, zero_mul, Pi.zero_apply]

theorem tsupport_laplacian_complex_subset {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    tsupport (Laplacian.laplacian φ) ⊆ tsupport φ := by
  have heq : Laplacian.laplacian φ = fun z =>
      fderiv ℝ (fun w => fderiv ℝ φ w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ φ w Complex.I) z Complex.I :=
    funext (laplacian_complex_eq_coordinate_derivatives hφ)
  rw [heq]
  apply (tsupport_add _ _).trans
  exact union_subset
    ((tsupport_fderiv_apply_subset ℝ 1).trans (tsupport_fderiv_apply_subset ℝ 1))
    ((tsupport_fderiv_apply_subset ℝ Complex.I).trans (tsupport_fderiv_apply_subset ℝ Complex.I))

theorem LocalLpConvergence.laplacian_test_integral {U : Set ℂ}
    {u : ℕ → ℂ → ℝ} {u₀ φ : ℂ → ℝ} (hu : LocalLpConvergence 1 U u u₀)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Tendsto (fun n => ∫ z, u n z * Laplacian.laplacian φ z) atTop
      (𝓝 (∫ z, u₀ z * Laplacian.laplacian φ z)) := by
  simpa only [mul_comm] using hu.compactlySupported_test_integral
    (continuous_laplacian_complex hφ) (hasCompactSupport_laplacian_complex hφ hφc)
    ((tsupport_laplacian_complex_subset hφ).trans hφU)


end ModifiedCartan






