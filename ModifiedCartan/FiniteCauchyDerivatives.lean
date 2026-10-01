import ModifiedCartan.LocalizedRepresentation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric MeromorphicOn

set_option autoImplicit false

namespace ModifiedCartan

/-! Exact finite Cauchy-transform and derivative formulas for `eq:singular-logderivative`. -/

theorem integral_finiteZeroCountingMeasure_complex {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hfinite : (divisor f U).support.Finite) (φ : ℂ → ℂ) :
    (∫ a, φ a ∂finiteZeroCountingMeasure f U hfinite) =
      ∑ a ∈ hfinite.toFinset, (divisor f U a : ℂ) * φ a := by
  unfold finiteZeroCountingMeasure
  rw [integral_finsetSum_measure (fun a _ =>
    (integrable_dirac (f := φ) (a := a) (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_ofReal (by exact_mod_cast hf.divisor_nonneg a)]
  simp [Complex.real_smul]

theorem integral_localizedMeasure_complex (ν : Measure ℂ) [IsFiniteMeasure ν]
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ a, 0 ≤ χ a) (φ : ℂ → ℂ) :
    (∫ a, φ a ∂(localizedMeasure ν χ hχ hχc : Measure ℂ)) =
      ∫ a, (χ a : ℂ) * φ a ∂ν := by
  change (∫ a, φ a ∂ν.withDensity (fun a => ENNReal.ofReal (χ a))) = _
  simpa only [Complex.real_smul, ENNReal.toReal_ofReal (hχ0 _)] using
    integral_withDensity_eq_integral_toReal_smul (μ := ν) hχ.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) φ

theorem cauchyTransform_localizedZeroMeasure {f : ℂ → ℂ} {c : ℂ} {R s : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hs : 0 ≤ s)
    {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ a, 0 ≤ χ a) (z : ℂ) :
    cauchyTransform (localizedZeroMeasure hf s χ hχ hχc) z =
      ∑ a ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        ((s : ℂ)⁻¹ * (χ a : ℂ) * (divisor f (ball c R) a : ℂ)) * (z - a)⁻¹ := by
  rw [cauchyTransform, localizedZeroMeasure, integral_localizedMeasure_complex _ _ _
    (fun a => mul_nonneg (inv_nonneg.mpr hs) (hχ0 a)),
    integral_finiteZeroCountingMeasure_complex (hf.mono ball_subset_closedBall)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem iteratedDeriv_shifted_inv (j : ℕ) (a z : ℂ) :
    iteratedDeriv j (fun w : ℂ => (w - a)⁻¹) z =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) * (z - a)⁻¹ ^ (j + 1) := by
  rw [iteratedDeriv_comp_sub_const j (fun w : ℂ => w⁻¹) a]
  have h := iteratedDerivWithin_one_div (𝕜 := ℂ) j isOpen_univ (mem_univ (z - a))
  have he : (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) := by omega
  simpa only [iteratedDerivWithin_univ, one_div, he, zpow_neg, zpow_natCast, inv_pow] using h

theorem iteratedDeriv_finite_cauchy_sum {ι : Type*} (S : Finset ι) (a w : ι → ℂ)
    (j : ℕ) {z : ℂ} (hz : ∀ i ∈ S, z ≠ a i) :
    iteratedDeriv j (fun z => ∑ i ∈ S, w i * (z - a i)⁻¹) z =
      (-1 : ℂ) ^ j * (j.factorial : ℂ) *
        ∑ i ∈ S, w i / (z - a i) ^ (j + 1) := by
  have ha (i : ι) (hi : i ∈ S) : AnalyticAt ℂ (fun z => w i * (z - a i)⁻¹) z :=
    analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (hz i hi)))
  rw [iteratedDeriv_fun_sum (fun i hi => (ha i hi).contDiffAt)]
  simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_shifted_inv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, inv_pow]
  ring


end ModifiedCartan

