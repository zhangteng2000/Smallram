import ModifiedCartan.SecondOrderTaylor
import ModifiedCartan.QuadraticTrace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A uniform second-derivative error on the segment controls the quadratic
Taylor error. The coarse constant suffices for a vanishing-radius argument. -/
theorem second_order_taylor_error_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (c z : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ f) (c + t • z) - fderiv ℝ (fderiv ℝ f) c‖ ≤ ε) :
    ‖f (c + z) - f c - fderiv ℝ f c z -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) c z z‖ ≤ ε * ‖z‖ ^ 2 := by
  let B := fderiv ℝ (fderiv ℝ f)
  have hcf : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
  have hB : Continuous B := hcf.continuous_fderiv one_ne_zero
  have hc : Continuous (fun t : ℝ => (1 - t) * B (c + t • z) z z) :=
    (continuous_const.sub continuous_id).mul
      (((hB.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const).clm_apply continuous_const)
  have hc0 : Continuous (fun t : ℝ => (1 - t) * B c z z) := by fun_prop
  have hi0 : (∫ t in (0 : ℝ)..1, (1 - t) * B c z z) = (1 / 2 : ℝ) * B c z z := by
    rw [intervalIntegral.integral_mul_const]
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
      (continuous_const.intervalIntegrable 0 1)
      (continuous_id.intervalIntegrable 0 1)]
    norm_num [intervalIntegral.integral_const, integral_id]
  have he : f (c + z) - f c - fderiv ℝ f c z - (1 / 2 : ℝ) * B c z z =
      ∫ t in (0 : ℝ)..1, (1 - t) * (B (c + t • z) - B c) z z := by
    simp only [ContinuousLinearMap.sub_apply, mul_sub]
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable 0 1) (hc0.intervalIntegrable 0 1), hi0]
    rw [second_order_integral_taylor hf c z]
    change _ + _ + (∫ t in (0 : ℝ)..1, (1 - t) * B (c + t • z) z z) - _ - _ - _ = _
    ring
  rw [he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := ε * ‖z‖ ^ 2) (f := fun t => (1 - t) * (B (c + t • z) - B c) z z) (by
      intro t ht
      have htI : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨htI.1.le, htI.2⟩
      have hbil : ‖(B (c + t • z) - B c) z z‖ ≤ ε * ‖z‖ ^ 2 := by
        calc
          _ ≤ ‖(B (c + t • z) - B c) z‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (‖B (c + t • z) - B c‖ * ‖z‖) * ‖z‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
          _ ≤ (ε * ‖z‖) * ‖z‖ := by gcongr; exact hb t ht'
          _ = ε * ‖z‖ ^ 2 := by ring
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht'.2)]
      calc
        _ ≤ (1 - t) * (ε * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left hbil (sub_nonneg.mpr ht'.2)
        _ ≤ 1 * (ε * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith [ht'.1]) (mul_nonneg hε (sq_nonneg _))
        _ = ε * ‖z‖ ^ 2 := one_mul _)
  simpa only [sub_zero, abs_one, mul_one] using hh

/-- The second-order Taylor error is uniformly o(norm z squared) near
the center, in the explicit epsilon-radius form used below. -/
theorem exists_second_order_taylor_error_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ →
      ‖f (c + z) - f c - fderiv ℝ f c z -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) c z z‖ ≤ ε * ‖z‖ ^ 2 := by
  let B : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ f)
  have hcf : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv.mp hf).2.2
  have hB : Continuous B := hcf.continuous_fderiv one_ne_zero
  let q : ℂ → ℝ := fun y => |B y 1 1 - B c 1 1| +
    |B y 1 Complex.I - B c 1 Complex.I| + |B y Complex.I 1 - B c Complex.I 1| +
    |B y Complex.I Complex.I - B c Complex.I Complex.I|
  have hbcont (v w : ℂ) : Continuous (fun y => B y v w) :=
    (hB.clm_apply continuous_const).clm_apply continuous_const
  have hq : Continuous q := by
    exact ((((hbcont 1 1).sub continuous_const).abs.add
      ((hbcont 1 Complex.I).sub continuous_const).abs).add
      ((hbcont Complex.I 1).sub continuous_const).abs).add
      ((hbcont Complex.I Complex.I).sub continuous_const).abs
  have ht : Tendsto q (𝓝 c) (𝓝 0) := by
    simpa only [q, sub_self, abs_zero, add_zero] using hq.tendsto c
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨δ, hδ, fun z hz => second_order_taylor_error_bound hf c z hε.le ?_⟩
  intro t ht
  have hnear : dist (c + t • z) c < δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)).trans_lt (by simpa using hz)
  have hcoord : ‖B (c + t • z) - B c‖ ≤ q (c + t • z) := by
    simpa only [ContinuousLinearMap.sub_apply, q] using
      norm_complex_bilinear_le_coordinates (B (c + t • z) - B c)
  exact hcoord.trans (show q (c + t • z) < ε from hd hnear).le

end ModifiedCartan
#print axioms ModifiedCartan.exists_second_order_taylor_error_bound
