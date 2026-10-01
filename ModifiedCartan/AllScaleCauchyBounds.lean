import ModifiedCartan.CanonicalDilation
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem exponent_eq_zero_of_positive_le_all_rpow {d C p : ℝ} (hd : 0 < d)
    (hbound : ∀ R : ℝ, 0 < R → d ≤ C * R ^ p) : p = 0 := by
  have hC : 0 < C := hd.trans_le (by simpa only [Real.one_rpow, mul_one] using hbound 1 zero_lt_one)
  by_contra hp
  let R : ℝ := Real.exp (Real.log (d / (2 * C)) / p)
  have hR : 0 < R := Real.exp_pos _
  have hpow : R ^ p = d / (2 * C) := by
    rw [Real.rpow_def_of_pos hR]
    dsimp only [R]
    rw [Real.log_exp, div_mul_cancel₀ _ hp, Real.exp_log (by positivity)]
  have hb := hbound R hR
  rw [hpow] at hb
  have heq : C * (d / (2 * C)) = d / 2 := by field_simp
  rw [heq] at hb
  linarith

theorem exists_nonzero_iteratedDeriv_at_center {a : ℂ → ℂ} {r : ℝ}
    (ha : AnalyticOnNhd ℂ a (ball 0 r)) (hne : ∃ z ∈ ball (0 : ℂ) r, a z ≠ 0) :
    ∃ m : ℕ, iteratedDeriv m a 0 ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨z, hz, haz⟩ := hne
  have hseries := Complex.taylorSeries_eq_on_ball ha.differentiableOn hz
  simp only [hn, smul_zero, tsum_zero] at hseries
  exact haz hseries.symm

/-- A germ identity under dilation transfers the uniform unit-disk bound
to an explicit derivative bound. It is the Cauchy step of `prop:indices`. -/
theorem norm_iteratedDeriv_le_of_dilation_germ {a b : ℂ → ℂ} {p K R : ℝ}
    (hR : 0 < R) (ha : AnalyticAt ℂ a 0)
    (hb : AnalyticOnNhd ℂ b (ball 0 4))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K)
    (hrel : (fun z : ℂ => a ((R : ℂ) * z)) =ᶠ[𝓝 0]
      (fun z => (R ^ p : ℝ) * b z)) (m : ℕ) :
    ‖iteratedDeriv m a 0‖ ≤
      ((m.factorial : ℝ) * K / (1 / 2 : ℝ) ^ m) * R ^ (p - m) := by
  have hd := hrel.iteratedDeriv_eq m
  rw [iteratedDeriv_dilate_at (R : ℂ) m (by simpa only [mul_zero] using ha),
    mul_zero, iteratedDeriv_const_mul_field] at hd
  have hdNorm := congrArg norm hd
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hR.le p)] at hdNorm
  have hDb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m
    (by norm_num : (0 : ℝ) < 1 / 2)
    (hb.differentiableOn.diffContOnCl_ball (closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 4)))
    (fun z hz => hbound z ((closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1))
      (sphere_subset_closedBall hz)))
  rw [Real.rpow_sub_natCast hR.ne', ← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hR m)).mpr
  calc
    ‖iteratedDeriv m a 0‖ * R ^ m = R ^ p * ‖iteratedDeriv m b 0‖ := by
      rw [mul_comm]
      exact hdNorm
    _ ≤ R ^ p * ((m.factorial : ℝ) * K / (1 / 2 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hDb (Real.rpow_nonneg hR.le p)
    _ = _ := mul_comm _ _

/-- The local version of Step 3 of `prop:indices`. Uniformly bounded analytic
representatives at every scale force a nonzero germ to have integral weight.
No global entire limit or unproved compactness assertion is assumed here. -/
theorem dilation_weight_eq_nat_of_uniform_local_bounds {a : ℂ → ℂ} {p K : ℝ}
    (ha : AnalyticOnNhd ℂ a (ball 0 4))
    (hne : ∃ z ∈ ball (0 : ℂ) 4, a z ≠ 0)
    (hscale : ∀ R : ℝ, 0 < R → ∃ b : ℂ → ℂ,
      AnalyticOnNhd ℂ b (ball 0 4) ∧ (∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K) ∧
      (fun z : ℂ => a ((R : ℂ) * z)) =ᶠ[𝓝 0] (fun z => (R ^ p : ℝ) * b z)) :
    ∃ m : ℕ, p = m ∧ iteratedDeriv m a 0 ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_nonzero_iteratedDeriv_at_center ha hne
  refine ⟨m, ?_, hm⟩
  have he : p - (m : ℝ) = 0 := exponent_eq_zero_of_positive_le_all_rpow
    (norm_pos_iff.mpr hm) (C := (m.factorial : ℝ) * K / (1 / 2 : ℝ) ^ m) (by
      intro R hR
      obtain ⟨b, hb, hbound, hrel⟩ := hscale R hR
      exact norm_iteratedDeriv_le_of_dilation_germ hR (ha 0 (mem_ball_self (by norm_num)))
        hb hbound hrel m)
  exact sub_eq_zero.mp he

end ModifiedCartan
#print axioms ModifiedCartan.dilation_weight_eq_nat_of_uniform_local_bounds
