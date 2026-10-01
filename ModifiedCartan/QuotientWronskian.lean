import ModifiedCartan.WronskianLogInequality
import ModifiedCartan.NegativeLogKernel
import ModifiedCartan.RescaledGauge

open scoped Topology BigOperators Classical
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem normalizedWronskian_one_scalar_mul {n : ℕ} {g : Index n → ℂ → ℂ}
    {η : ℂ → ℂ} {z : ℂ} (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hη : AnalyticAt ℂ η z) (hη0 : η z ≠ 0) :
    normalizedWronskian n 1 (fun j w => η w * g j w) z = normalizedWronskian n 1 g z := by
  rw [normalizedWronskian_eq_div, normalizedWronskian_eq_div,
    FewInflection.wronskian_scalar_mul η g z hη.contDiffAt (fun j => (hg j).contDiffAt)]
  simp only [Complex.ofReal_one, one_pow, one_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hη0)

theorem normalizedWronskian_one_quotients {n : ℕ} {g : Index n → ℂ → ℂ}
    {z : ℂ} (hg : ∀ j, AnalyticAt ℂ (g j) z) (j : Index n) (hj : g j z ≠ 0) :
    normalizedWronskian n 1 (fun l w => g l w / g j w) z = normalizedWronskian n 1 g z := by
  have hη : AnalyticAt ℂ (fun w => (g j w)⁻¹) z := (hg j).inv hj
  simpa only [div_eq_mul_inv, mul_comm] using
    normalizedWronskian_one_scalar_mul hg hη (inv_ne_zero hj)

theorem normalizedWronskian_rescaled_quotients {n : ℕ} (f : Curve n) (t : ℝ)
    {H : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z) (j : Index n)
    (hj : f.coord j ((t : ℂ) * z) ≠ 0) :
    normalizedWronskian n 1 (rescaledRepresentation f t H) z =
      normalizedWronskian n 1
        (fun l w => f.coord l ((t : ℂ) * w) / f.coord j ((t : ℂ) * w)) z := by
  have hg : ∀ l, AnalyticAt ℂ (fun w => f.coord l ((t : ℂ) * w)) z := fun l =>
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic l)
      _ (mem_univ _)).fun_comp (analyticAt_const.fun_mul analyticAt_id)
  have hη : AnalyticAt ℂ (fun w => Complex.exp (-H w)) z := hH.neg.cexp
  exact (normalizedWronskian_one_scalar_mul hg hη (Complex.exp_ne_zero _)).trans
    (normalizedWronskian_one_quotients hg j hj).symm

theorem wronskian_euclidean_negative_bound {n : ℕ} {g : Index n → ℂ → ℂ}
    {z : ℂ} (hg0 : ∀ j, g j z ≠ 0) (hW : FewInflection.wronskian n g z ≠ 0) :
    (n + 1 : ℝ) * max 0 (-Real.log (euclideanNorm (fun j => g j z))) ≤
      negativeLogNorm (FewInflection.wronskian n g z) + logPlusNorm (normalizedWronskian n 1 g z) := by
  have hbase := wronskian_log_sum_lower_bound (by norm_num : (0 : ℝ) < 1) hg0 hW
  simp only [inv_one, one_mul, Real.log_one, mul_zero, sub_zero] at hbase
  have hsum : (∑ j : Index n, Real.log ‖g j z‖) ≤
      (n + 1 : ℝ) * Real.log (euclideanNorm (fun j => g j z)) := by
    calc
      _ ≤ ∑ _j : Index n, Real.log (euclideanNorm (fun j => g j z)) := by
        apply Finset.sum_le_sum
        intro j _
        apply Real.log_le_log (norm_pos_iff.mpr (hg0 j))
        exact (norm_le_pi_norm (fun j => g j z) j).trans (norm_le_euclideanNorm _)
      _ = _ := by simp [Index, FewInflection.Index]
  have hneg : -Real.log ‖FewInflection.wronskian n g z‖ ≤
      negativeLogNorm (FewInflection.wronskian n g z) := le_max_right _ _
  have hpositive : 0 ≤ logPlusNorm (normalizedWronskian n 1 g z) :=
    Real.log_nonneg (le_max_right _ _)
  by_cases hu : 0 ≤ Real.log (euclideanNorm (fun j => g j z))
  · rw [max_eq_left (neg_nonpos.mpr hu), mul_zero]
    exact add_nonneg (negativeLogNorm_nonneg _) hpositive
  · rw [max_eq_right (by linarith : 0 ≤ -Real.log (euclideanNorm (fun j => g j z)))]
    linarith

/-- Pointwise estimate supporting LaTeX `eq:negativedeterminant` and
`eq:negativepart`. Any fixed nonvanishing coordinate may be used as the
denominator: the full normalized Wronskian is scalar-gauge invariant.
This avoids the measurable partition by a maximizing coordinate. -/
theorem rescaled_negative_norm_le_quotient_wronskian {n : ℕ} (f : Curve n) (t : ℝ)
    {H : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z)
    (hf0 : ∀ j, f.coord j ((t : ℂ) * z) ≠ 0)
    (hW : FewInflection.wronskian n (rescaledRepresentation f t H) z ≠ 0)
    (j : Index n) :
    (n + 1 : ℝ) * max 0 (-Real.log (euclideanNorm
      (fun l => rescaledRepresentation f t H l z))) ≤
      negativeLogNorm (FewInflection.wronskian n (rescaledRepresentation f t H) z) +
        logPlusNorm (normalizedWronskian n 1
          (fun l w => f.coord l ((t : ℂ) * w) / f.coord j ((t : ℂ) * w)) z) := by
  have hg0 : ∀ l, rescaledRepresentation f t H l z ≠ 0 := fun l =>
    mul_ne_zero (Complex.exp_ne_zero _) (hf0 l)
  have h := wronskian_euclidean_negative_bound hg0 hW
  rw [normalizedWronskian_rescaled_quotients f t hH j (hf0 j)] at h
  exact h

end
end ModifiedCartan
#print axioms ModifiedCartan.rescaled_negative_norm_le_quotient_wronskian
