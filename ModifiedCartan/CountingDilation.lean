import ModifiedCartan.OpenDiskCounting
import ModifiedCartan.RescaledGauge

open scoped Topology BigOperators Classical
open Filter Set Metric MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem meromorphicTrailingCoeffAt_linear {t : ℂ} :
    meromorphicTrailingCoeffAt (fun z : ℂ => t * z) 0 = t := by
  have hc : MeromorphicAt (fun _ : ℂ => t) 0 := by fun_prop
  have hi : MeromorphicAt (fun z : ℂ => z) 0 := by fun_prop
  have hti : meromorphicTrailingCoeffAt (fun z : ℂ => z) 0 = 1 := by
    simpa using (meromorphicTrailingCoeffAt_id_sub_const (x := (0 : ℂ)) (y := 0))
  rw [hc.meromorphicTrailingCoeffAt_fun_mul hi, meromorphicTrailingCoeffAt_const, hti, mul_one]

theorem meromorphicTrailingCoeffAt_dilate {F : ℂ → ℂ}
    (hF : MeromorphicAt F 0) {t : ℂ} (ht : t ≠ 0) :
    meromorphicTrailingCoeffAt (fun z => F (t * z)) 0 =
      t ^ (meromorphicOrderAt F 0).untop₀ * meromorphicTrailingCoeffAt F 0 := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => t * z) 0 := by fun_prop
  have hord := hlin.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by
    simpa only [deriv_const_mul_id] using ht)
  have hnc : ¬EventuallyConst (fun z : ℂ => t * z) (𝓝 0) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hord]
    simp
  have hF' : MeromorphicAt F (t * 0) := by simpa using hF
  have hh := hF'.meromorphicTrailingCoeffAt_comp hlin hnc
  simpa only [Function.comp_def, mul_zero, sub_zero, meromorphicTrailingCoeffAt_linear,
    smul_eq_mul] using hh

theorem log_trailingCoeff_dilate {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∃ z, F z ≠ 0) {t : ℝ} (ht : 0 < t) :
    Real.log ‖meromorphicTrailingCoeffAt (fun z => F ((t : ℂ) * z)) 0‖ =
      (divisor F univ 0 : ℝ) * Real.log t + Real.log ‖meromorphicTrailingCoeffAt F 0‖ := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have hf0 := (hA 0 (mem_univ _)).meromorphicAt
  have htrail := hf0.meromorphicTrailingCoeffAt_ne_zero (entire_meromorphicOrder_ne_top hF hF0 0)
  rw [meromorphicTrailingCoeffAt_dilate hf0 (Complex.ofReal_ne_zero.mpr ht.ne'),
    norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    Real.log_mul (zpow_ne_zero _ ht.ne') (norm_ne_zero_iff.mpr htrail), Real.log_zpow,
    hA.meromorphicOn.divisor_apply (mem_univ 0)]

theorem logCounting_real_dilate {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∃ z, F z ≠ 0) {t R : ℝ} (ht : 0 < t) (hR : 0 < R) :
    ValueDistribution.logCounting (fun z => F ((t : ℂ) * z)) (0 : WithTop ℂ) R =
      ValueDistribution.logCounting F (0 : WithTop ℂ) (t * R) -
        (divisor F univ 0 : ℝ) * Real.log t := by
  have hd : Differentiable ℂ (fun z => F ((t : ℂ) * z)) := hF.comp (by fun_prop)
  have hscaled := Paper.eq_zerojensen hd hR.ne'
  have horiginal := Paper.eq_zerojensen hF (mul_pos ht hR).ne'
  rw [circleAverage_real_dilate (fun z => Real.log ‖F z‖) t R,
    log_trailingCoeff_dilate hF hF0 ht] at hscaled
  linarith

theorem logCounting_const_mul {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∃ z, F z ≠ 0) {c : ℂ} (hc : c ≠ 0) (R : ℝ) :
    ValueDistribution.logCounting (fun z => c * F z) (0 : WithTop ℂ) R =
      ValueDistribution.logCounting F (0 : WithTop ℂ) R := by
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have hcA : AnalyticOnNhd ℂ (fun _ : ℂ => c) univ := fun _ _ => analyticAt_const
  have hcorder : ∀ z ∈ (univ : Set ℂ), meromorphicOrderAt (fun _ : ℂ => c) z ≠ ⊤ := by
    intro z hz
    rw [(hcA z hz).meromorphicOrderAt_eq, (hcA z hz).analyticOrderAt_eq_zero.mpr hc]
    simp
  rw [ValueDistribution.logCounting_zero, ValueDistribution.logCounting_zero,
    divisor_fun_mul hcA.meromorphicOn hA.meromorphicOn hcorder
      (fun z _ => entire_meromorphicOrder_ne_top hF hF0 z), divisor_const, zero_add]

theorem logCounting_wronskian_dilate {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) {t R : ℝ} (ht : 0 < t) (hR : 0 < R) :
    ValueDistribution.logCounting (FewInflection.wronskian n (f.dilate (t : ℂ)).coord)
      (0 : WithTop ℂ) R =
      ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
        (0 : WithTop ℂ) (t * R) -
          (divisor (FewInflection.wronskian n f.coord) univ 0 : ℝ) * Real.log t := by
  have hW := FewInflection.differentiable_wronskian f
  have hW0 := curve_wronskian_nontrivial f hlin
  have hd : Differentiable ℂ (fun z => FewInflection.wronskian n f.coord ((t : ℂ) * z)) :=
    hW.comp (by fun_prop)
  have hd0 : ∃ z, FewInflection.wronskian n f.coord ((t : ℂ) * z) ≠ 0 := by
    obtain ⟨a, ha⟩ := hW0
    refine ⟨a / (t : ℂ), ?_⟩
    simpa only [mul_div_cancel₀ a (Complex.ofReal_ne_zero.mpr ht.ne')] using ha
  have heq : FewInflection.wronskian n (f.dilate (t : ℂ)).coord =
      (fun z => (t : ℂ) ^ (∑ i : Index n, i.val) *
        FewInflection.wronskian n f.coord ((t : ℂ) * z)) :=
    funext (FewInflection.wronskian_dilate f (t : ℂ))
  rw [heq, logCounting_const_mul hd hd0 (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne'))]
  exact logCounting_real_dilate hW hW0 ht hR

theorem logCounting_wronskian_dilate_le {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) {t R : ℝ} (ht : 1 ≤ t) (hR : 0 < R) :
    ValueDistribution.logCounting (FewInflection.wronskian n (f.dilate (t : ℂ)).coord)
      (0 : WithTop ℂ) R ≤
      ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
        (0 : WithTop ℂ) (t * R) := by
  rw [logCounting_wronskian_dilate f hlin (zero_lt_one.trans_le ht) hR]
  apply sub_le_self
  apply mul_nonneg _ (Real.log_nonneg ht)
  exact Int.cast_nonneg
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (FewInflection.differentiable_wronskian f)).divisor_nonneg 0)

theorem log_trailingCoeff_const_mul {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∃ z, F z ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    Real.log ‖meromorphicTrailingCoeffAt (fun z => c * F z) 0‖ =
      Real.log ‖c‖ + Real.log ‖meromorphicTrailingCoeffAt F 0‖ := by
  have hf0 := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF 0 (mem_univ _)).meromorphicAt
  have htrail := hf0.meromorphicTrailingCoeffAt_ne_zero (entire_meromorphicOrder_ne_top hF hF0 0)
  have hc0 : MeromorphicAt (fun _ : ℂ => c) 0 := by fun_prop
  rw [hc0.meromorphicTrailingCoeffAt_fun_mul hf0, meromorphicTrailingCoeffAt_const,
    norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr htrail)]

theorem log_trailingCoeff_wronskian_dilate {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) {t : ℝ} (ht : 0 < t) :
    Real.log ‖meromorphicTrailingCoeffAt
      (FewInflection.wronskian n (f.dilate (t : ℂ)).coord) 0‖ =
      ((∑ i : Index n, i.val : ℕ) +
        (divisor (FewInflection.wronskian n f.coord) univ 0 : ℝ)) * Real.log t +
          Real.log ‖meromorphicTrailingCoeffAt (FewInflection.wronskian n f.coord) 0‖ := by
  have hW := FewInflection.differentiable_wronskian f
  have hW0 := curve_wronskian_nontrivial f hlin
  have hd : Differentiable ℂ (fun z => FewInflection.wronskian n f.coord ((t : ℂ) * z)) :=
    hW.comp (by fun_prop)
  have hd0 : ∃ z, FewInflection.wronskian n f.coord ((t : ℂ) * z) ≠ 0 := by
    obtain ⟨a, ha⟩ := hW0
    refine ⟨a / (t : ℂ), ?_⟩
    simpa only [mul_div_cancel₀ a (Complex.ofReal_ne_zero.mpr ht.ne')] using ha
  have heq : FewInflection.wronskian n (f.dilate (t : ℂ)).coord =
      (fun z => (t : ℂ) ^ (∑ i : Index n, i.val) *
        FewInflection.wronskian n f.coord ((t : ℂ) * z)) :=
    funext (FewInflection.wronskian_dilate f (t : ℂ))
  rw [heq, log_trailingCoeff_const_mul hd hd0
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne')),
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Real.log_pow,
    log_trailingCoeff_dilate hW hW0 ht]
  ring

end
end ModifiedCartan
#print axioms ModifiedCartan.logCounting_wronskian_dilate
#print axioms ModifiedCartan.log_trailingCoeff_wronskian_dilate
