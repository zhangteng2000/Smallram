import ModifiedCartan.RepresentationCenter

open scoped Topology BigOperators Classical
open Filter Set Metric MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem representation_inner_count_small {n : ℕ} (f : Curve n)
    {t s : ℕ → ℝ} (ht : Tendsto t atTop atTop) (hs : Tendsto s atTop atTop)
    (hN : Tendsto (fun ν => ValueDistribution.logCounting
      (FewInflection.wronskian n f.coord) (0 : WithTop ℂ) (256 * t ν) / s ν) atTop (𝓝 0)) :
    Tendsto (fun ν => ValueDistribution.logCounting
      (FewInflection.wronskian n f.coord) (0 : WithTop ℂ) (64 * t ν) / s ν) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ hN
  · filter_upwards [ht.eventually_ge_atTop 1, hs.eventually_gt_atTop 0] with ν htν hsν
    exact div_nonneg (ValueDistribution.logCounting_nonneg (by linarith : 1 ≤ 64 * t ν)) hsν.le
  · filter_upwards [ht.eventually_ge_atTop 1, hs.eventually_gt_atTop 0] with ν htν hsν
    apply div_le_div_of_nonneg_right _ hsν.le
    exact ValueDistribution.logCounting_monotoneOn
      (show 0 < 64 * t ν by linarith) (show 0 < 256 * t ν by linarith) (by linarith)

theorem rescaledWronskianPolynomial_degree_small {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) {t s : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) (hs : Tendsto s atTop atTop)
    (hN : Tendsto (fun ν => ValueDistribution.logCounting
      (FewInflection.wronskian n f.coord) (0 : WithTop ℂ) (256 * t ν) / s ν) atTop (𝓝 0)) :
    Tendsto (fun ν => ((rescaledWronskianPolynomial f (t ν)).natDegree : ℝ) / s ν) atTop (𝓝 0) := by
  have hlim := hN.div_const (Real.log 2)
  simp only [zero_div] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hs.eventually_gt_atTop 0] with ν hsν
    positivity
  · filter_upwards [ht.eventually_ge_atTop 1, hs.eventually_gt_atTop 0] with ν htν hsν
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    calc
      _ = (((rescaledWronskianPolynomial f (t ν)).natDegree : ℝ) * Real.log 2) / s ν := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (rescaledWronskianPolynomial_degree_bound f hlin htν) hsν.le

theorem representation_center_small {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) {t s : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) (hs : Tendsto s atTop atTop)
    (hlog : Tendsto (fun ν => Real.log (t ν) / s ν) atTop (𝓝 0))
    (hN : Tendsto (fun ν => ValueDistribution.logCounting
      (FewInflection.wronskian n f.coord) (0 : WithTop ℂ) (256 * t ν) / s ν) atTop (𝓝 0))
    {H : ℕ → ℂ → ℂ}
    (hcenter : ∀ᶠ ν in atTop, (n + 1 : ℝ) * (H ν 0).re =
      (∑ i : Index n, i.val : ℕ) * Real.log (t ν) +
        ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
          (0 : WithTop ℂ) (64 * t ν) -
            ((rescaledWronskianPolynomial f (t ν)).natDegree : ℝ) * Real.log 64 +
              Real.log ‖meromorphicTrailingCoeffAt (FewInflection.wronskian n f.coord) 0‖) :
    Tendsto (fun ν => (H ν 0).re / s ν) atTop (𝓝 0) := by
  have hinner := representation_inner_count_small f ht hs hN
  have hdegree := rescaledWronskianPolynomial_degree_small f hlin ht hs hN
  have hconstant := (tendsto_inv_atTop_zero.comp hs).const_mul
    (Real.log ‖meromorphicTrailingCoeffAt (FewInflection.wronskian n f.coord) 0‖)
  have hlim := ((((hlog.const_mul ((∑ i : Index n, i.val : ℕ) : ℝ)).add hinner).sub
    (hdegree.mul_const (Real.log 64))).add hconstant).div_const (n + 1 : ℝ)
  simp only [mul_zero, zero_mul, add_zero, sub_zero, zero_div] at hlim
  apply hlim.congr'
  filter_upwards [hcenter] with ν hν
  have hN0 : (n + 1 : ℝ) ≠ 0 := by positivity
  change (((∑ i : Index n, i.val : ℕ) * (Real.log (t ν) / s ν) +
    ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
      (0 : WithTop ℂ) (64 * t ν) / s ν -
    ((rescaledWronskianPolynomial f (t ν)).natDegree : ℝ) / s ν * Real.log 64) +
    Real.log ‖meromorphicTrailingCoeffAt (FewInflection.wronskian n f.coord) 0‖ * (s ν)⁻¹) /
      (n + 1 : ℝ) = (H ν 0).re / s ν
  calc
    _ = (((∑ i : Index n, i.val : ℕ) * Real.log (t ν) +
      ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
        (0 : WithTop ℂ) (64 * t ν) -
      ((rescaledWronskianPolynomial f (t ν)).natDegree : ℝ) * Real.log 64 +
      Real.log ‖meromorphicTrailingCoeffAt (FewInflection.wronskian n f.coord) 0‖) /
        (n + 1 : ℝ)) / s ν := by ring
    _ = _ := by rw [← hν, mul_div_cancel_left₀ _ hN0]

/-- Step 1 of LaTeX `prop:representation`, including all asserted center
limits, the exact mean identity, and its small constant. The norm upper
bound and coefficient compactness are deliberately left for the full
proposition, which will derive them from the characteristic hypothesis. -/
theorem Paper.representation_step_one {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (hf0 : ∀ j, f.coord j 0 ≠ 0)
    {t s : ℕ → ℝ} (ht : Tendsto t atTop atTop) (hs : Tendsto s atTop atTop)
    (hlog : Tendsto (fun ν => Real.log (t ν) / s ν) atTop (𝓝 0))
    (hN : Tendsto (fun ν => ValueDistribution.logCounting
      (FewInflection.wronskian n f.coord) (0 : WithTop ℂ) (256 * t ν) / s ν) atTop (𝓝 0)) :
    ∃ (H : ℕ → ℂ → ℂ) (c : ℕ → ℝ),
      (∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H ν) (ball 0 64) ∧
        (∀ z ∈ ball (0 : ℂ) 64, FewInflection.wronskian n
          (rescaledRepresentation f (t ν) (H ν)) z = (rescaledWronskianPolynomial f (t ν)).eval z) ∧
        (∀ R : ℝ, 0 < R → R < 64 →
          Real.circleAverage (fun z => Real.log (euclideanNorm
            (fun j => rescaledRepresentation f (t ν) (H ν) j z))) 0 R =
              characteristic f (R * t ν) + c ν)) ∧
      Tendsto (fun ν => ((rescaledWronskianPolynomial f (t ν)).natDegree : ℝ) / s ν) atTop (𝓝 0) ∧
      Tendsto (fun ν => (H ν 0).re / s ν) atTop (𝓝 0) ∧
      (∀ j, Tendsto (fun ν => Real.log ‖rescaledRepresentation f (t ν) (H ν) j 0‖ / s ν)
        atTop (𝓝 0)) ∧ Tendsto (fun ν => c ν / s ν) atTop (𝓝 0) := by
  have hchoice (ν : ℕ) : ∃ H : ℂ → ℂ, 0 < t ν →
      AnalyticOnNhd ℂ H (ball 0 64) ∧
      (∀ z ∈ ball (0 : ℂ) 64, FewInflection.wronskian n (rescaledRepresentation f (t ν) H) z =
        (rescaledWronskianPolynomial f (t ν)).eval z) ∧
      (n + 1 : ℝ) * (H 0).re =
        (∑ i : Index n, i.val : ℕ) * Real.log (t ν) +
          ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
            (0 : WithTop ℂ) (64 * t ν) -
              ((rescaledWronskianPolynomial f (t ν)).natDegree : ℝ) * Real.log 64 +
                Real.log ‖meromorphicTrailingCoeffAt (FewInflection.wronskian n f.coord) 0‖ := by
    by_cases htν : 0 < t ν
    · obtain ⟨H, hHa, _, hW, hcenter⟩ := eq_centeridentity f hlin htν
      exact ⟨H, fun _ => ⟨hHa, hW, hcenter⟩⟩
    · exact ⟨fun _ => 0, fun hp => (htν hp).elim⟩
  choose H hH using hchoice
  let c := fun ν => Real.log (euclideanNorm (f.vector 0)) - (H ν 0).re
  have hcenter := representation_center_small f hlin ht hs hlog hN (H := H) (by
    filter_upwards [ht.eventually_gt_atTop 0] with ν htν
    exact (hH ν htν).2.2)
  refine ⟨H, c, ?_, rescaledWronskianPolynomial_degree_small f hlin ht hs hN, hcenter, ?_, ?_⟩
  · filter_upwards [ht.eventually_gt_atTop 0] with ν htν
    refine ⟨(hH ν htν).1, (hH ν htν).2.1, ?_⟩
    intro R hR hR64
    have hm := eq_meanidentity f (t ν) (hH ν htν).1 hR hR64
    dsimp [c]
    linarith
  · intro j
    have hlim := ((tendsto_inv_atTop_zero.comp hs).const_mul (Real.log ‖f.coord j 0‖)).sub hcenter
    simp only [mul_zero, sub_zero] at hlim
    convert! hlim using 1
    funext ν
    rw [rescaledRepresentation_log_center f (t ν) (H ν) j (hf0 j)]
    simp only [Function.comp_apply]
    ring
  · have hlim := ((tendsto_inv_atTop_zero.comp hs).const_mul
      (Real.log (euclideanNorm (f.vector 0)))).sub hcenter
    simp only [mul_zero, sub_zero] at hlim
    convert! hlim using 1
    funext ν
    dsimp [c]
    ring

end
end ModifiedCartan
#print axioms ModifiedCartan.rescaledWronskianPolynomial_degree_small
#print axioms ModifiedCartan.Paper.representation_step_one
