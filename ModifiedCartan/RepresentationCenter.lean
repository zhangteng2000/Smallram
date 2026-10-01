import ModifiedCartan.CountingDilation

open scoped Topology BigOperators Classical
open Filter Set Metric MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The actual monic Wronskian zero polynomial on D64 after dilation.
LaTeX: the polynomial P in Step 1 of `prop:representation`. -/
def rescaledWronskianPolynomial {n : ℕ} (f : Curve n) (t : ℝ) : Polynomial ℂ :=
  finiteDivisorPolynomial
    (divisor (FewInflection.wronskian n (f.dilate (t : ℂ)).coord) (ball 0 64))
    (((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (FewInflection.differentiable_wronskian (f.dilate (t : ℂ)))).meromorphicOn.mono_set
        (subset_univ (closedBall (0 : ℂ) 64))).divisor_ball_support_finite)

theorem rescaledWronskianPolynomial_monic {n : ℕ} (f : Curve n) (t : ℝ) :
    (rescaledWronskianPolynomial f t).Monic := finiteDivisorPolynomial_monic _ _

theorem rescaledWronskianPolynomial_roots_mem {n : ℕ} (f : Curve n) (t : ℝ)
    {z : ℂ} (hz : (rescaledWronskianPolynomial f t).eval z = 0) :
    z ∈ ball (0 : ℂ) 64 := finiteDivisorPolynomial_roots_mem _ _ hz

theorem rescaledWronskianPolynomial_degree_bound {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) {t : ℝ} (ht : 1 ≤ t) :
    ((rescaledWronskianPolynomial f t).natDegree : ℝ) * Real.log 2 ≤
      ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
        (0 : WithTop ℂ) (256 * t) := by
  have hd := finiteDivisorPolynomial_degree_count_bound
    (FewInflection.differentiable_wronskian (f.dilate (t : ℂ))) (R := 64) (by norm_num)
    (((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (FewInflection.differentiable_wronskian (f.dilate (t : ℂ)))).meromorphicOn.mono_set
        (subset_univ (closedBall (0 : ℂ) 64))).divisor_ball_support_finite)
  change ((rescaledWronskianPolynomial f t).natDegree : ℝ) * Real.log 2 ≤ _ at hd
  rw [show (2 : ℝ) * 64 = 128 by norm_num] at hd
  have hscale := logCounting_wronskian_dilate_le f hlin ht (R := 128) (by norm_num)
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hmono : ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
      (0 : WithTop ℂ) (t * 128) ≤
      ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
        (0 : WithTop ℂ) (256 * t) :=
    ValueDistribution.logCounting_monotoneOn
      (show 0 < t * 128 by positivity) (show 0 < 256 * t by positivity) (by linarith)
  exact hd.trans (hscale.trans hmono)

/-- LaTeX `eq:centeridentity` together with the actual local gauge.
The polynomial is fixed by the Wronskian divisor rather than chosen later
to satisfy estimates. Zeros at the origin are fully included. -/
theorem Paper.eq_centeridentity {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) {t : ℝ} (ht : 0 < t) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 64) ∧
      (∀ z ∈ ball (0 : ℂ) 64,
        (t : ℂ) ^ (∑ i : Index n, i.val) * FewInflection.wronskian n f.coord ((t : ℂ) * z) =
          (rescaledWronskianPolynomial f t).eval z * Complex.exp ((n + 1 : ℂ) * H z)) ∧
      (∀ z ∈ ball (0 : ℂ) 64,
        FewInflection.wronskian n (rescaledRepresentation f t H) z =
          (rescaledWronskianPolynomial f t).eval z) ∧
      (n + 1 : ℝ) * (H 0).re =
        (∑ i : Index n, i.val : ℕ) * Real.log t +
          ValueDistribution.logCounting (FewInflection.wronskian n f.coord)
            (0 : WithTop ℂ) (64 * t) -
              ((rescaledWronskianPolynomial f t).natDegree : ℝ) * Real.log 64 +
                Real.log ‖meromorphicTrailingCoeffAt (FewInflection.wronskian n f.coord) 0‖ := by
  let F := f.dilate (t : ℂ)
  have hA := Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (FewInflection.differentiable_wronskian F)
  have hF0 := curve_wronskian_nontrivial F
    (f.dilate_linearlyNonDegenerate (t : ℂ) (Complex.ofReal_ne_zero.mpr ht.ne') hlin)
  have hfinite := (hA.meromorphicOn.mono_set
    (subset_univ (closedBall (0 : ℂ) 64))).divisor_ball_support_finite
  obtain ⟨v, hv, hv0, heq⟩ := exists_monic_polynomial_nonzero_factor isOpen_ball
    (hA.mono (subset_univ (ball (0 : ℂ) 64)))
    (fun z => entire_meromorphicOrder_ne_top (FewInflection.differentiable_wronskian F) hF0 z)
    hfinite
  let : ContractibleSpace (ball (0 : ℂ) 64) :=
    (convex_ball (0 : ℂ) 64).contractibleSpace ⟨0, mem_ball_self (by norm_num)⟩
  obtain ⟨L, hL, heL⟩ := FewInflection.exists_analyticOnNhd_log
    (SimplyConnectedSpace.ofContractible _) isOpen_ball hv hv0
  have hfactor : ∀ z ∈ ball (0 : ℂ) 64,
      FewInflection.wronskian n F.coord z =
        (rescaledWronskianPolynomial f t).eval z * Complex.exp (L z) := by
    intro z hz
    rw [heL z hz]
    exact heq z hz
  let H : ℂ → ℂ := fun z => L z / (n + 1 : ℂ)
  have hN : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hHL (z : ℂ) : (n + 1 : ℂ) * H z = L z := mul_div_cancel₀ _ hN
  have hH : AnalyticOnNhd ℂ H (ball 0 64) := fun z hz => (hL z hz).div_const
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · intro z hz
    rw [hHL]
    exact (FewInflection.wronskian_dilate f (t : ℂ) z).symm.trans (hfactor z hz)
  · intro z hz
    rw [rescaledRepresentation_wronskian f t (hH z hz), hfactor z hz,
      ← Complex.exp_nat_mul]
    push_cast
    rw [mul_neg, hHL, Complex.exp_neg]
    calc
      _ = (rescaledWronskianPolynomial f t).eval z *
          ((Complex.exp (L z))⁻¹ * Complex.exp (L z)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one]
  · have hcenter := exponential_factor_center_identity
      (FewInflection.differentiable_wronskian F) (R := 64) (by norm_num) hfinite hL hfactor
    have hreal : (n + 1 : ℝ) * (H 0).re = (L 0).re := by
      simpa [Complex.mul_re] using congrArg Complex.re (hHL 0)
    rw [hreal, hcenter]
    change ValueDistribution.logCounting
        (FewInflection.wronskian n (f.dilate (t : ℂ)).coord) (0 : WithTop ℂ) 64 -
      ((rescaledWronskianPolynomial f t).natDegree : ℝ) * Real.log 64 +
      Real.log ‖meromorphicTrailingCoeffAt (FewInflection.wronskian n (f.dilate (t : ℂ)).coord) 0‖ = _
    rw [logCounting_wronskian_dilate f hlin ht (by norm_num),
      log_trailingCoeff_wronskian_dilate f hlin ht]
    rw [mul_comm t 64]
    ring

end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_centeridentity
