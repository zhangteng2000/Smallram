import ModifiedCartan.DivisorPolynomial
import ModifiedCartan.WronskianNontrivial
import ModifiedCartan.CanonicalDilation
import FewInflection.Dilation
import FewInflection.WronskianRegularity
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

open scoped Topology BigOperators Classical
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The representation in LaTeX `eq:localgauge`. -/
def rescaledRepresentation {n : ℕ} (f : Curve n) (t : ℝ) (H : ℂ → ℂ) :
    Index n → ℂ → ℂ := fun j z => Complex.exp (-H z) * f.coord j ((t : ℂ) * z)

theorem rescaledRepresentation_analyticAt {n : ℕ} (f : Curve n) (t : ℝ)
    {H : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z) (j : Index n) :
    AnalyticAt ℂ (rescaledRepresentation f t H j) z := by
  exact hH.neg.cexp.fun_mul
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
      _ (mem_univ _)).fun_comp (analyticAt_const.fun_mul analyticAt_id))

theorem rescaledRepresentation_reduced {n : ℕ} (f : Curve n) (t : ℝ)
    (H : ℂ → ℂ) (z : ℂ) : ∃ j, rescaledRepresentation f t H j z ≠ 0 := by
  obtain ⟨j, hj⟩ := f.reduced ((t : ℂ) * z)
  exact ⟨j, mul_ne_zero (Complex.exp_ne_zero _) hj⟩

theorem euclideanNorm_mul_scalar {n : ℕ} (c : ℂ) (v : Index n → ℂ) :
    euclideanNorm (fun j => c * v j) = ‖c‖ * euclideanNorm v := by
  unfold euclideanNorm
  simp_rw [norm_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq (norm_nonneg c)]

theorem rescaledRepresentation_log_norm {n : ℕ} (f : Curve n) (t : ℝ)
    (H : ℂ → ℂ) (z : ℂ) :
    Real.log (euclideanNorm (fun j => rescaledRepresentation f t H j z)) =
      Real.log (euclideanNorm (f.vector ((t : ℂ) * z))) - (H z).re := by
  change Real.log (euclideanNorm (fun j => Complex.exp (-H z) *
    f.vector ((t : ℂ) * z) j)) = _
  rw [euclideanNorm_mul_scalar, Real.log_mul
    (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _))
    (euclideanNorm_pos (f.vector_ne_zero _)).ne', Complex.norm_exp, Real.log_exp,
    Complex.neg_re]
  ring

theorem rescaledRepresentation_log_center {n : ℕ} (f : Curve n) (t : ℝ)
    (H : ℂ → ℂ) (j : Index n) (hj : f.coord j 0 ≠ 0) :
    Real.log ‖rescaledRepresentation f t H j 0‖ = Real.log ‖f.coord j 0‖ - (H 0).re := by
  simp only [rescaledRepresentation, mul_zero, norm_mul]
  rw [Real.log_mul (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _))
    (norm_ne_zero_iff.mpr hj), Complex.norm_exp, Real.log_exp, Complex.neg_re]
  ring

theorem rescaledRepresentation_wronskian {n : ℕ} (f : Curve n) (t : ℝ)
    {H : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z) :
    FewInflection.wronskian n (rescaledRepresentation f t H) z =
      Complex.exp (-H z) ^ (n + 1) *
        FewInflection.wronskian n (f.dilate (t : ℂ)).coord z := by
  apply FewInflection.wronskian_scalar_mul (fun z => Complex.exp (-H z))
    (f.dilate (t : ℂ)).coord z hH.neg.cexp.contDiffAt
  intro j
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr
    ((f.dilate (t : ℂ)).holomorphic j) z (mem_univ _)).contDiffAt

/-- LaTeX `eq:localgauge`, constructed from the actual Wronskian divisor.
The product identity is stated also at its zeros, where a raw quotient
would use totalized division and would not express removable singularities. -/
theorem Paper.eq_localgauge {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) {t : ℝ} (ht : 0 < t) :
    ∃ (H : ℂ → ℂ) (P : Polynomial ℂ),
      AnalyticOnNhd ℂ H (ball 0 64) ∧ P.Monic ∧
      (∀ z, P.eval z = 0 → z ∈ ball (0 : ℂ) 64) ∧
      (∀ z ∈ ball (0 : ℂ) 64,
        (t : ℂ) ^ (∑ i : Index n, i.val) *
          FewInflection.wronskian n f.coord ((t : ℂ) * z) =
            P.eval z * Complex.exp ((n + 1 : ℂ) * H z)) ∧
      (∀ z ∈ ball (0 : ℂ) 64,
        FewInflection.wronskian n (rescaledRepresentation f t H) z = P.eval z) := by
  let F := f.dilate (t : ℂ)
  have hlinF := f.dilate_linearlyNonDegenerate (t : ℂ)
    (Complex.ofReal_ne_zero.mpr ht.ne') hlin
  obtain ⟨P, L, hP, hL, hroots, hfactor, _⟩ :=
    exists_monic_polynomial_exp_factor_on_ball (FewInflection.differentiable_wronskian F)
      (curve_wronskian_nontrivial F hlinF) (R := 64) (by norm_num)
  let H : ℂ → ℂ := fun z => L z / (n + 1 : ℂ)
  have hN : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hHL (z : ℂ) : (n + 1 : ℂ) * H z = L z := mul_div_cancel₀ _ hN
  have hH : AnalyticOnNhd ℂ H (ball 0 64) := fun z hz => (hL z hz).div_const
  refine ⟨H, P, hH, hP, hroots, ?_, ?_⟩
  · intro z hz
    rw [hHL]
    exact (FewInflection.wronskian_dilate f (t : ℂ) z).symm.trans (hfactor z hz)
  · intro z hz
    rw [rescaledRepresentation_wronskian f t (hH z hz), hfactor z hz,
      ← Complex.exp_nat_mul]
    push_cast
    rw [mul_neg, hHL, Complex.exp_neg]
    calc
      _ = P.eval z * ((Complex.exp (L z))⁻¹ * Complex.exp (L z)) := by ring
      _ = P.eval z := by rw [inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one]

/-- LaTeX `eq:canonical-coefficient-identification`. Scalar gauge invariance
and dilation identify the actual coefficients, including their totalized
values at Wronskian zeros. -/
theorem Paper.eq_canonical_coefficient_identification {n : ℕ} (f : Curve n)
    {t : ℝ} (ht : 0 < t) {H : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z)
    (i : Index n) :
    canonicalCoefficient n (rescaledRepresentation f t H) i z =
      (t : ℂ) ^ (n + 1 - i.val) * canonicalCoefficient n f.coord i ((t : ℂ) * z) := by
  have hg : ∀ j, AnalyticAt ℂ (fun w => f.coord j ((t : ℂ) * w)) z := fun j =>
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic j)
      _ (mem_univ _)).fun_comp (analyticAt_const.fun_mul analyticAt_id)
  have hη : AnalyticAt ℂ (fun w => Complex.exp (-H w)) z := hH.neg.cexp
  exact (canonicalCoefficient_scalar_mul hg hη (Complex.exp_ne_zero _) i).trans
    (Paper.eq_scalecoeff
      (fun j => Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (f.holomorphic j) _ (mem_univ _)) ht i)

theorem circleAverage_real_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℂ → E) (t R : ℝ) :
    Real.circleAverage (fun z => u ((t : ℂ) * z)) 0 R = Real.circleAverage u 0 (t * R) := by
  have he (θ : ℝ) : (t : ℂ) * circleMap 0 R θ = circleMap 0 (t * R) θ := by
    simp only [circleMap, zero_add, Complex.ofReal_mul]
    ring
  simp only [Real.circleAverage, he]

/-- LaTeX `eq:meanidentity`, with its constant explicitly identified.
The asymptotic smallness of this constant is a separate conclusion from
the center estimate; this exact identity needs only the analytic gauge. -/
theorem Paper.eq_meanidentity {n : ℕ} (f : Curve n) (t : ℝ)
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H (ball 0 64))
    {R : ℝ} (hR : 0 < R) (hR64 : R < 64) :
    Real.circleAverage (fun z => Real.log (euclideanNorm
      (fun j => rescaledRepresentation f t H j z))) 0 R =
        characteristic f (R * t) + Real.log (euclideanNorm (f.vector 0)) - (H 0).re := by
  have hh : InnerProductSpace.HarmonicOnNhd (fun z => (H z).re) (closedBall 0 |R|) := by
    intro z hz
    rw [abs_of_pos hR] at hz
    exact (hH z (closedBall_subset_ball hR64 hz)).harmonicAt_re
  have hleft : CircleIntegrable
      (fun z => Real.log (euclideanNorm (f.vector ((t : ℂ) * z)))) 0 R := by
    apply ContinuousOn.circleIntegrable'
    exact ((curve_log_euclideanNorm_continuous f).comp (by fun_prop)).continuousOn
  have hright : CircleIntegrable (fun z => (H z).re) 0 R :=
    (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  simp_rw [rescaledRepresentation_log_norm]
  rw [Real.circleAverage_fun_sub hleft hright, hh.circleAverage_eq,
    circleAverage_real_dilate (fun z => Real.log (euclideanNorm (f.vector z))) t R]
  unfold characteristic
  rw [mul_comm t R]
  ring

end
end ModifiedCartan
#print axioms ModifiedCartan.Paper.eq_localgauge
#print axioms ModifiedCartan.Paper.eq_canonical_coefficient_identification
#print axioms ModifiedCartan.Paper.eq_meanidentity
