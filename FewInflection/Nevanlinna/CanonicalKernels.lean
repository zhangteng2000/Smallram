import FewInflection.Nevanlinna.PoissonLogDerivative
import FewInflection.Nevanlinna.PoissonKernelBounds

/-!
# The explicit kernels in the differentiated canonical decomposition

Mathlib's canonical factor is the reciprocal of the usual disk Blaschke
factor.  Its logarithmic derivative is therefore the negative of the sum of
the ordinary pole kernel and its reflected kernel.
-/

open scoped BigOperators ComplexConjugate Topology
open Complex Filter Function MeromorphicOn Metric Set

namespace FewInflection

noncomputable section

theorem logDeriv_canonicalFactor
    {R : ℝ} {a z : ℂ} (hR : R ≠ 0) (hza : z ≠ a)
    (hden : (R : ℂ) ^ 2 - conj a * z ≠ 0) :
    logDeriv (canonicalFactor R a) z =
      -((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z)) := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  have hnumder : HasDerivAt
      (fun w : ℂ => (R : ℂ) ^ 2 - conj a * w) (-conj a) z := by
    simpa using ((hasDerivAt_id z).const_mul (conj a)).const_sub ((R : ℂ) ^ 2)
  have hsubder : HasDerivAt (fun w : ℂ => w - a) 1 z :=
    (hasDerivAt_id z).sub_const a
  have hdenom : (R : ℂ) * (z - a) ≠ 0 :=
    mul_ne_zero hRc (sub_ne_zero.mpr hza)
  have hdenDer : HasDerivAt
      (fun w : ℂ => (R : ℂ) * (w - a)) (R : ℂ) z := by
    simpa [mul_comm] using hsubder.const_mul (R : ℂ)
  rw [canonicalFactor_def,
    logDeriv_div z hden hdenom
      hnumder.differentiableAt hdenDer.differentiableAt,
    logDeriv_const_mul z (R : ℂ) hRc]
  simp only [logDeriv_apply, hnumder.deriv, hsubder.deriv]
  simp only [neg_div, one_div]
  ring

theorem logDeriv_canonicalFactor_of_mem_ball
    {R : ℝ} {a z : ℂ} (ha : a ∈ ball 0 R)
    (hz : z ∈ closedBall 0 R) (hza : z ≠ a) :
    logDeriv (canonicalFactor R a) z =
      -((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z)) := by
  have hfactor := canonicalFactor_ne_zero ha hz hza
  rw [canonicalFactor_apply] at hfactor
  exact logDeriv_canonicalFactor (pos_of_mem_ball ha).ne' hza
    (div_ne_zero_iff.mp hfactor).1

theorem canonicalDecomp_logDeriv_kernels_eventuallyEq
    {f g : ℂ → ℂ} {R : ℝ}
    (D : CanonicalDecomp f g R) (hR : 0 < R) :
    logDeriv f =ᶠ[codiscreteWithin (ball 0 R)]
      (fun z =>
        (∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) +
          logDeriv g z) := by
  have hfinite := D.meromorphicOn.divisor_ball_support_finite
  have hexcluded : ∀ᶠ z in codiscreteWithin (ball (0 : ℂ) R),
      z ∉ support (divisor f (ball 0 R)) :=
    compl_finite_mem_codiscreteWithin hfinite
  filter_upwards [canonicalDecomp_logDeriv_eventuallyEq D hR,
    self_mem_codiscreteWithin (ball (0 : ℂ) R), hexcluded] with z heq hz houtside
  rw [heq]
  congr 1
  apply finsum_congr
  intro a
  by_cases ha0 : divisor f (ball 0 R) a = 0
  · simp [ha0]
  · have ha : a ∈ ball (0 : ℂ) R := by
      by_contra ha
      exact ha0 (locallyFinsuppWithin.apply_eq_zero_of_notMem _ ha)
    have hza : z ≠ a := by
      intro heqza
      subst z
      exact houtside ha0
    rw [logDeriv_canonicalFactor_of_mem_ball ha (ball_subset_closedBall hz) hza]
    simp only [zsmul_eq_mul, Int.cast_neg, neg_mul_neg]

end

/-! A finite-radius estimate for the differentiated canonical kernels.  The
ordinary pole part is controlled by the explicit separation parameter, while
the reflected part is controlled uniformly on the unit disk. -/
theorem norm_iteratedDeriv_canonical_kernel_sum_le
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ν : ι → ℤ) (m : ℕ)
    {R δ : ℝ} {z : ℂ}
    (hR : 2 < R) (ha : ∀ i ∈ s, ‖a i‖ < R) (hz : ‖z‖ ≤ 1)
    (hδ : 0 < δ) (hsep : ∀ i ∈ s, δ ≤ ‖z - a i‖) :
    ‖iteratedDeriv m
      (fun w : ℂ => ∑ i ∈ s, (ν i : ℂ) *
        ((w - a i)⁻¹ + conj (a i) /
          ((R : ℂ) ^ 2 - conj (a i) * w))) z‖ ≤
      (Nat.factorial m : ℝ) * (δ⁻¹ ^ (m + 1) + 1) *
        ∑ i ∈ s, |(ν i : ℝ)| := by
  let fs : ℂ → ℂ := fun w => ∑ i ∈ s, (ν i : ℂ) * (w - a i)⁻¹
  let fr : ℂ → ℂ := fun w => ∑ i ∈ s, (ν i : ℂ) *
      (conj (a i) / ((R : ℂ) ^ 2 - conj (a i) * w))
  have hscont : ContDiffAt ℂ m fs z := by
    dsimp [fs]
    apply ContDiffAt.sum
    intro i hi
    have hne : a i ≠ z := by
      intro h
      subst z
      have hnorm : ‖a i - a i‖ = 0 := by simp
      linarith [hsep i hi]
    have hlin : ContDiffAt ℂ m (fun w : ℂ => w - a i) z :=
      contDiffAt_id.sub contDiffAt_const
    have hinv : ContDiffAt ℂ m (fun w : ℂ => (w - a i)⁻¹) z :=
      hlin.fun_inv (sub_ne_zero.mpr hne.symm)
    simpa only [smul_eq_mul] using (contDiffAt_const.mul hinv)
  have hrcont : ContDiffAt ℂ m fr z := by
    dsimp [fr]
    apply ContDiffAt.sum
    intro i hi
    have hden : (R : ℂ) ^ 2 - conj (a i) * z ≠ 0 :=
      reflected_denominator_ne_zero (by linarith) (ha i hi) hz
    have hmul : ContDiffAt ℂ m (fun w : ℂ => conj (a i) * w) z :=
      contDiffAt_const.mul contDiffAt_id
    have hlin : ContDiffAt ℂ m
        (fun w : ℂ => (R : ℂ) ^ 2 - conj (a i) * w) z := by
      simpa only [id_eq] using contDiffAt_const.sub hmul
    have hfrac : ContDiffAt ℂ m
        (fun w : ℂ => conj (a i) /
          ((R : ℂ) ^ 2 - conj (a i) * w)) z :=
      contDiffAt_const.div hlin hden
    simpa only [smul_eq_mul] using (contDiffAt_const.mul hfrac)
  have hderiv : iteratedDeriv m (fun w : ℂ => fs w + fr w) z =
      iteratedDeriv m fs z + iteratedDeriv m fr z := by
    have hadd : (fun w : ℂ => fs w + fr w) = fs + fr := by
      funext w
      rfl
    rw [hadd]
    exact iteratedDeriv_add hscont hrcont
  have hsing := norm_iteratedDeriv_singular_sum_le s a
      (fun i => (ν i : ℂ)) m hδ hsep
  have href := norm_iteratedDeriv_reflected_sum_le s a ν m hR ha hz
  have hfun : (fun w : ℂ => ∑ i ∈ s, (ν i : ℂ) *
        ((w - a i)⁻¹ + conj (a i) /
          ((R : ℂ) ^ 2 - conj (a i) * w))) =
      (fun w : ℂ => fs w + fr w) := by
    funext w
    simp [fs, fr, Finset.sum_add_distrib, mul_add]
  rw [hfun, hderiv]
  calc
    ‖iteratedDeriv m fs z + iteratedDeriv m fr z‖ ≤
        ‖iteratedDeriv m fs z‖ + ‖iteratedDeriv m fr z‖ := norm_add_le _ _
    _ ≤ (Nat.factorial m : ℝ) * δ⁻¹ ^ (m + 1) *
          ∑ i ∈ s, ‖(ν i : ℂ)‖ +
        (Nat.factorial m : ℝ) * ∑ i ∈ s, |(ν i : ℝ)| :=
      add_le_add hsing href
    _ = (Nat.factorial m : ℝ) * (δ⁻¹ ^ (m + 1) + 1) *
          ∑ i ∈ s, |(ν i : ℝ)| := by
      simp only [Complex.norm_intCast]
      ring

end FewInflection
