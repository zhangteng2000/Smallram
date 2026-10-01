import FewInflection.Nevanlinna.PoissonBoundaryBounds
import FewInflection.Nevanlinna.BoundaryMeanBounds

/-!
# A finite-support fixed-radius logarithmic-derivative bound

This module combines the proved differentiated Poisson--Jensen formula with
the finite canonical-kernel estimate and the boundary Poisson estimate.  The
support, separation, and boundary hypotheses are all explicit: this is a
fixed-radius statement and does not hide the later global compactness step.
-/

open scoped BigOperators ComplexConjugate Topology
open Complex Filter Function MeromorphicOn Metric Real Set

namespace FewInflection

theorem norm_logDeriv_le_of_poisson_jensen_formula
    {f : ℂ → ℂ} {R δ : ℝ} {z : ℂ} (s : Finset ℂ)
    (hR2 : 2 < R) (hR3 : R < 3) (hz : ‖z‖ ≤ 1)
    (hfSphere : MeromorphicOn f (sphere 0 R))
    (hδ : 0 < δ)
    (hsupport : Function.support (divisor f (ball 0 R)) ⊆ (s : Set ℂ))
    (hinside : ∀ a ∈ s, ‖a‖ < R)
    (hsep : ∀ a ∈ s, δ ≤ ‖z - a‖)
    (hformula : logDeriv f z =
      (∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
        ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) +
      Real.circleAverage (fun ζ : ℂ =>
        (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R) :
    ‖logDeriv f z‖ ≤
      (δ⁻¹ + 1) * ∑ a ∈ s, |(divisor f (ball 0 R) a : ℝ)| +
        6 * Real.circleAverage (fun ζ : ℂ => |Real.log ‖f ζ‖|) 0 R := by
  have hsupportKernel :
      Function.support (fun a : ℂ =>
        (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) ⊆
        (s : Set ℂ) := by
    intro a ha
    by_contra haS
    have hzero : divisor f (ball 0 R) a = 0 := by
      apply notMem_support.mp
      intro haDiv
      exact haS (hsupport haDiv)
    exact ha (by simp [hzero])
  rw [hformula, finsum_eq_sum_of_support_subset _ hsupportKernel]
  have hsing := norm_iteratedDeriv_canonical_kernel_sum_le
    s (fun a : ℂ => a) (fun a : ℂ => divisor f (ball 0 R) a) 0
      hR2 hinside hz hδ hsep
  have hsing' :
      ‖∑ a ∈ s, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))‖ ≤
        (δ⁻¹ + 1) * ∑ a ∈ s, |(divisor f (ball 0 R) a : ℝ)| := by
    simpa using hsing
  have hboundary := norm_circleAverage_poisson_first_derivative_le
    hR2 hR3 hz hfSphere
  calc
    ‖(∑ a ∈ s, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) +
        Real.circleAverage (fun ζ : ℂ =>
          (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R‖ ≤
        ‖∑ a ∈ s, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))‖ +
        ‖Real.circleAverage (fun ζ : ℂ =>
          (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R‖ :=
      norm_add_le _ _
    _ ≤ (δ⁻¹ + 1) * ∑ a ∈ s, |(divisor f (ball 0 R) a : ℝ)| +
        6 * Real.circleAverage (fun ζ : ℂ => |Real.log ‖f ζ‖|) 0 R :=
      add_le_add hsing' hboundary

theorem norm_logDeriv_le_of_poisson_jensen_formula_characteristic
    {f : ℂ → ℂ} {R δ : ℝ} {z : ℂ} (s : Finset ℂ)
    (hR2 : 2 < R) (hR3 : R < 3) (hz : ‖z‖ ≤ 1)
    (hfSphere : MeromorphicOn f (sphere 0 R))
    (hf : Meromorphic f) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hδ : 0 < δ)
    (hsupport : Function.support (divisor f (ball 0 R)) ⊆ (s : Set ℂ))
    (hinside : ∀ a ∈ s, ‖a‖ < R)
    (hsep : ∀ a ∈ s, δ ≤ ‖z - a‖)
    (hformula : logDeriv f z =
      (∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
        ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) +
      Real.circleAverage (fun ζ : ℂ =>
        (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R) :
    ‖logDeriv f z‖ ≤
      (δ⁻¹ + 1) * ∑ a ∈ s, |(divisor f (ball 0 R) a : ℝ)| +
        12 * ValueDistribution.characteristic f ⊤ R +
        6 * |Real.log ‖f 0‖| := by
  have hlocal := norm_logDeriv_le_of_poisson_jensen_formula s hR2 hR3 hz
    hfSphere hδ hsupport hinside hsep hformula
  have hmean := circleAverage_abs_log_norm_le_two_characteristic_add_center
    hf hfa h0 (r := R) (by linarith)
  have hmul :
      6 * Real.circleAverage (fun ζ : ℂ => |Real.log ‖f ζ‖|) 0 R ≤
        6 * (2 * ValueDistribution.characteristic f ⊤ R +
          |Real.log ‖f 0‖|) := by
    exact mul_le_mul_of_nonneg_left hmean (by norm_num)
  linarith

end FewInflection
