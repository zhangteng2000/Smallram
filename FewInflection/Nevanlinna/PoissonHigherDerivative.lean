import FewInflection.Nevanlinna.CharacteristicMassBound
import Mathlib.Analysis.Meromorphic.IsolatedZeros

/-!
# Differentiating the Poisson--Jensen logarithmic-derivative identity

The differentiated identity is first recorded at the level of meromorphic
functions.  Mathlib's codiscrete derivative theorem supplies the step from an
eventual equality to equality of derivatives; the boundary integral is
identified with the derivative of its Herglotz--Riesz transform.
-/

open scoped BigOperators ComplexConjugate Topology
open Complex Filter Function MeromorphicOn Metric Real Set
open ValueDistribution

namespace FewInflection

theorem deriv_logDeriv_poisson_jensen_eventuallyEq
    {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hfClosed : MeromorphicOn f (closedBall 0 R))
    (hf : Meromorphic f) (hfa : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hboundary : ∀ w ∈ sphere 0 R, AnalyticAt ℂ f w ∧ f w ≠ 0) :
    deriv (logDeriv f) =ᶠ[codiscreteWithin (ball 0 R)]
      deriv (fun z =>
        (∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) +
        Real.circleAverage (fun ζ : ℂ =>
          (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R) := by
  have hH : AnalyticOnNhd ℂ
      (fun z : ℂ => Real.circleAverage
        (fun ζ : ℂ => herglotzRieszKernel 0 z ζ *
          (Real.log ‖f ζ‖ : ℂ)) 0 R) (ball 0 R) := by
    exact analyticOnNhd_circleAverage_herglotzRieszKernel_smul
      (circleIntegrable_ofReal_log_norm hf R)
  let B : ℂ → ℂ := fun z => Real.circleAverage (fun ζ : ℂ =>
    (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R
  have hB : AnalyticOnNhd ℂ B (ball 0 R) := by
    apply (hH.deriv_of_isOpen isOpen_ball).congr isOpen_ball
    intro z hz
    dsimp [B]
    exact (hasDerivAt_circleAverage_herglotz_log_norm hf hz).deriv
  have hsum : MeromorphicOn (fun z : ℂ =>
      ∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
        ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z)))
      (ball 0 R) := by
    obtain ⟨s, hsupp, _, _⟩ :=
      exists_finset_divisor_support_within_ball hfClosed hR
    have hfinite : MeromorphicOn (fun z : ℂ =>
        ∑ a ∈ s, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z)))
        (ball 0 R) := by
      apply MeromorphicOn.fun_sum
      intro a
      intro z hz
      fun_prop
    have hEq : (fun z : ℂ =>
        ∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) =
        (fun z : ℂ =>
        ∑ a ∈ s, (divisor f (ball 0 R) a : ℂ) *
          ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) := by
      funext z
      apply finsum_eq_sum_of_support_subset
      intro a ha
      apply hsupp
      intro hzero
      apply ha
      simp [hzero]
    rw [hEq]
    exact hfinite
  have hK : MeromorphicOn (fun z =>
      (∑ᶠ a, (divisor f (ball 0 R) a : ℂ) *
        ((z - a)⁻¹ + conj a / ((R : ℂ) ^ 2 - conj a * z))) + B z)
      (ball 0 R) := by
    exact hsum.add hB.meromorphicOn
  have hlogClosed : MeromorphicOn (logDeriv f) (closedBall 0 R) :=
    fun z hz => hfClosed.logDeriv z hz
  have hlog : MeromorphicOn (logDeriv f) (ball 0 R) :=
    fun z hz => hlogClosed z (ball_subset_closedBall hz)
  have heq := logDeriv_poisson_jensen_eventuallyEq
    hR hfClosed hfa h0 hboundary
  have hderiv := hlog.deriv_eventuallyEq_codiscreteWithin hK heq
  filter_upwards [hderiv] with z hz
  simpa [B] using hz

end FewInflection
