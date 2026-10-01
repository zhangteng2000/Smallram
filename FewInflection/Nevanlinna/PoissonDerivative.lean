import FewInflection.Nevanlinna.PoissonJensen
import Mathlib.Analysis.Complex.Poisson

/-!
# Differentiating the harmonic Poisson term

The fixed-radius logarithmic-derivative argument differentiates the harmonic
part of Poisson--Jensen.  Mathlib already proves differentiation under the
Herglotz--Riesz circle integral; this file specializes that result to the
boundary function `log ‖f‖` of a meromorphic function and keeps all
integrability hypotheses explicit.
-/

open scoped BigOperators ComplexConjugate Topology
open Complex Filter MeromorphicOn MeasureTheory Metric Real Set

namespace FewInflection

theorem circleIntegrable_ofReal_log_norm
    {f : ℂ → ℂ} (hf : Meromorphic f) (R : ℝ) :
    CircleIntegrable (fun ζ : ℂ => (Real.log ‖f ζ‖ : ℂ)) 0 R := by
  have hreal : CircleIntegrable (fun ζ : ℂ => Real.log ‖f ζ‖) 0 R :=
    hf.meromorphicOn.circleIntegrable_log_norm
  simp only [CircleIntegrable, intervalIntegrable_iff] at hreal ⊢
  exact Complex.ofRealCLM.integrable_comp hreal

/-- The first derivative of the harmonic boundary transform.  The output is
the exact complex Cauchy-kernel integral supplied by Mathlib's Poisson API. -/
theorem hasDerivAt_circleAverage_herglotz_log_norm
    {f : ℂ → ℂ} (hf : Meromorphic f) {R : ℝ} {w : ℂ}
    (hw : w ∈ ball 0 R) :
    HasDerivAt
      (fun v : ℂ => Real.circleAverage
        (fun ζ : ℂ => herglotzRieszKernel 0 v ζ *
          (Real.log ‖f ζ‖ : ℂ)) 0 R)
      (Real.circleAverage
        (fun ζ : ℂ =>
          (2 * ζ / (ζ - w) ^ 2) * (Real.log ‖f ζ‖ : ℂ)) 0 R) w := by
  have h := hasDerivAt_circleAverage_herglotzRieszKernel_smul
    (f := fun ζ : ℂ => (Real.log ‖f ζ‖ : ℂ))
    (circleIntegrable_ofReal_log_norm hf R) hw
  simpa only [smul_eq_mul] using h

end FewInflection
