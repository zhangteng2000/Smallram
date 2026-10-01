import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Meromorphic.LogDeriv

/-!
# Logarithmic derivatives of a canonical decomposition

This file records the codiscrete differentiation step that follows the
Poisson--Jensen identity.  It uses Mathlib's meromorphic logarithmic-derivative
API, so the finite divisor sum is differentiated as an actual finite-support
`finsum` rather than being postulated as an analytic estimate.
-/

open scoped BigOperators Topology
open Complex Filter Function MeromorphicOn Metric Real Set

namespace FewInflection

noncomputable section

theorem canonicalDecomp_logDeriv_eventuallyEq
    {f g : ℂ → ℂ} {R : ℝ}
    (D : CanonicalDecomp f g R) (hR : 0 < R) :
    logDeriv f =ᶠ[codiscreteWithin (ball 0 R)]
      (fun z =>
        (∑ᶠ a, (-(MeromorphicOn.divisor f (ball 0 R) a)) •
          logDeriv (canonicalFactor R a) z) + logDeriv g z) := by
  let d : ℂ → ℤ := fun a => -(MeromorphicOn.divisor f (ball 0 R) a)
  let P : ℂ → ℂ := ∏ᶠ a, (canonicalFactor R a) ^ d a
  have hd : (support d).Finite := by
    simpa [d] using D.meromorphicOn.divisor_ball_support_finite
  have hP : MeromorphicOn P (ball 0 R) := by
    dsimp [P]
    apply MeromorphicOn.finprod
    intro a
    exact (Complex.meromorphic_canonicalFactor R a).meromorphicOn.zpow _
  have hPorder : ∀ z ∈ ball 0 R, meromorphicOrderAt P z ≠ ⊤ := by
    intro z hz
    dsimp [P]
    apply meromorphicOrderAt_finprod_ne_top
    · intro a
      exact (Complex.meromorphic_canonicalFactor R a).meromorphicAt.zpow _
    · intro a
      rw [meromorphicOrderAt_zpow (Complex.meromorphic_canonicalFactor R a).meromorphicAt]
      lift meromorphicOrderAt (canonicalFactor R a) z to ℤ using
        (Complex.meromorphicOrderAt_canonicalFactor_ne_top a hR) with m
      exact WithTop.mul_ne_top (by simp) (by simp)
  have hg : MeromorphicOn g (ball 0 R) :=
    D.meromorphicNFOn.meromorphicOn.mono_set ball_subset_closedBall
  have hgorder : ∀ z ∈ ball 0 R, meromorphicOrderAt g z ≠ ⊤ := by
    intro z hz
    have hgclosed : MeromorphicOn g (closedBall 0 R) := D.meromorphicNFOn.meromorphicOn
    have h0ball : (0 : ℂ) ∈ ball 0 R := by
      rw [mem_ball_zero_iff, norm_zero]
      exact hR
    have h0closed : (0 : ℂ) ∈ closedBall 0 R := by
      rw [mem_closedBall_zero_iff, norm_zero]
      exact le_of_lt hR
    have hzero : meromorphicOrderAt g 0 = 0 := by
      exact (D.meromorphicNFOn h0closed).meromorphicOrderAt_eq_zero_iff.mpr
        (D.ne_zero 0 h0ball)
    exact hgclosed.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected h0closed
      (ball_subset_closedBall hz) (by rw [hzero]; exact WithTop.coe_ne_top)
  have hmul :
      logDeriv (P * g) =ᶠ[codiscreteWithin (ball 0 R)]
        logDeriv P + logDeriv g := by
    exact hP.logDeriv_mul_eventuallyEq hg hPorder hgorder
  have hfin :
      logDeriv P =ᶠ[codiscreteWithin (ball 0 R)]
        (fun z => ∑ᶠ a, d a • logDeriv (canonicalFactor R a) z) := by
    dsimp [P]
    exact MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hd
      (fun a => (Complex.meromorphic_canonicalFactor R a).meromorphicOn)
      (fun a z hz => Complex.meromorphicOrderAt_canonicalFactor_ne_top a hR)
  have heq : f =ᶠ[codiscreteWithin (ball 0 R)] (P * g) := by
    have hD := D.eventuallyEq.filter_mono
      (codiscreteWithin_mono ball_subset_closedBall)
    filter_upwards [hD] with z hz
    simpa [P, d, Pi.smul_apply', smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hz
  have hlog :
      logDeriv f =ᶠ[codiscreteWithin (ball 0 R)] logDeriv (P * g) :=
    logDeriv_congr_codiscreteWithin isOpen_ball heq
  filter_upwards [hlog, hmul, hfin] with z hz hzg hzp
  rw [hz, hzg]
  simpa [Pi.add_apply, d] using congrArg (fun x => x + logDeriv g z) hzp

end

end FewInflection
