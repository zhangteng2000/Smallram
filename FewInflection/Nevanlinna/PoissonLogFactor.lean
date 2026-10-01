import FewInflection.AnalyticLogBranch
import FewInflection.Nevanlinna.PoissonDerivative
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# The logarithmic derivative of the zero-free Poisson factor

The harmonic Poisson formula determines the real part of an analytic
logarithm. The open mapping theorem then shows that its difference from the
Herglotz transform is constant. Differentiating gives the exact boundary
integral for the logarithmic derivative of the nonvanishing factor.
-/

open scoped Topology
open Complex Filter Function Metric Real Set

namespace FewInflection

theorem deriv_eq_of_analytic_re_eq
    {U : Set ℂ} {F G : ℂ → ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hre : ∀ z ∈ U, (F z).re = (G z).re) {z : ℂ} (hz : z ∈ U) :
    deriv F z = deriv G z := by
  have hsub : AnalyticOnNhd ℂ (fun w => F w - G w) U := hF.sub hG
  obtain ⟨c, hc⟩ := hsub.eq_const_of_re_eq_const
    (c₀ := 0) (fun w hw => by simp [hre w hw]) hU hconn
  have heq : (fun w => F w - G w) =ᶠ[𝓝 z] (fun _ => c) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hc w hw
  have hd := heq.deriv_eq
  rw [deriv_fun_sub (hF z hz).differentiableAt (hG z hz).differentiableAt,
    deriv_const] at hd
  exact sub_eq_zero.mp hd

/-- The exact logarithmic-derivative Poisson formula for an analytic function
that is nonzero on a neighborhood of a closed disk. -/
theorem logDeriv_eq_circleAverage_poisson_derivative_of_nonvanishing
    {g : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hg0 : ∀ w ∈ closedBall 0 R, g w ≠ 0)
    (hz : z ∈ ball 0 R) :
    logDeriv g z = Real.circleAverage
      (fun ζ : ℂ => (2 * ζ / (ζ - z) ^ 2) * (Real.log ‖g ζ‖ : ℂ)) 0 R := by
  have hR : 0 < R := pos_of_mem_ball hz
  have hnonempty : (ball (0 : ℂ) R).Nonempty := ⟨0, mem_ball_self hR⟩
  letI : ContractibleSpace (ball (0 : ℂ) R) :=
    (convex_ball (0 : ℂ) R).contractibleSpace hnonempty
  have hsc : IsSimplyConnected (ball (0 : ℂ) R) :=
    SimplyConnectedSpace.ofContractible _
  have hconn : IsConnected (ball (0 : ℂ) R) :=
    ⟨hnonempty, (convex_ball (0 : ℂ) R).isPreconnected⟩
  obtain ⟨L, hL, hExp⟩ := exists_analyticOnNhd_log hsc isOpen_ball
    (hg.mono ball_subset_closedBall) (fun w hw => hg0 w (ball_subset_closedBall hw))
  have hsphere : sphere (0 : ℂ) |R| ⊆ closedBall 0 R := by
    simpa [abs_of_pos hR] using (sphere_subset_closedBall :
      sphere (0 : ℂ) R ⊆ closedBall 0 R)
  have hreal' := (hg.mono hsphere).meromorphicOn.circleIntegrable_log_norm
  have hreal : CircleIntegrable (fun ζ => Real.log ‖g ζ‖) 0 R := by
    simpa [abs_of_pos hR] using hreal'
  have hcomplex : CircleIntegrable (fun ζ => (Real.log ‖g ζ‖ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hreal ⊢
    exact Complex.ofRealCLM.integrable_comp hreal
  let H : ℂ → ℂ := fun w => Real.circleAverage
    (fun ζ : ℂ => herglotzRieszKernel 0 w ζ • (Real.log ‖g ζ‖ : ℂ)) 0 R
  have hH : AnalyticOnNhd ℂ H (ball 0 R) :=
    analyticOnNhd_circleAverage_herglotzRieszKernel_smul hcomplex
  have hHre : ∀ w ∈ ball 0 R, (H w).re = Real.log ‖g w‖ := by
    intro w hw
    have hharm : InnerProductSpace.HarmonicOnNhd (fun v => Real.log ‖g v‖)
        (closedBall 0 R) := fun v hv =>
      (hg v hv).harmonicAt_log_norm (hg0 v hv)
    exact (re_circleAverage_herglotzRieszKernel_smul hreal hw).trans
      (hharm.circleAverage_re_herglotzRieszKernel_smul hw)
  have hLre : ∀ w ∈ ball 0 R, (L w).re = Real.log ‖g w‖ := by
    intro w hw
    rw [← hExp w hw, Complex.norm_exp, Real.log_exp]
  have hderiv : deriv L z = deriv H z :=
    deriv_eq_of_analytic_re_eq isOpen_ball hconn hL hH
      (fun w hw => (hLre w hw).trans (hHre w hw).symm) hz
  have heq : (Complex.exp ∘ L) =ᶠ[𝓝 z] g := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hExp w hw
  have hlog : logDeriv g z = deriv L z := by
    rw [← (logDeriv_congr_nhds heq).eq_of_nhds,
      logDeriv_comp Complex.differentiable_exp.differentiableAt (hL z hz).differentiableAt,
      Complex.logDeriv_exp]
    simp
  rw [hlog, hderiv]
  exact (hasDerivAt_circleAverage_herglotzRieszKernel_smul hcomplex hz).deriv

end FewInflection
