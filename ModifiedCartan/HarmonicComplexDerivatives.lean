import ModifiedCartan.GradientConvergence
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Higher complex derivatives of harmonic gradients, supporting the remainder
in `eq:singular-logderivative`. Uses mathlib's proved Weierstrass derivative
convergence theorem and analyticity of the complex harmonic gradient. -/

theorem analyticOnNhd_iteratedDeriv {U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (j : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv j f) U := by
  simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv j

theorem locallyUniform_iteratedDeriv {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (h : TendstoLocallyUniformlyOn f g atTop U) (j : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv j (f n)) (iteratedDeriv j g) atTop U := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ j ih =>
    simpa only [iteratedDeriv_succ, Function.comp_def] using
      ih.deriv (Eventually.of_forall (fun n => (analyticOnNhd_iteratedDeriv (hf n) j).differentiableOn)) hU

theorem harmonic_complexGradient_analytic {U : Set ℂ} {H : ℂ → ℝ}
    (hH : HarmonicOnNhd H U) : AnalyticOnNhd ℂ (classicalComplexGradient H) U := by
  intro z hz
  exact HarmonicAt.analyticAt_complex_partial (hH z hz)

theorem harmonicGradient_iteratedDeriv_tendsto {U : Set ℂ} (hU : IsOpen U)
    {Hn : ℕ → ℂ → ℝ} {H : ℂ → ℝ} (hHn : ∀ n, HarmonicOnNhd (Hn n) U)
    (hD : TendstoUniformlyOn (fun n => fderiv ℝ (Hn n)) (fderiv ℝ H) atTop U)
    (j : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv j (classicalComplexGradient (Hn n)))
      (iteratedDeriv j (classicalComplexGradient H)) atTop U := by
  exact locallyUniform_iteratedDeriv hU (fun n => harmonic_complexGradient_analytic (hHn n))
    (classicalComplexGradient_tendstoUniformlyOn hD).tendstoLocallyUniformlyOn j

theorem iteratedDeriv_eqOn_of_ae_eq {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (heq : f =ᵐ[volume.restrict U] g) (j : ℕ) :
    U.EqOn (iteratedDeriv j f) (iteratedDeriv j g) := by
  have hpoint := Measure.eqOn_open_of_ae_eq heq hU hf.continuousOn hg.continuousOn
  intro z hz
  have hnear : f =ᶠ[𝓝 z] g := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hpoint hw
  exact (hnear.iteratedDeriv j).eq_of_nhds


end ModifiedCartan

