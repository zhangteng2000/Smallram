import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Analytic logarithm branches

Mathlib provides a continuous logarithm on a simply connected open set.
The local logarithm identity below upgrades that branch to an analytic one.
-/

open scoped Topology
open Filter Set

namespace FewInflection

/-- A continuous lift through the complex exponential is analytic whenever
its exponential is analytic. -/
theorem analyticAt_of_continuousAt_exp
    {g : ℂ → ℂ} {z : ℂ} (hg : ContinuousAt g z)
    (hExp : AnalyticAt ℂ (fun w => Complex.exp (g w)) z) :
    AnalyticAt ℂ g z := by
  have hratio : AnalyticAt ℂ
      (fun w => Complex.exp (g w) / Complex.exp (g z)) z :=
    hExp.div_const (c := Complex.exp (g z))
  have hlog : AnalyticAt ℂ
      (fun w => Complex.log (Complex.exp (g w) / Complex.exp (g z))) z :=
    hratio.clog (by simp)
  have him : ContinuousAt (fun w => (g w - g z).im) z :=
    by
      simpa [Function.comp_def] using
        (Complex.continuous_im.continuousAt.comp (hg.sub continuousAt_const))
  have hstrip : ∀ᶠ w in 𝓝 z,
      -Real.pi < (g w - g z).im ∧ (g w - g z).im < Real.pi := by
    have hmem : Ioo (-Real.pi) Real.pi ∈ 𝓝 ((g z - g z).im) := by
      rw [show (g z - g z).im = 0 by simp]
      exact isOpen_Ioo.mem_nhds
        (show (0 : ℝ) ∈ Ioo (-Real.pi) Real.pi from
          ⟨by linarith [Real.pi_pos], Real.pi_pos⟩)
    simpa only [mem_Ioo] using him.tendsto.eventually hmem
  apply (analyticAt_const.add hlog).congr
  filter_upwards [hstrip] with w hw
  change g z + Complex.log (Complex.exp (g w) / Complex.exp (g z)) = g w
  rw [← Complex.exp_sub, Complex.log_exp hw.1 hw.2.le]
  ring

/-- Analytic logarithm on an open simply connected domain, with no global
analyticity requirement outside that domain. -/
theorem exists_analyticOnNhd_log
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H U)
    (hH0 : ∀ z ∈ U, H z ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧
      ∀ z ∈ U, Complex.exp (L z) = H z := by
  have havoid : 0 ∉ H '' U := by
    rintro ⟨z, hz, hzero⟩
    exact hH0 z hz hzero
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    hUc hUo hH.continuousOn havoid
  refine ⟨L, ?_, hL⟩
  intro z hz
  apply analyticAt_of_continuousAt_exp (hLc.continuousAt (hUo.mem_nhds hz))
  apply (hH z hz).congr
  filter_upwards [hUo.mem_nhds hz] with w hw
  exact (hL hw).symm

end FewInflection
