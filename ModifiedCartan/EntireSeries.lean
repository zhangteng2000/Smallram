import FewInflection.WronskianLimits
import Mathlib.Analysis.Normed.Group.FunctionSeries

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Local summable bounds on actual terms give locally uniform convergence
of their finite sums throughout the complex plane. -/
theorem entireSeries_locallyUniform {F : ℕ → ℂ → ℂ}
    (hb : ∀ R : ℝ, 0 < R → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ i z, ‖z‖ ≤ R → ‖F i z‖ ≤ u i) :
    TendstoLocallyUniformlyOn (fun S : Finset ℕ => fun z => ∑ i ∈ S, F i z)
      (fun z => ∑' i, F i z) atTop univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  obtain ⟨u, hu, hbu⟩ := hb R hR
  apply tendstoUniformlyOn_tsum hu
  intro i z hz
  exact hbu i z (by simpa only [mem_closedBall, dist_zero_right] using hKR hz)

theorem entireSeries_differentiable {F : ℕ → ℂ → ℂ}
    (hF : ∀ i, Differentiable ℂ (F i))
    (hb : ∀ R : ℝ, 0 < R → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ i z, ‖z‖ ≤ R → ‖F i z‖ ≤ u i) :
    Differentiable ℂ (fun z => ∑' i, F i z) := by
  apply differentiableOn_univ.mp
  apply (entireSeries_locallyUniform hb).differentiableOn _ isOpen_univ
  exact Eventually.of_forall (fun S => DifferentiableOn.fun_sum (fun i _ => (hF i).differentiableOn))

/-- Termwise differentiation to any finite order, proved from actual
locally uniform holomorphic convergence rather than assumed derivative bounds. -/
theorem entireSeries_hasSum_iteratedDeriv {F : ℕ → ℂ → ℂ}
    (hF : ∀ i, Differentiable ℂ (F i))
    (hb : ∀ R : ℝ, 0 < R → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ i z, ‖z‖ ≤ R → ‖F i z‖ ≤ u i)
    (m : ℕ) (z : ℂ) :
    HasSum (fun i => iteratedDeriv m (F i) z)
      (iteratedDeriv m (fun w => ∑' i, F i w) z) := by
  have ht := FewInflection.tendsto_iteratedDeriv_of_locallyUniformlyOn_at isOpen_univ
    (mem_univ z) (entireSeries_locallyUniform hb)
    (Eventually.of_forall (fun S => Differentiable.fun_sum (fun i _ => hF i))) m
  have he (S : Finset ℕ) : iteratedDeriv m (fun w => ∑ i ∈ S, F i w) z =
      ∑ i ∈ S, iteratedDeriv m (F i) z := by
    rw [iteratedDeriv_fun_sum (fun i _ => (hF i).contDiff.contDiffAt)]
  simpa only [he] using! ht

end ModifiedCartan
#print axioms ModifiedCartan.entireSeries_differentiable
#print axioms ModifiedCartan.entireSeries_hasSum_iteratedDeriv
