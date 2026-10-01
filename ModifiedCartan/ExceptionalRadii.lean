import ModifiedCartan.EntireZeroCopies
import ModifiedCartan.LogCountingLimit
import ModifiedCartan.WronskianUniform

open scoped Topology
open Filter Set Metric MeasureTheory MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_zero_set_countable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) : {z | f z = 0}.Countable := by
  apply (locallyFinsupp_support_countable (divisor f univ)).mono
  intro z hz
  change divisor f univ z ≠ 0
  rw [entire_divisor_eq_analyticMultiplicity hf]
  have ht : analyticOrderAt f z ≠ ⊤ := by
    intro ht
    have he : f = 0 :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w => hf.analyticAt w)).mp ht
    exact h0 (congrFun he 0)
  have hn : analyticOrderAt f z ≠ 0 := by
    intro he
    exact ((hf.analyticAt z).analyticOrderAt_eq_zero.mp he) hz
  cases ho : analyticOrderAt f z using ENat.recTopCoe with
  | top => exact (ht ho).elim
  | coe m =>
      have hm : m ≠ 0 := by intro hm; simp [ho, hm] at hn
      simpa only [ENat.toNat_natCast, Nat.cast_ne_zero] using hm

/-- Only a countable set of radii can meet an entire function's zeros;
used in the dominated-convergence proof of `lem:entire-majorant`. -/
theorem entire_ae_sphere_no_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) : ∀ᵐ r : ℝ, ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0 := by
  have ha := ((entire_zero_set_countable hf h0).image (fun z : ℂ => ‖z‖)).ae_notMem volume
  filter_upwards [ha] with r hr z hz hzero
  apply hr
  refine ⟨z, hzero, ?_⟩
  simpa only [mem_sphere, dist_zero_right] using hz

theorem taylorWronskian_logCounting_ae_tendsto {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j))
    (hjets : ∀ i j : Fin (n + 1), iteratedDeriv i.val (y j) 0 = if i = j then 1 else 0) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun N => ValueDistribution.logCounting
        (FewInflection.wronskian n (fun j z => (FewInflection.taylorPolynomial (y j) 0 N).eval z))
          (0 : WithTop ℂ) r) atTop
        (𝓝 (ValueDistribution.logCounting (FewInflection.wronskian n y) (0 : WithTop ℂ) r)) := by
  have hW := entire_wronskian_differentiable hy
  have hW0 := wronskian_zero_of_initial_jets hjets
  have hn := entire_ae_sphere_no_zero hW (by rw [hW0]; exact one_ne_zero)
  filter_upwards [ae_restrict_of_ae hn, ae_restrict_mem measurableSet_Ioi] with r hnr hr
  apply logCounting_tendsto_of_uniform_sphere
    (fun N => entire_wronskian_differentiable (fun j =>
      (FewInflection.taylorPolynomial (y j) 0 N).differentiable)) hW
    (Filter.eventually_atTop.mpr ⟨n + 1, fun N hN =>
      entire_taylorPolynomial_wronskian_zero (by omega) hjets⟩) hW0 hr hnr
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere 0 r)).mp
    ((taylorWronskian_tendstoLocallyUniformlyOn hy).mono (subset_univ _))

end ModifiedCartan
#print axioms ModifiedCartan.entire_ae_sphere_no_zero
#print axioms ModifiedCartan.taylorWronskian_logCounting_ae_tendsto
