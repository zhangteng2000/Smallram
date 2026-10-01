import ModifiedCartan.NormComparison
import FewInflection.Jensen
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.HahnBanach

open scoped BigOperators Topology
open Filter Metric Set

namespace ModifiedCartan

theorem log_norm_le_circleAverage_log_majorant
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) {c : ℂ} (hc : h c ≠ 0)
    {U : ℂ → ℝ} (hUc : Continuous U) (hUp : ∀ z, 0 < U z)
    (hbound : ∀ z, ‖h z‖ ≤ U z) {r : ℝ} (hr : 0 < r) :
    Real.log ‖h c‖ ≤ Real.circleAverage (fun z => Real.log (U z)) c r := by
  classical
  have ha := Complex.analyticOnNhd_univ_iff_differentiable.mpr hh
  have hn : ∀ᶠ z in codiscrete ℂ, h z ≠ 0 := ha.preimage_zero_mem_codiscrete hc
  have hns : ∀ᶠ z in codiscreteWithin (sphere c |r|), h z ≠ 0 :=
    hn.filter_mono (Filter.codiscreteWithin_mono (Set.subset_univ _))
  let v : ℂ → ℝ := fun z => if h z = 0 then Real.log (U z) else Real.log ‖h z‖
  have heq : v =ᶠ[codiscreteWithin (sphere c |r|)] (fun z => Real.log ‖h z‖) := by
    filter_upwards [hns] with z hz
    simp [v, hz]
  have hint : CircleIntegrable (fun z => Real.log ‖h z‖) c r :=
    (ha.meromorphicOn.mono_set (Set.subset_univ _)).circleIntegrable_log_norm
  have hvint : CircleIntegrable v c r :=
    CircleIntegrable.congr_codiscreteWithin heq.symm hint
  have hUint : CircleIntegrable (fun z => Real.log (U z)) c r :=
    (hUc.log (fun z => (hUp z).ne')).continuousOn.circleIntegrable'
  have hmean := Real.circleAverage_mono hvint hUint (by
    intro z _
    by_cases hz : h z = 0
    · simp [v, hz]
    · simpa [v, hz] using Real.log_le_log (norm_pos_iff.mpr hz) (hbound z))
  rw [Real.circleAverage_congr_codiscreteWithin heq hr.ne'] at hmean
  have hj := FewInflection.scalar_circleAverage_log_norm_sub_nonneg_at hh hr hc
  linarith

/-- An entire scalar support function attains the Euclidean norm at the centre.
This supplies the scalar Jensen comparison without a maximum-norm substitution. -/
theorem exists_entire_euclidean_support {n : ℕ} (f : Curve n) (c : ℂ) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h c ≠ 0 ∧
      ‖h c‖ = euclideanNorm (f.vector c) ∧ ∀ z, ‖h z‖ ≤ euclideanNorm (f.vector z) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Index n => ℂ)).symm
  have he (v : Index n → ℂ) : ‖e v‖ = euclideanNorm v := by
    rw [PiLp.norm_eq_of_L2]
    rfl
  have hv : ‖e (f.vector c)‖ ≠ 0 := by
    rw [he]
    exact (euclideanNorm_pos (f.vector_ne_zero c)).ne'
  obtain ⟨L, hL, hLc⟩ := exists_dual_vector ℂ (e (f.vector c)) hv
  let h : ℂ → ℂ := fun z => L (e (f.vector z))
  have hdiff : Differentiable ℂ h :=
    L.differentiable.comp (e.differentiable.comp (differentiable_pi.mpr f.holomorphic))
  have hnorm : ‖h c‖ = euclideanNorm (f.vector c) := by
    calc
      ‖h c‖ = ‖(‖e (f.vector c)‖ : ℂ)‖ := congrArg norm hLc
      _ = ‖e (f.vector c)‖ := by simp
      _ = euclideanNorm (f.vector c) := he _
  have hc : h c ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hnorm]
    exact (euclideanNorm_pos (f.vector_ne_zero c)).ne'
  refine ⟨h, hdiff, hc, hnorm, ?_⟩
  intro z
  simpa [h, hL, he] using L.le_opNorm (e (f.vector z))

/-- Scalar Jensen applied to a supporting linear functional of the Euclidean norm.
LaTeX context: `eq:zerojensen` and the characteristic preceding `cartan`. -/
theorem euclidean_characteristic_nonneg_at {n : ℕ} (f : Curve n) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    0 ≤ Real.circleAverage (fun z => Real.log (euclideanNorm (f.vector z))) c r -
      Real.log (euclideanNorm (f.vector c)) := by
  obtain ⟨h, hdiff, hc, hnorm, hbound⟩ := exists_entire_euclidean_support f c
  have hU : Continuous (fun z => euclideanNorm (f.vector z)) :=
    euclideanNorm_continuous.comp (continuous_pi (fun j => (f.holomorphic j).continuous))
  have hj := log_norm_le_circleAverage_log_majorant hdiff hc hU
    (fun z => euclideanNorm_pos (f.vector_ne_zero z)) hbound hr
  rw [hnorm] at hj
  exact sub_nonneg.mpr hj

theorem characteristic_nonneg {n : ℕ} (f : Curve n) {r : ℝ} (hr : 0 < r) :
    0 ≤ characteristic f r := euclidean_characteristic_nonneg_at f 0 hr

end ModifiedCartan

