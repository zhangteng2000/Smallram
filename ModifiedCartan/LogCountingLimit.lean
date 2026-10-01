import ModifiedCartan.WronskianReciprocalRoots
import Mathlib.Topology.Algebra.IsUniformGroup.Order
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem uniform_log_norm_bound_on_compact {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hf : ContinuousOn f K) (hzero : ∀ z ∈ K, f z ≠ 0)
    (hlim : TendstoUniformlyOn F f atTop K) :
    ∃ B : ℝ, ∀ᶠ N in atTop, ∀ z ∈ K, ‖Real.log ‖F N z‖‖ ≤ B := by
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hf.norm
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hf.norm
  have ha0 : 0 < ‖f a‖ := norm_pos_iff.mpr (hzero a ha)
  have hnorm : TendstoUniformlyOn (fun N z => ‖F N z‖) (fun z => ‖f z‖) atTop K :=
    uniformContinuous_norm.comp_tendstoUniformlyOn hlim
  have hlo : ∀ᶠ N in atTop, ∀ z ∈ K, ‖f a‖ / 2 ≤ ‖F N z‖ := by
    have hn := hnorm.neg.eventually_forall_le
      (show -‖f a‖ < -(‖f a‖ / 2) by linarith)
      (fun z hz => neg_le_neg (hmin hz))
    filter_upwards [hn] with N hN z hz
    simpa only [Pi.neg_apply, neg_le_neg_iff] using hN z hz
  have hhi : ∀ᶠ N in atTop, ∀ z ∈ K, ‖F N z‖ ≤ ‖f b‖ + 1 :=
    hnorm.eventually_forall_le (lt_add_one _) (fun z hz => hmax hz)
  refine ⟨|Real.log (‖f a‖ / 2)| + |Real.log (‖f b‖ + 1)|, ?_⟩
  filter_upwards [hlo, hhi] with N hNlo hNhi z hz
  have hl := Real.log_le_log (half_pos ha0) (hNlo z hz)
  have hu := Real.log_le_log ((half_pos ha0).trans_le (hNlo z hz)) (hNhi z hz)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (Real.log (‖f a‖ / 2)),
    le_abs_self (Real.log (‖f b‖ + 1)), abs_nonneg (Real.log (‖f a‖ / 2)),
    abs_nonneg (Real.log (‖f b‖ + 1))]

/-- Jensen's logarithmic counts converge on every circle avoiding zeros
of the limit. This supplies the integral passage in `lem:entire-majorant`. -/
theorem logCounting_tendsto_of_uniform_sphere {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ N, Differentiable ℂ (F N)) (hf : Differentiable ℂ f)
    (hF0 : ∀ᶠ N in atTop, F N 0 = 1) (hf0 : f 0 = 1)
    {r : ℝ} (hr : 0 < r) (hzero : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0)
    (hlim : TendstoUniformlyOn F f atTop (sphere 0 r)) :
    Tendsto (fun N => ValueDistribution.logCounting (F N) (0 : WithTop ℂ) r) atTop
      (𝓝 (ValueDistribution.logCounting f (0 : WithTop ℂ) r)) := by
  have hne : (sphere (0 : ℂ) r).Nonempty := ⟨(r : ℂ), by
    simp only [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]⟩
  obtain ⟨B, hB⟩ := uniform_log_norm_bound_on_compact (isCompact_sphere 0 r) hne
    hf.continuous.continuousOn hzero hlim
  have havg : Tendsto (fun N => Real.circleAverage (fun z => Real.log ‖F N z‖) 0 r) atTop
      (𝓝 (Real.circleAverage (fun z => Real.log ‖f z‖) 0 r)) := by
    simp only [Real.circleAverage_def, smul_eq_mul]
    apply tendsto_const_nhds.mul
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    · exact Filter.Eventually.of_forall (fun N =>
        (Real.measurable_log.comp ((hF N).continuous.comp (continuous_circleMap 0 r)).norm.measurable).aestronglyMeasurable)
    · filter_upwards [hB] with N hN
      exact Filter.Eventually.of_forall (fun θ _ => hN _ (circleMap_mem_sphere 0 hr.le θ))
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun θ _ =>
        (Real.continuousAt_log (norm_ne_zero_iff.mpr (hzero _ (circleMap_mem_sphere 0 hr.le θ)))).tendsto.comp
          (hlim.tendsto_at (circleMap_mem_sphere 0 hr.le θ)).norm)
  rw [FewInflection.logCounting_zero_eq_circleAverage_sub_const_of_entire hf hr
    (by rw [hf0]; exact one_ne_zero), hf0, norm_one, Real.log_one, sub_zero]
  apply havg.congr'
  filter_upwards [hF0] with N hN
  rw [FewInflection.logCounting_zero_eq_circleAverage_sub_const_of_entire (hF N) hr
    (by rw [hN]; exact one_ne_zero), hN, norm_one, Real.log_one, sub_zero]

end ModifiedCartan
#print axioms ModifiedCartan.logCounting_tendsto_of_uniform_sphere
