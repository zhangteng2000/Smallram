import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- An elementary antiderivative for LaTeX `eq:kernel-identity` above
the root radius a. -/
noncomputable def rootKernelPrimitive (r a t : ℝ) : ℝ :=
  -(Real.log (1 + r / t) / r) - Real.log (t / a) / (r + t)

theorem rootKernelPrimitive_hasDerivAt {r a t : ℝ}
    (hr : 0 < r) (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (rootKernelPrimitive r a) (Real.log (t / a) / (r + t) ^ 2) t := by
  have hrt : r + t ≠ 0 := (add_pos hr ht).ne'
  have hsum : 1 + r / t ≠ 0 := (by positivity : (0 : ℝ) < 1 + r / t).ne'
  have hfirst := (((hasDerivAt_const t (1 : ℝ)).add
    ((hasDerivAt_const t r).div (hasDerivAt_id t) ht.ne')).log hsum).div_const r
  have hsecond := (((hasDerivAt_id t).div_const a).log (div_pos ht ha).ne').div
    ((hasDerivAt_const t r).add (hasDerivAt_id t)) hrt
  convert! hfirst.neg.sub hsecond using 1
  simp only [zero_mul, mul_one, zero_sub, zero_add, Pi.add_apply, Pi.div_apply, id_eq]
  field_simp
  <;> ring

theorem rootKernelPrimitive_tendsto_zero {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    Tendsto (rootKernelPrimitive r a) atTop (𝓝 0) := by
  have hden : Tendsto (fun t : ℝ => r + t) atTop atTop := by
    simpa only [add_comm, id_eq] using tendsto_atTop_add_const_right atTop r tendsto_id
  have hratio : Tendsto (fun t : ℝ => t / (r + t)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub (hden.const_div_atTop r)
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hn := (add_pos hr ht).ne'
    field_simp
    <;> ring
  have hlog : Tendsto (fun t : ℝ => Real.log (t / a) / (r + t)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun t : ℝ => Real.log t / t - Real.log a / t) atTop (𝓝 0) := by
      simpa only [id_eq, sub_zero] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.sub
        (tendsto_id.const_div_atTop (Real.log a))
    have hh := hbase.mul hratio
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.log_div ht.ne' ha.ne']
    field_simp
    <;> ring
  have hsmall : Tendsto (fun t : ℝ => 1 + r / t) atTop (𝓝 1) := by
    simpa only [add_zero, id_eq] using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_id.const_div_atTop r)
  have hfirst := ((hsmall.log one_ne_zero).div_const r).neg
  change Tendsto (fun t => rootKernelPrimitive r a t) atTop (𝓝 0)
  simpa only [Real.log_one, zero_div, neg_zero, sub_zero, rootKernelPrimitive] using hfirst.sub hlog

theorem root_log_kernel_integrable_and_integral {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    IntegrableOn (fun t => Real.log (t / a) / (r + t) ^ 2) (Ioi a) ∧
      r * (∫ t in Ioi a, Real.log (t / a) / (r + t) ^ 2) = Real.log (1 + r / a) := by
  have hd : ∀ t ∈ Ici a, HasDerivAt (rootKernelPrimitive r a)
      (Real.log (t / a) / (r + t) ^ 2) t :=
    fun t ht => rootKernelPrimitive_hasDerivAt hr ha (ha.trans_le ht)
  have hn : ∀ t ∈ Ioi a, 0 ≤ Real.log (t / a) / (r + t) ^ 2 := by
    intro t ht
    apply div_nonneg (Real.log_nonneg ((one_le_div ha).mpr ht.le)) (sq_nonneg _)
  have ht := rootKernelPrimitive_tendsto_zero hr ha
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn ht, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hn ht]
  simp only [rootKernelPrimitive, div_self ha.ne', Real.log_one, zero_div, sub_zero,
    zero_sub, neg_neg]
  exact mul_div_cancel₀ _ hr.ne'

end ModifiedCartan
#print axioms ModifiedCartan.root_log_kernel_integrable_and_integral
