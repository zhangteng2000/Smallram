import ModifiedCartan.MaximumModulus
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Instances.EReal.Lemmas

open scoped Topology
open Filter Set Metric Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- Literal scalar entire-function order from the paragraph preceding
LaTeX `lem:entire-majorant`. Both positive logarithms are retained. -/
noncomputable def entireOrder (f : ℂ → ℂ) : EReal :=
  limsup (fun r : ℝ =>
    ((Real.posLog (Real.posLog (maximumModulus f r)) / Real.log r : ℝ) : EReal)) atTop

theorem entireOrder_nonneg (f : ℂ → ℂ) : 0 ≤ entireOrder f := by
  apply le_trans (le_liminf_of_le (h := ?_)) liminf_le_limsup
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have h : 0 ≤ Real.posLog (Real.posLog (maximumModulus f r)) / Real.log r :=
    div_nonneg Real.posLog_nonneg (Real.log_pos (by linarith)).le
  exact_mod_cast h

theorem maximumModulus_const (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus (fun _ => c) r = ‖c‖ := by
  obtain ⟨z, _, hz⟩ := maximumModulus_attained (continuous_const (y := c)) hr
  exact hz

theorem entireOrder_const (c : ℂ) : entireOrder (fun _ => c) = 0 := by
  have ht : Tendsto (fun r : ℝ =>
      Real.posLog (Real.posLog (maximumModulus (fun _ => c) r)) / Real.log r) atTop (𝓝 0) := by
    apply (Real.tendsto_log_atTop.const_div_atTop (Real.posLog (Real.posLog ‖c‖))).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    rw [maximumModulus_const c hr]
  exact (EReal.tendsto_coe.mpr ht).limsup_eq

theorem entireOrder_eventually_posLog_le_rpow {f : ℂ → ℂ} {β : ℝ}
    (hβ : entireOrder f < (β : EReal)) :
    ∀ᶠ r : ℝ in atTop, Real.posLog (maximumModulus f r) ≤ r ^ β := by
  filter_upwards [eventually_lt_of_limsup_lt hβ, eventually_ge_atTop (2 : ℝ)] with r hr hr2
  have hr0 : 0 < r := by linarith
  have hlog : 0 < Real.log r := Real.log_pos (by linarith)
  have hratio : Real.posLog (Real.posLog (maximumModulus f r)) / Real.log r < β := by
    exact_mod_cast hr
  apply Real.le_rpow_of_log_le hr0
  exact (le_max_right 0 _).trans ((div_lt_iff₀ hlog).mp hratio).le

/-- A strict order bound implies the exact little-o estimate needed by
the envelope lemma. The intermediate exponent is constructed, not assumed. -/
theorem entireOrder_posLog_isLittleO {f : ℂ → ℂ} {α : ℝ}
    (hα : entireOrder f < (α : EReal)) :
    (fun r => Real.posLog (maximumModulus f r)) =o[atTop] (fun r => r ^ α) := by
  obtain ⟨β, hβ, hβα⟩ := EReal.exists_between_coe_real hα
  have hβα' : β < α := by exact_mod_cast hβα
  have hpow : Tendsto (fun r : ℝ => r ^ (β - α)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hβα')
  apply isLittleO_of_tendsto' ?_ (squeeze_zero' ?_ ?_ hpow)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    intro he
    exact False.elim ((Real.rpow_pos_of_pos hr α).ne' he)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_nonneg Real.posLog_nonneg (Real.rpow_nonneg hr.le α)
  · filter_upwards [entireOrder_eventually_posLog_le_rpow hβ,
      eventually_gt_atTop (0 : ℝ)] with r hr hr0
    rw [Real.rpow_sub hr0]
    exact div_le_div_of_nonneg_right hr (Real.rpow_nonneg hr0.le α)

/-- A global power bound on [1,infinity), including its initial compact
interval. This is the first estimate in `lem:entire-majorant`. -/
theorem entireOrder_exists_posLog_power_bound {f : ℂ → ℂ}
    (hf : Continuous f) {β : ℝ} (hβ : entireOrder f < (β : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      Real.posLog (maximumModulus f r) ≤ C * r ^ β := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (entireOrder_eventually_posLog_le_rpow hβ)
  let S : ℝ := max 1 R
  have hratio : ContinuousOn
      (fun r => Real.posLog (maximumModulus f r) / r ^ β) (Icc 1 S) := by
    apply (Real.continuous_posLog.comp_continuousOn
      ((maximumModulus_continuousOn hf).mono (fun r hr => by change 0 ≤ r; linarith [hr.1]))).div
    · intro r hr
      exact (Real.continuousAt_rpow_const r β (Or.inl (by linarith [hr.1]))).continuousWithinAt
    · intro r hr
      exact (Real.rpow_pos_of_pos (by linarith [hr.1]) β).ne'
  obtain ⟨B, hB⟩ := (isCompact_Icc.bddAbove_image hratio)
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  by_cases hrs : r ≤ S
  · have hbr := hB (mem_image_of_mem _ ⟨hr, hrs⟩)
    have hbound : Real.posLog (maximumModulus f r) / r ^ β ≤ max 1 B :=
      hbr.trans (le_max_right _ _)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hr0 β)).mp hbound
  · exact (hR r ((le_max_right 1 R).trans (le_of_not_ge hrs))).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left 1 B) (Real.rpow_nonneg hr0.le β))

end ModifiedCartan
#print axioms ModifiedCartan.entireOrder_posLog_isLittleO
#print axioms ModifiedCartan.entireOrder_exists_posLog_power_bound
