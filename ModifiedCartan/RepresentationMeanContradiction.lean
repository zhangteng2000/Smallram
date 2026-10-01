import ModifiedCartan.NormalizedLogUpper
import ModifiedCartan.RescaledRepresentation
import ModifiedCartan.CharacteristicZero

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The M9 mean identity at radius one contradicts nonpositive constant
coordinate logarithm limits. This completes the upper-bound half of the
local nonvanishing argument for `prop:indices`. -/
theorem representation_mean_contradicts_nonpositive_constants {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hf0 : ∀ j, f.coord j 0 ≠ 0)
    {r : ℕ → ℝ} (hrpos : ∀ ν, 0 < r ν)
    (hs : Tendsto (fun ν => characteristic f (r ν)) atTop atTop)
    {H : ℕ → ℂ → ℂ} {c : ℕ → ℝ} {a : Index n → ℝ}
    (hf : ∀ ν j, AnalyticOnNhd ℂ (rescaledRepresentation f (r ν) (H ν) j) (ball 0 3))
    (hu : ∀ j, LocalLpConvergence 1 (ball (0 : ℂ) 3)
      (fun ν z => (characteristic f (r ν))⁻¹ *
        Real.log ‖rescaledRepresentation f (r ν) (H ν) j z‖) (fun _ => a j))
    (ha : ∀ j, a j ≤ 0)
    (hdata : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H ν) (ball 0 3) ∧
      Real.circleAverage
        (fun z => Real.log (euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j z))) 0 1 =
          characteristic f (r ν) + c ν)
    (hc : Tendsto (fun ν => c ν / characteristic f (r ν)) atTop (𝓝 0)) : False := by
  have hspos (ν : ℕ) := characteristic_pos_of_transcendental f htrans (hrpos ν)
  have hbound : ∀ᶠ ν in atTop, ∀ j z, z ∈ closedBall (0 : ℂ) 1 →
      ‖rescaledRepresentation f (r ν) (H ν) j z‖ ≤ Real.exp ((1 / 2) * characteristic f (r ν)) := by
    apply Filter.eventually_all.mpr
    intro j
    apply normalized_log_eventually_small_on_unit_disk (fun ν => hf ν j) _ hspos (hu j) (ha j) (by norm_num)
    intro ν
    refine ⟨0, mem_ball_self (by norm_num), ?_⟩
    simpa only [rescaledRepresentation, mul_zero] using mul_ne_zero (Complex.exp_ne_zero _) (hf0 j)
  have hratio : ∀ᶠ ν in atTop, 1 + c ν / characteristic f (r ν) ≤
      Real.log (Real.sqrt (n + 1 : ℝ)) / characteristic f (r ν) + 1 / 2 := by
    filter_upwards [hbound, hdata] with ν hν hdν
    have hL : ContinuousOn
        (fun z => Real.log (euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j z)))
        (ball (0 : ℂ) 3) := by
      simpa only [rescaledRepresentation_log_norm, Function.comp_def, Pi.mul_apply, Pi.sub_apply, id_eq] using!
        ((curve_log_euclideanNorm_continuous f).comp (continuous_const.mul continuous_id)).continuousOn.sub
          (Complex.continuous_re.comp_continuousOn hdν.1.continuousOn)
    have hci : CircleIntegrable
        (fun z => Real.log (euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j z))) 0 1 := by
      apply ContinuousOn.circleIntegrable'
      simpa only [abs_one] using hL.mono (sphere_subset_closedBall.trans (closedBall_subset_ball (by norm_num : (1 : ℝ) < 3)))
    have havg := Real.circleAverage_mono_on_of_le_circle hci
      (a := Real.log (Real.sqrt (n + 1 : ℝ)) + (1 / 2) * characteristic f (r ν)) (by
        intro z hz
        have hz1 : z ∈ closedBall (0 : ℂ) 1 := by
          simpa only [abs_one] using sphere_subset_closedBall hz
        have hv : (fun j => rescaledRepresentation f (r ν) (H ν) j z) ≠ 0 := by
          intro he
          obtain ⟨j, hj⟩ := rescaledRepresentation_reduced f (r ν) (H ν) z
          exact hj (congrFun he j)
        have hn : ‖fun j => rescaledRepresentation f (r ν) (H ν) j z‖ ≤
            Real.exp ((1 / 2) * characteristic f (r ν)) :=
          (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr (fun j => hν j z hz1)
        have hlog := Real.log_le_log (norm_pos_iff.mpr hv) hn
        rw [Real.log_exp] at hlog
        exact (log_euclideanNorm_le hv).trans (add_le_add le_rfl hlog))
    rw [hdν.2] at havg
    have hcanc := div_mul_cancel₀ (c ν) (hspos ν).ne'
    have hlanc := div_mul_cancel₀ (Real.log (Real.sqrt (n + 1 : ℝ))) (hspos ν).ne'
    nlinarith [hspos ν]
  have hl : Tendsto (fun ν => 1 + c ν / characteristic f (r ν)) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hc
  have hr : Tendsto (fun ν => Real.log (Real.sqrt (n + 1 : ℝ)) / characteristic f (r ν) + 1 / 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [zero_add] using (hs.const_div_atTop (Real.log (Real.sqrt (n + 1 : ℝ)))).add_const (1 / 2 : ℝ)
  have hbad := le_of_tendsto_of_tendsto hl hr hratio
  norm_num at hbad

end ModifiedCartan
#print axioms ModifiedCartan.representation_mean_contradicts_nonpositive_constants
