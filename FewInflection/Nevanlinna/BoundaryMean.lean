import FewInflection.Nevanlinna.CountingCharacteristic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Boundary absolute-log bookkeeping

The fixed-radius proof replaces the absolute boundary mean of
`log ‖h‖` by the sum of the proximity functions of `h` and `1/h`.
The identity is proved pointwise and then transported through the circle
average using Mathlib's meromorphic circle-integrability results.
-/

open scoped BigOperators Topology
open Filter Asymptotics MeromorphicAt MeromorphicOn MeasureTheory Metric Real Set
open ValueDistribution

namespace FewInflection

theorem abs_log_eq_posLog_add_posLog_inv (x : ℝ) :
    |Real.log x| = Real.posLog x + Real.posLog x⁻¹ := by
  have hd := Real.posLog_sub_posLog_inv (x := x)
  by_cases h : 0 ≤ Real.log x
  · rw [abs_of_nonneg h]
    have hinv : Real.log x⁻¹ ≤ 0 := by
      rw [Real.log_inv]
      linarith
    have hzero : Real.posLog x⁻¹ = 0 := by
      rw [Real.posLog_apply, max_eq_left hinv]
    linarith
  · rw [abs_of_neg (lt_of_not_ge h)]
    have hzero : Real.posLog x = 0 := by
      rw [Real.posLog_apply, max_eq_left (le_of_not_ge h)]
    linarith

/-- The absolute logarithmic boundary mean is the sum of the two proximity
means. The equality is valid for every radius, including radii containing
zeros, because the circle integral is interpreted measure-theoretically. -/
theorem circleAverage_abs_log_norm_eq_proximity_add_inv
    {f : ℂ → ℂ} (hf : Meromorphic f) (R : ℝ) :
    Real.circleAverage (fun x => |Real.log ‖f x‖|) 0 R =
      ValueDistribution.proximity f ⊤ R +
        ValueDistribution.proximity (fun z => (f z)⁻¹) ⊤ R := by
  have hpos : CircleIntegrable (fun x => Real.posLog ‖f x‖) 0 R := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    intro x hx
    exact hf x
  have hinv : CircleIntegrable (fun x => Real.posLog ‖(f x)⁻¹‖) 0 R := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    intro x hx
    exact hf.inv x
  have hadd : Real.circleAverage
      ((fun x => Real.posLog ‖f x‖) +
        (fun x => Real.posLog ‖(f x)⁻¹‖)) 0 R =
      Real.circleAverage (fun x => Real.posLog ‖f x‖) 0 R +
        Real.circleAverage (fun x => Real.posLog ‖(f x)⁻¹‖) 0 R :=
    Real.circleAverage_add hpos hinv
  calc
    Real.circleAverage (fun x => |Real.log ‖f x‖|) 0 R =
        Real.circleAverage
          ((fun x => Real.posLog ‖f x‖) +
            (fun x => Real.posLog ‖(f x)⁻¹‖)) 0 R := by
      apply Real.circleAverage_congr_sphere
      intro x hx
      dsimp
      simpa [norm_inv] using abs_log_eq_posLog_add_posLog_inv ‖f x‖
    _ = _ := hadd
    _ = _ := by
      rw [ValueDistribution.proximity_top, ValueDistribution.proximity_top]

end FewInflection

