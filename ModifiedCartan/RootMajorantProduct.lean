import ModifiedCartan.EntireZeroCopies
import Mathlib.Analysis.SpecialFunctions.Log.Summable

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The literal product in LaTeX `eq:entire-majorant`, indexed by the
actual analytic zero multiplicities. -/
noncomputable def rootMajorantProduct (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∏' a : entireZeroCopies f, (1 + r / ‖a.1‖)

theorem rootMajorant_log_summable {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (r : ℝ) :
    Summable (fun a : entireZeroCopies f => Real.log (1 + r / ‖a.1‖)) := by
  simpa only [div_eq_mul_inv] using Real.summable_log_one_add_of_summable (hs.mul_left r)

theorem rootMajorant_multipliable {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (r : ℝ) :
    Multipliable (fun a : entireZeroCopies f => (1 + r / ‖a.1‖)) := by
  simpa only [div_eq_mul_inv] using Real.multipliable_one_add_of_summable (hs.mul_left r)

theorem rootMajorantProduct_eq_exp {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    {r : ℝ} (hr : 0 ≤ r) :
    rootMajorantProduct f r = Real.exp (∑' a : entireZeroCopies f, Real.log (1 + r / ‖a.1‖)) := by
  exact (Real.rexp_tsum_eq_tprod (fun a => by positivity)
    (rootMajorant_log_summable hs r)).symm

theorem rootMajorantProduct_pos {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    {r : ℝ} (hr : 0 ≤ r) : 0 < rootMajorantProduct f r := by
  rw [rootMajorantProduct_eq_exp hs hr]
  exact Real.exp_pos _

theorem log_rootMajorantProduct {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    {r : ℝ} (hr : 0 ≤ r) :
    Real.log (rootMajorantProduct f r) =
      ∑' a : entireZeroCopies f, Real.log (1 + r / ‖a.1‖) := by
  rw [rootMajorantProduct_eq_exp hs hr, Real.log_exp]

theorem rootMajorant_log_sum_le_reciprocal_sum {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    {r : ℝ} (hr : 0 ≤ r) :
    (∑' a : entireZeroCopies f, Real.log (1 + r / ‖a.1‖)) ≤
      r * ∑' a : entireZeroCopies f, ‖a.1‖⁻¹ := by
  rw [← hs.tsum_mul_left r]
  apply (rootMajorant_log_summable hs r).tsum_le_tsum _ (hs.mul_left r)
  intro a
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + r / ‖a.1‖ by positivity)
  simpa only [add_sub_cancel_left, div_eq_mul_inv] using h

end ModifiedCartan
#print axioms ModifiedCartan.rootMajorantProduct_eq_exp
#print axioms ModifiedCartan.log_rootMajorantProduct
