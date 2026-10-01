import ModifiedCartan.WeakGradientConstancy
import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem convex_radial_bound_of_zero {G : Set ℂ} (hG : IsOpen G) {F : ℂ → ℝ}
    (hF : ConvexOn ℝ G F) (hc : ContinuousOn F G) (hc0 : ContinuousAt F 0) (h0 : F 0 = 0)
    (hseg : ∀ t : ℝ, 0 < t → t ≤ 1 → (t : ℂ) ∈ G)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : F (t : ℂ) ≤ t * F 1 := by
  let e : ℕ → ℂ := fun ν => ((shrinkingWeakBump ν).rOut : ℂ)
  have heG (ν : ℕ) : e ν ∈ G := hseg _ (inv_pos.mpr (by positivity))
    (inv_le_one_of_one_le₀ (by norm_num))
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [e, Function.comp_def, Complex.ofReal_zero] using! (Complex.continuous_ofReal.tendsto 0).comp shrinkingWeakBump_tendsto
  have hp : Tendsto (fun ν => (1 - t) • e ν + t • (1 : ℂ)) atTop (𝓝 (t : ℂ)) := by
    simpa only [smul_zero, zero_add, Complex.real_smul, mul_one] using
      (he.const_smul (1 - t)).add_const (t • (1 : ℂ))
  have hl := (hc.continuousAt (hG.mem_nhds (hseg t ht ht1))).tendsto.comp hp
  have hr : Tendsto (fun ν => (1 - t) * F (e ν) + t * F 1) atTop (𝓝 (t * F 1)) := by
    simpa only [h0, mul_zero, zero_add, Function.comp_def] using! ((hc0.tendsto.comp he).const_mul (1 - t)).add_const (t * F 1)
  apply le_of_tendsto_of_tendsto hl hr
  exact Eventually.of_forall (fun ν => by
    simpa only [smul_eq_mul, Complex.ofReal_one, Function.comp_def] using! hF.2 (heG ν) (hseg 1 zero_lt_one le_rfl) (sub_nonneg.mpr ht1) ht.le (by ring))

theorem finite_nonpos_eq_zero_of_sum_nonneg {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hv : ∀ j, v j ≤ 0) (hs : 0 ≤ ∑ j, v j) : ∀ j, v j = 0 := by
  have he : ∑ j, v j = 0 := le_antisymm (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hv j)) hs
  exact fun j => (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hv i)).mp he j (Finset.mem_univ j)

theorem finite_balance_forces_equality {ι : Type*} [Fintype ι]
    (v w : ι → ℝ) (hle : ∀ j, v j ≤ w j)
    (hv : 0 ≤ ∑ j, v j) (hw : ∑ j, w j = 0) : ∀ j, v j = w j := by
  have hz : ∀ j, v j - w j = 0 := finite_nonpos_eq_zero_of_sum_nonneg
    (fun j => v j - w j) (fun j => sub_nonpos.mpr (hle j)) (by simpa only [Finset.sum_sub_distrib, hw, sub_zero] using hv)
  exact fun j => sub_eq_zero.mp (hz j)

end ModifiedCartan
#print axioms ModifiedCartan.convex_radial_bound_of_zero
#print axioms ModifiedCartan.finite_balance_forces_equality


