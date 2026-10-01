import ModifiedCartan.OrdinaryGrowthOrders
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Topology.Instances.EReal.Lemmas

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- Bounded additive errors are negligible relative to a function tending
to infinity. Used for the scalar/curve characteristic comparison in `thm:A`. -/
theorem isEquivalent_of_bounded_difference {f g : ℝ → ℝ} {C : ℝ}
    (hg : Tendsto g atTop atTop) (hb : ∀ᶠ r in atTop, |f r - g r| ≤ C) : f ~[atTop] g := by
  change (f - g) =o[atTop] g
  apply isLittleO_iff.mpr
  intro ε hε
  filter_upwards [hb, hg.eventually (eventually_ge_atTop (max 0 (C / ε)))] with r hr hgr
  have hg0 : 0 ≤ g r := (le_max_left _ _).trans hgr
  have hCg : C ≤ g r * ε := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hgr)
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hg0, mul_comm ε] using hr.trans hCg

/-- Both extended-real extrema are unchanged by a real error tending to zero;
this includes infinite orders and makes no finiteness premise. -/
theorem ereal_extrema_eq_of_sub_tendsto_zero {α : Type*} {l : Filter α} [l.NeBot]
    {u v : α → ℝ} (h : Tendsto (fun x => u x - v x) l (𝓝 0)) :
    limsup (fun x => (u x : EReal)) l = limsup (fun x => (v x : EReal)) l ∧
    liminf (fun x => (u x : EReal)) l = liminf (fun x => (v x : EReal)) l := by
  let V : α → EReal := fun x => v x
  let D : α → EReal := fun x => (u x - v x : ℝ)
  have hD : Tendsto D l (𝓝 0) := by simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr h
  have hsup : limsup D l = 0 := hD.limsup_eq
  have hinf : liminf D l = 0 := hD.liminf_eq
  have he : (fun x => (u x : EReal)) = V + D := by
    ext x
    simp only [Pi.add_apply, V, D, ← EReal.coe_add]
    congr 1
    ring
  rw [he]
  change limsup (V + D) l = limsup V l ∧ liminf (V + D) l = liminf V l
  constructor
  · apply le_antisymm
    · have hh := EReal.limsup_add_le (u := V) (v := D) (f := l)
        (Or.inr (by rw [hsup]; exact EReal.zero_ne_top))
        (Or.inr (by rw [hsup]; exact EReal.zero_ne_bot))
      simpa only [hsup, add_zero] using hh
    · have hh := EReal.le_limsup_add (u := V) (v := D) (f := l)
      simpa only [hinf, add_zero] using hh
  · apply le_antisymm
    · have hh := EReal.liminf_add_le (u := D) (v := V) (f := l)
        (Or.inl (by rw [hsup]; exact EReal.zero_ne_bot))
        (Or.inl (by rw [hsup]; exact EReal.zero_ne_top))
      simpa only [hsup, zero_add, add_comm D V] using hh
    · have hh := EReal.le_liminf_add (u := V) (v := D) (f := l)
      simpa only [hinf, add_zero] using hh

/-- Classical logarithmic growth orders agree under asymptotic equivalence
when the comparison characteristic tends to infinity. -/
theorem growthOrders_eq_of_isEquivalent {f g : ℝ → ℝ}
    (he : f ~[atTop] g) (hg : Tendsto g atTop atTop) :
    upperGrowthOrder f = upperGrowthOrder g ∧ lowerGrowthOrder f = lowerGrowthOrder g := by
  have hgp : ∀ᶠ r in atTop, 0 < g r := hg.eventually (eventually_gt_atTop 0)
  have hgn : ∀ᶠ r in atTop, g r ≠ 0 := hgp.mono (fun _ hr => hr.ne')
  have hratio : Tendsto (fun r => f r / g r) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hgn).mp he
  have hlog : Tendsto (fun r => Real.log (f r / g r)) atTop (𝓝 0) := by
    simpa only [Real.log_one] using hratio.log one_ne_zero
  have hsmall : Tendsto (fun r => Real.log (f r / g r) / Real.log r) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, zero_mul] using
      hlog.mul (Real.tendsto_log_atTop.const_div_atTop (1 : ℝ))
  have heq : (fun r => Real.log (f r / g r) / Real.log r) =ᶠ[atTop]
      (fun r => Real.log (f r) / Real.log r - Real.log (g r) / Real.log r) := by
    filter_upwards [hgn, hratio.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))]
      with r hgr hfr
    have hfn : f r ≠ 0 := by intro hz; simp only [hz, zero_div, lt_self_iff_false] at hfr
    rw [Real.log_div hfn hgr, sub_div]
  exact ereal_extrema_eq_of_sub_tendsto_zero (hsmall.congr' heq)

end ModifiedCartan
#print axioms ModifiedCartan.isEquivalent_of_bounded_difference
#print axioms ModifiedCartan.growthOrders_eq_of_isEquivalent
