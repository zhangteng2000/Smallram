import ModifiedCartan.CurveOrderBasic
import ModifiedCartan.GaugedCoordinateBounds

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem gaugedCoordinates_entireOrder_le {n : ℕ} (f : Curve n)
    (horder : order f < 1) {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (h0 : f.coord 0 0 ≠ 0)
    (he : ∀ z, f.coord 0 z = genusZeroProduct (f.coord 0) z * Complex.exp (G z))
    (j : Index n) : entireOrder (gaugedCoordinates f G j) ≤ order f := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro γ hγ
  obtain ⟨β, hβ, hb⟩ := EReal.exists_between_coe_real (lt_min hγ horder)
  have hβ0 : 0 ≤ β := by
    have hh := (order_nonneg f).trans hβ.le
    exact_mod_cast hh
  have hβ1 : β < 1 := by exact_mod_cast (hb.trans_le (min_le_right _ _))
  have hβγ : (β : EReal) ≤ (γ : EReal) := (hb.trans_le (min_le_left _ _)).le
  obtain ⟨C, hC, hc⟩ := gaugedCoordinates_posLog_power_bound f hG h0 he hβ0 hβ1 hβ j
  exact (entireOrder_le_of_posLog_power_bound hβ0 hC hc).trans hβγ

/-- Step 1 of LaTeX `lem:small-order-coordinates`: one entire gauge with
all component orders at most the original curve order. Every auxiliary
count, product, and scalar growth bound is derived from the stated order. -/
theorem exists_small_order_entire_gauge {n : ℕ} (f : Curve n)
    (horder : order f < 1) (h0 : f.coord 0 0 ≠ 0) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ z, f.coord 0 z = genusZeroProduct (f.coord 0) z * Complex.exp (G z)) ∧
      ∀ j : Index n, entireOrder (gaugedCoordinates f G j) ≤ order f := by
  obtain ⟨β, hβ, hβ1⟩ := EReal.exists_between_coe_real horder
  have hβ0 : 0 ≤ β := by
    have hh := (order_nonneg f).trans hβ.le
    exact_mod_cast hh
  have hb1 : β < 1 := by exact_mod_cast hβ1
  have hs := coordinate_reciprocal_roots_summable f 0 h0 hβ0 hb1 hβ
  obtain ⟨G, hG, he⟩ := exists_genusZeroProduct_exp_factor (f.holomorphic 0) h0 hs
  exact ⟨G, hG, he, gaugedCoordinates_entireOrder_le f horder hG h0 he⟩

end ModifiedCartan
#print axioms ModifiedCartan.exists_small_order_entire_gauge
