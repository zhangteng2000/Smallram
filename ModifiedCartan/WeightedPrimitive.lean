import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- A derivative negligible relative to an increasing exponential-type weight
has a primitive negligible relative to the same weight. The proof uses a
scalar derivative fence, so it applies equally to complex-valued primitives. -/
theorem norm_primitive_div_weight_tendsto_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f f' : ℝ → V} {w w' : ℝ → ℝ} {T a : ℝ}
    (ha : 0 < a) (hpos : ∀ t, T ≤ t → 0 < w t)
    (hw : Tendsto w atTop atTop)
    (hdw : ∀ t, T ≤ t → HasDerivAt w (w' t) t)
    (hw' : ∀ t, T ≤ t → a * w t ≤ w' t)
    (hdf : ∀ t, T ≤ t → HasDerivAt f (f' t) t)
    (hf' : Tendsto (fun t => ‖f' t‖ / w t) atTop (𝓝 0)) :
    Tendsto (fun t => ‖f t‖ / w t) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    filter_upwards [eventually_ge_atTop T] with t ht
    exact hl.trans_le (div_nonneg (norm_nonneg _) (hpos t ht).le)
  · intro ε hε
    have hea : 0 < (ε / 2) * a := mul_pos (half_pos hε) ha
    obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp (hf'.eventually_lt_const hea)
    let S := max T S₀
    have hST : T ≤ S := le_max_left _ _
    have hSb (t : ℝ) (ht : S ≤ t) : ‖f' t‖ ≤ (ε / 2) * (a * w t) := by
      have hp := hpos t (hST.trans ht)
      have hh := hS₀ t ((le_max_right T S₀).trans ht)
      have hh' := (div_lt_iff₀ hp).mp hh
      nlinarith
    have hfence (t : ℝ) (ht : S ≤ t) :
        ‖f t‖ ≤ ‖f S‖ + (ε / 2) * w t := by
      have hbound (u : ℝ) (hu : u ∈ Ico S t) : ‖f' u‖ ≤ (ε / 2) * w' u :=
        (hSb u hu.1).trans (mul_le_mul_of_nonneg_left (hw' u (hST.trans hu.1)) (half_pos hε).le)
      exact image_norm_le_of_norm_deriv_right_le_deriv_boundary'
        (fun u hu => (hdf u (hST.trans hu.1)).continuousAt.continuousWithinAt)
        (fun u hu => (hdf u (hST.trans hu.1)).hasDerivWithinAt)
        (show ‖f S‖ ≤ ‖f S‖ + ε / 2 * w S from
          le_add_of_nonneg_right (mul_nonneg (half_pos hε).le (hpos S hST).le))
        (fun u hu => ((hdw u (hST.trans hu.1)).const_mul (ε / 2)).const_add
          ‖f S‖ |>.continuousAt.continuousWithinAt)
        (fun u hu => ((hdw u (hST.trans hu.1)).const_mul (ε / 2)).const_add
          ‖f S‖ |>.hasDerivWithinAt)
        hbound ⟨ht, le_rfl⟩
    have hc : Tendsto (fun t => ‖f S‖ / w t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hw
    filter_upwards [eventually_ge_atTop S, hc.eventually_lt_const (half_pos hε)] with t ht hct
    have hp := hpos t (hST.trans ht)
    calc
      ‖f t‖ / w t ≤ (‖f S‖ + (ε / 2) * w t) / w t :=
        div_le_div_of_nonneg_right (hfence t ht) hp.le
      _ = ‖f S‖ / w t + ε / 2 := by field_simp
      _ < ε := by linarith

end ModifiedCartan
#print axioms ModifiedCartan.norm_primitive_div_weight_tendsto_zero

