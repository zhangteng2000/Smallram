import ModifiedCartan.CharacteristicRatioLimit
import ModifiedCartan.MonotoneCompactUniformity

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `prop:regular-variation`: the characteristic ratios converge to c^rho,
locally uniformly for positive multipliers, for the original curve. -/
theorem Paper.prop_regular_variation {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ}
    (hρ : FewInflection.AdmissibleOrder n ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal)) :
    FewInflection.RegularlyVarying (characteristic f) ρ := by
  have hρpos := FewInflection.admissibleOrder_pos hρ
  intro K hK hKpos ε hε
  have hm : ∀ᶠ r : ℝ in atTop,
      MonotoneOn (fun c => characteristic f (c * r) / characteristic f r) (Ioi 0) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    intro a ha b hb hab
    exact div_le_div_of_nonneg_right
      (characteristic_monotoneOn f (mul_pos ha hr) (mul_pos hb hr)
        (mul_le_mul_of_nonneg_right hab hr.le))
      (characteristic_pos_of_transcendental f htrans hr).le
  have he := eventually_uniform_of_monotone_pointwise hm
    (Real.continuous_rpow_const hρpos.le).continuousOn
    (fun c hc => characteristic_ratio_tendsto f htrans hlin hsmall hρpos hl hu hc)
    hK hKpos hε
  obtain ⟨R, hR⟩ := eventually_atTop.mp he
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro r hr c hc
  exact hR r ((le_max_left _ _).trans hr.le) c hc

end ModifiedCartan
#print axioms ModifiedCartan.Paper.prop_regular_variation
