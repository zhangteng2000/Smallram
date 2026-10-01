import ModifiedCartan.SmallOrderCoordinates
import ModifiedCartan.SystemDivisorMajorant
import ModifiedCartan.SystemPowerSequence
import ModifiedCartan.PolynomialNormalForm
import ModifiedCartan.AbsorptionConstants
import ModifiedCartan.CurveCoordinateNormalization
import ModifiedCartan.CharacteristicZero
import ModifiedCartan.Targets

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem zero_order_polynomial_of_eventual_ratio_bound {n : ℕ} (f : Curve n)
    (hn : 1 ≤ n) (hlin : f.linearlyNonDegenerate) (horder : order f = 0)
    (h0 : f.coord 0 0 ≠ 0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∀ᶠ r : ℝ in atTop, ramification f r ≤ c * characteristic f r) :
    f.HasPolynomialRepresentation := by
  have ho1 : order f < 1 := by rw [horder]; norm_num
  obtain ⟨G, hG, _, _, ⟨b, hW⟩, hcoords⟩ :=
    Paper.lem_small_order_coordinates f hlin ho1 h0
  obtain ⟨hjets, ho, ⟨CT, hT⟩, ⟨CN, hN⟩⟩ := hcoords b hW
  let y := normalizedCoordinates (gaugedCoordinates f G) b
  have hy : ∀ j, Differentiable ℂ (y j) :=
    normalizedCoordinates_differentiable (exponentialGauge f G hG).holomorphic b
  have hy0 : y 0 0 = 1 := by simpa using hjets 0 0
  obtain ⟨α, hα0, hα1, hαc⟩ := exists_envelope_exponent_for_ratio hc1
  have hα (j : Index n) : entireOrder (y j) < (α : EReal) := by
    have hz := ho j
    rw [horder] at hz
    exact hz.trans_lt (by exact_mod_cast hα0)
  obtain ⟨C, hcount⟩ := system_divisor_majorant_of_eventual_bound f hy hy0
    (norm_nonneg b) hc0 hT hN hc
  obtain ⟨r, hr, ht, K, _, hK⟩ := system_power_sequence_of_divisor_majorant hn hy hjets
    hα0 hα1 hα hc0 hαc hcount
  have hp (j : Index n) : ∃ p : Polynomial ℂ, ∀ z, y j z = p.eval z :=
    entire_polynomial_of_power_sequence (hy j) hr ht (hK.mono (fun ν hν => hν j))
  choose p hp using hp
  exact gaugedCurve_polynomialRepresentation_of_normalized_polynomials f G hG hW p hp

theorem eventual_ramification_bound_of_limsup_lt_one {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental)
    (hL : limsup (fun r => (ramification f r / characteristic f r : ℝ) : ℝ → EReal) atTop < 1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      ∀ᶠ r : ℝ in atTop, ramification f r ≤ c * characteristic f r := by
  let L := limsup (fun r => (ramification f r / characteristic f r : ℝ) : ℝ → EReal) atTop
  have hmax : max 0 L < 1 := max_lt (by norm_num) hL
  obtain ⟨c, hc, hc1⟩ := EReal.exists_between_coe_real hmax
  have hc0 : 0 < c := by exact_mod_cast (le_max_left 0 L).trans_lt hc
  have hc1' : c < 1 := by exact_mod_cast hc1
  have hLc : L < (c : EReal) := (le_max_right 0 L).trans_lt hc
  refine ⟨c, hc0, hc1', ?_⟩
  filter_upwards [eventually_lt_of_limsup_lt hLc, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hratio : ramification f r / characteristic f r < c := by exact_mod_cast hr
  exact ((div_lt_iff₀ (characteristic_pos_of_transcendental f htrans hr0)).mp hratio).le

namespace Paper

/-- LaTeX `prop:zero-order-ramification` and `eq:zero-order-ramification`.
The limsup is the literal extended-real limsup in the target registry. -/
theorem prop_zero_order_ramification {n : ℕ} (f : Curve n) : ZeroRatioTarget f := by
  intro hn htrans hlin horder
  by_contra hnot
  obtain ⟨c, hc0, hc1, hc⟩ := eventual_ramification_bound_of_limsup_lt_one f htrans (lt_of_not_ge hnot)
  obtain ⟨g, hg0, hT, hN, _, hlinG, htransG, _, _⟩ := exists_normalized_curve f
  have hratio : logGrowthRatio g = logGrowthRatio f := by
    funext r
    simp only [logGrowthRatio, hT]
  have hoG : order g = 0 := by simpa only [order, hratio] using horder
  have hcG : ∀ᶠ r : ℝ in atTop, ramification g r ≤ c * characteristic g r := by
    simpa only [hT, hN] using hc
  exact (htransG.mpr htrans) (zero_order_polynomial_of_eventual_ratio_bound g hn
    (hlinG.mpr hlin) hoG (hg0 0) hc0.le hc1 hcG)

/-- LaTeX `cor:zero-ratio`, proved by the quantitative order-zero proposition. -/
theorem cor_zero_ratio {n : ℕ} (f : Curve n) : ZeroRatioTarget f :=
  prop_zero_order_ramification f

end Paper
end ModifiedCartan
#print axioms ModifiedCartan.zero_order_polynomial_of_eventual_ratio_bound
#print axioms ModifiedCartan.Paper.prop_zero_order_ramification
#print axioms ModifiedCartan.Paper.cor_zero_ratio
