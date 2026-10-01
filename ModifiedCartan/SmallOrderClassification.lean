import ModifiedCartan.SmallOrderCoordinates
import ModifiedCartan.SystemDivisorMajorant
import ModifiedCartan.SystemPowerSequence
import ModifiedCartan.NormalizedMonomials
import ModifiedCartan.PolynomialNormalForm
import ModifiedCartan.AbsorptionConstants
import ModifiedCartan.CurveCoordinateNormalization
import ModifiedCartan.Targets

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem small_order_normal_form_of_coordinate_nonzero {n : ℕ} (f : Curve n)
    (hn : 1 ≤ n) (hlin : f.linearlyNonDegenerate) (hsmall : SmallRamification f)
    (horder : order f < 1) (h0 : f.coord 0 0 ≠ 0) :
    Nonempty (FewInflection.RationalNormalForm n f) := by
  obtain ⟨G, hG, _, _, ⟨b, hW⟩, hcoords⟩ :=
    Paper.lem_small_order_coordinates f hlin horder h0
  obtain ⟨hjets, ho, ⟨CT, hT⟩, ⟨CN, hN⟩⟩ := hcoords b hW
  let y := normalizedCoordinates (gaugedCoordinates f G) b
  have hy : ∀ j, Differentiable ℂ (y j) :=
    normalizedCoordinates_differentiable (exponentialGauge f G hG).holomorphic b
  have hy0 : y 0 0 = 1 := by simpa using hjets 0 0
  have hyorder (j : Index n) : entireOrder (y j) < 1 := (ho j).trans_lt horder
  obtain ⟨α, hα0, hα1, hα⟩ := finite_entireOrder_exists_exponent_lt_one hyorder
  have hI : 0 < envelopeConstant α := zero_lt_one.trans_le (one_le_envelopeConstant hα0.le hα1)
  obtain ⟨ε, hε0, hεI, hγ⟩ := exists_small_absorption_coefficient n hI
  obtain ⟨C, hc⟩ := small_order_divisor_majorant hsmall hy hy0 (norm_nonneg b) hT hN hε0
  obtain ⟨r, hr, ht, K, _, hK⟩ := system_power_sequence_of_divisor_majorant hn hy hjets
    hα0 hα1 hα hε0.le hεI hc
  have hmon := normalized_system_eq_monomials_of_power_sequence hy hjets hr ht hK hγ
  exact gaugedCurve_rationalNormalForm_of_normalized_monomials f hlin G hG hW hmon

namespace Paper

/-- LaTeX `prop:small-order`, with the exact submitted hypotheses and
the projective rational normal form `eq:rationalnormal`. All analytic
majorants, absorption, and polynomiality have been proved above. -/
theorem prop_small_order {n : ℕ} (f : Curve n) : SmallOrderTarget f := by
  intro hn hlin hsmall horder
  obtain ⟨A, hA, hAnorm, hA0⟩ :=
    exists_euclidean_matrix_nonzero_coordinates (f.vector 0) (f.vector_ne_zero 0)
  have hT := characteristic_matrixGauge_of_euclidean_isometry f A hA hAnorm
  have hN := FewInflection.Curve.matrixGauge_ramification_eq f A hA
  have hlinG := (FewInflection.Curve.matrixGauge_linearlyNonDegenerate_iff f A hA).mp hlin
  have hsmallG : SmallRamification (f.matrixGauge A hA) := by
    simpa only [SmallRamification, hT, hN] using hsmall
  have hratio : logGrowthRatio (f.matrixGauge A hA) = logGrowthRatio f := by
    funext r
    simp only [logGrowthRatio, hT]
  have horderG : order (f.matrixGauge A hA) < 1 := by
    simpa only [order, hratio] using horder
  have hzeroG : (f.matrixGauge A hA).coord 0 0 ≠ 0 := hA0 0
  obtain ⟨hform⟩ := small_order_normal_form_of_coordinate_nonzero (f.matrixGauge A hA)
    hn hlinG hsmallG horderG hzeroG
  exact rationalNormalForm_of_matrixGauge f hlin A hA hform

end Paper
end ModifiedCartan
#print axioms ModifiedCartan.Paper.prop_small_order
