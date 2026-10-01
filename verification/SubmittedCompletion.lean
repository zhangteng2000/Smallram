import ModifiedCartan
import Lean.Util.CollectAxioms

/-! Completion checks for all 35 labelled results of paper/submitted.tex.
Historical verification/Completion.lean concerns an earlier manuscript.
This gate checks theorem declarations, exact principal target applications,
and prints the actual dependencies of every labelled result. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let results : Array (String × Name) := #[
    ("thm:A", ``ModifiedCartan.Paper.thm_A),
    ("thm:main", ``ModifiedCartan.Paper.thm_main),
    ("cor:zero-ratio", ``ModifiedCartan.Paper.cor_zero_ratio),
    ("lem:fundamental-operator", ``ModifiedCartan.Paper.lem_fundamental_operator),
    ("lem:canonical-gauge", ``ModifiedCartan.Paper.lem_canonical_gauge),
    ("lem:NH", ``ModifiedCartan.Paper.lem_NH),
    ("lem:logderivlimit", ``ModifiedCartan.Paper.lem_logderivlimit),
    ("lem:sum", ``ModifiedCartan.Paper.lem_sum),
    ("lem:subharmonic-compactness", ``ModifiedCartan.Paper.lem_subharmonic_compactness),
    ("lem:plucker-translation", ``ModifiedCartan.Paper.lem_plucker_translation),
    ("lem:KP-correspondence", ``ModifiedCartan.Paper.lem_KP_correspondence),
    ("lem:character-projection", ``ModifiedCartan.Paper.lem_character_projection),
    ("lem:universal-minors", ``ModifiedCartan.Paper.lem_universal_minors),
    ("prop:polynomialcoeff", ``ModifiedCartan.Paper.prop_polynomialcoeff),
    ("prop:initial-basis", ``ModifiedCartan.Paper.prop_initial_basis),
    ("prop:localcompact", ``ModifiedCartan.Paper.prop_localcompact),
    ("prop:representation", ``ModifiedCartan.Paper.prop_representation),
    ("lem:replacement", ``ModifiedCartan.Paper.lem_replacement),
    ("lem:peaks", ``ModifiedCartan.Paper.lem_peaks),
    ("prop:indices", ``ModifiedCartan.Paper.prop_indices),
    ("lem:power-bounds", ``ModifiedCartan.Paper.lem_power_bounds),
    ("lem:entire-majorant", ``ModifiedCartan.Paper.lem_entire_majorant),
    ("lem:Tonelli", ``ModifiedCartan.Paper.lem_Tonelli),
    ("cor:convolution", ``ModifiedCartan.Paper.cor_convolution),
    ("lem:envelope", ``ModifiedCartan.Paper.lem_envelope),
    ("lem:small-order-coordinates", ``ModifiedCartan.Paper.lem_small_order_coordinates),
    ("prop:small-order", ``ModifiedCartan.Paper.prop_small_order),
    ("prop:zero-order-ramification", ``ModifiedCartan.Paper.prop_zero_order_ramification),
    ("lem:basis-at-point", ``ModifiedCartan.Paper.lem_basis_at_point),
    ("lem:finite-gradient-convex", ``ModifiedCartan.Paper.lem_finite_gradient_convex),
    ("prop:homogeneity", ``ModifiedCartan.Paper.prop_homogeneity),
    ("prop:regular-variation", ``ModifiedCartan.Paper.prop_regular_variation),
    ("lem:integrable-system", ``ModifiedCartan.Paper.lem_integrable_system),
    ("prop:sharpness-orders", ``ModifiedCartan.Paper.prop_sharpness_orders),
    ("prop:sharpness-zero", ``ModifiedCartan.Paper.prop_sharpness_zero)]
  for (label, name) in results do
    let some info := env.checked.get.find? name
      | throwError "Missing submitted result {label}: {name}"
    unless info.isTheorem do
      throwError "Submitted result is not a theorem: {label}: {name}"
  logInfo m!"SUBMITTED COVERAGE PASSED: {results.size} labelled theorem declarations."

namespace ModifiedCartan
example (f : ℂ → ℂ) : ScalarTheoremATarget f := Paper.thm_A f
example {n : ℕ} (f : Curve n) : MainTheoremTarget f := Paper.thm_main f
example {n : ℕ} (f : Curve n) : SmallOrderTarget f := Paper.prop_small_order f
example {n : ℕ} (f : Curve n) : ZeroRatioTarget f := Paper.cor_zero_ratio f
example (n k q : ℕ) : SharpnessSystemExistenceTarget n k q := sharpnessSystem_exists n k q
example (n k q : ℕ) (g : Index n → ℂ → ℂ) : SharpnessOrdersTarget n k q g :=
  Paper.prop_sharpness_orders n k q g
example (n : ℕ) : SharpnessZeroTarget n := Paper.prop_sharpness_zero n
end ModifiedCartan

#check ModifiedCartan.Paper.thm_A
#print axioms ModifiedCartan.Paper.thm_A
#check ModifiedCartan.Paper.thm_main
#print axioms ModifiedCartan.Paper.thm_main
#check ModifiedCartan.Paper.cor_zero_ratio
#print axioms ModifiedCartan.Paper.cor_zero_ratio
#check ModifiedCartan.Paper.lem_fundamental_operator
#print axioms ModifiedCartan.Paper.lem_fundamental_operator
#check ModifiedCartan.Paper.lem_canonical_gauge
#print axioms ModifiedCartan.Paper.lem_canonical_gauge
#check ModifiedCartan.Paper.lem_NH
#print axioms ModifiedCartan.Paper.lem_NH
#check ModifiedCartan.Paper.lem_logderivlimit
#print axioms ModifiedCartan.Paper.lem_logderivlimit
#check ModifiedCartan.Paper.lem_sum
#print axioms ModifiedCartan.Paper.lem_sum
#check ModifiedCartan.Paper.lem_subharmonic_compactness
#print axioms ModifiedCartan.Paper.lem_subharmonic_compactness
#check ModifiedCartan.Paper.lem_plucker_translation
#print axioms ModifiedCartan.Paper.lem_plucker_translation
#check ModifiedCartan.Paper.lem_KP_correspondence
#print axioms ModifiedCartan.Paper.lem_KP_correspondence
#check ModifiedCartan.Paper.lem_character_projection
#print axioms ModifiedCartan.Paper.lem_character_projection
#check ModifiedCartan.Paper.lem_universal_minors
#print axioms ModifiedCartan.Paper.lem_universal_minors
#check ModifiedCartan.Paper.prop_polynomialcoeff
#print axioms ModifiedCartan.Paper.prop_polynomialcoeff
#check ModifiedCartan.Paper.prop_initial_basis
#print axioms ModifiedCartan.Paper.prop_initial_basis
#check ModifiedCartan.Paper.prop_localcompact
#print axioms ModifiedCartan.Paper.prop_localcompact
#check ModifiedCartan.Paper.prop_representation
#print axioms ModifiedCartan.Paper.prop_representation
#check ModifiedCartan.Paper.lem_replacement
#print axioms ModifiedCartan.Paper.lem_replacement
#check ModifiedCartan.Paper.lem_peaks
#print axioms ModifiedCartan.Paper.lem_peaks
#check ModifiedCartan.Paper.prop_indices
#print axioms ModifiedCartan.Paper.prop_indices
#check ModifiedCartan.Paper.lem_power_bounds
#print axioms ModifiedCartan.Paper.lem_power_bounds
#check ModifiedCartan.Paper.lem_entire_majorant
#print axioms ModifiedCartan.Paper.lem_entire_majorant
#check ModifiedCartan.Paper.lem_Tonelli
#print axioms ModifiedCartan.Paper.lem_Tonelli
#check ModifiedCartan.Paper.cor_convolution
#print axioms ModifiedCartan.Paper.cor_convolution
#check ModifiedCartan.Paper.lem_envelope
#print axioms ModifiedCartan.Paper.lem_envelope
#check ModifiedCartan.Paper.lem_small_order_coordinates
#print axioms ModifiedCartan.Paper.lem_small_order_coordinates
#check ModifiedCartan.Paper.prop_small_order
#print axioms ModifiedCartan.Paper.prop_small_order
#check ModifiedCartan.Paper.prop_zero_order_ramification
#print axioms ModifiedCartan.Paper.prop_zero_order_ramification
#check ModifiedCartan.Paper.lem_basis_at_point
#print axioms ModifiedCartan.Paper.lem_basis_at_point
#check ModifiedCartan.Paper.lem_finite_gradient_convex
#print axioms ModifiedCartan.Paper.lem_finite_gradient_convex
#check ModifiedCartan.Paper.prop_homogeneity
#print axioms ModifiedCartan.Paper.prop_homogeneity
#check ModifiedCartan.Paper.prop_regular_variation
#print axioms ModifiedCartan.Paper.prop_regular_variation
#check ModifiedCartan.Paper.lem_integrable_system
#print axioms ModifiedCartan.Paper.lem_integrable_system
#check ModifiedCartan.Paper.prop_sharpness_orders
#print axioms ModifiedCartan.Paper.prop_sharpness_orders
#check ModifiedCartan.Paper.prop_sharpness_zero
#print axioms ModifiedCartan.Paper.prop_sharpness_zero
#print axioms ModifiedCartan.sharpnessSystem_exists
#print axioms ModifiedCartan.Paper.thm_A_deficiency_sum
