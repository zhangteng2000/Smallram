import Mathlib.MeasureTheory.Measure.Prod

open scoped ENNReal
open MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan.Paper

/-- LaTeX `lem:Tonelli`, including measurability of both iterated integrals.
The integral may equal infinity; no finiteness hypothesis is introduced. -/
theorem lem_Tonelli {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    {Φ : X × Y → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable (fun x => ∫⁻ y, Φ (x, y) ∂ν) ∧
      Measurable (fun y => ∫⁻ x, Φ (x, y) ∂μ) ∧
      (∫⁻ x, ∫⁻ y, Φ (x, y) ∂ν ∂μ) = (∫⁻ p, Φ p ∂μ.prod ν) ∧
      (∫⁻ p, Φ p ∂μ.prod ν) = (∫⁻ y, ∫⁻ x, Φ (x, y) ∂μ ∂ν) :=
  ⟨hΦ.lintegral_prod_right', hΦ.lintegral_prod_left',
    (lintegral_prod Φ hΦ.aemeasurable).symm, lintegral_prod_symm Φ hΦ.aemeasurable⟩

end ModifiedCartan.Paper
#print axioms ModifiedCartan.Paper.lem_Tonelli
