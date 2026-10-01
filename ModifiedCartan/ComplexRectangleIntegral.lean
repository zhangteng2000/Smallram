import ModifiedCartan.LocalConvergenceAlgebra
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Compact Cartesian rectangle in the complex plane, used for the actual
horizontal/vertical good paths in LaTeX `thm:A` (b). -/
def complexClosedRectangle (a b c d : ℝ) : Set ℂ :=
  Complex.reProdIm (Icc a b) (Icc c d)

theorem complexClosedRectangle_isCompact (a b c d : ℝ) :
    IsCompact (complexClosedRectangle a b c d) := isCompact_Icc.reProdIm isCompact_Icc

theorem complexClosedRectangle_preimage (a b c d : ℝ) :
    Complex.measurableEquivRealProd.symm ⁻¹' complexClosedRectangle a b c d =
      Icc a b ×ˢ Icc c d := rfl

/-- Fubini coordinates preserve the actual planar restricted integral. -/
theorem integral_complexClosedRectangle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℂ → E) (a b c d : ℝ) :
    (∫ v : ℝ × ℝ, F (⟨v.1, v.2⟩ : ℂ)
      ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) =
      ∫ z in complexClosedRectangle a b c d, F z := by
  have hh := Complex.volume_preserving_equiv_real_prod.symm.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding F (complexClosedRectangle a b c d)
  rw [complexClosedRectangle_preimage, Measure.volume_eq_prod, ← Measure.prod_restrict] at hh
  exact hh

theorem integrable_complexClosedRectangle_iff {E : Type*} [NormedAddCommGroup E]
    {F : ℂ → E} {a b c d : ℝ} :
    Integrable (fun v : ℝ × ℝ => F (⟨v.1, v.2⟩ : ℂ))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) ↔
      IntegrableOn F (complexClosedRectangle a b c d) := by
  have hh := Complex.volume_preserving_equiv_real_prod.symm.integrableOn_comp_preimage
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    (f := F) (s := complexClosedRectangle a b c d)
  rw [complexClosedRectangle_preimage] at hh
  simp only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hh
  exact hh

/-- Both membership and convergence of the line error integrals follow from
literal local L1 convergence; no rectangle convergence is postulated. -/
theorem LocalLpConvergence.rectangle_integral_norm_sub
    {E : Type*} [NormedAddCommGroup E] {U : Set ℂ}
    {F : ℕ → ℂ → E} {u : ℂ → E} (h : LocalLpConvergence 1 U F u)
    {a b c d : ℝ} (hK : complexClosedRectangle a b c d ⊆ U) :
    (∀ n, Integrable (fun v : ℝ × ℝ => ‖F n (⟨v.1, v.2⟩ : ℂ) - u (⟨v.1, v.2⟩ : ℂ)‖)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) ∧
    Tendsto (fun n => ∫ v : ℝ × ℝ, ‖F n (⟨v.1, v.2⟩ : ℂ) - u (⟨v.1, v.2⟩ : ℂ)‖
      ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) atTop (𝓝 0) := by
  have hcompact := complexClosedRectangle_isCompact a b c d
  constructor
  · intro n
    apply (integrable_complexClosedRectangle_iff (F := fun z => ‖F n z - u z‖)
      (a := a) (b := b) (c := c) (d := d)).mpr
    exact (memLp_one_iff_integrable.mp
      ((h.source_mem _ hcompact hK n).sub (h.limit_mem _ hcompact hK))).norm
  · have he (n : ℕ) := integral_complexClosedRectangle (fun z => ‖F n z - u z‖) a b c d
    have ht := h.integral_norm_sub_tendsto_zero hcompact hK
    exact ht.congr (fun n => (he n).symm)

end ModifiedCartan
#print axioms ModifiedCartan.integral_complexClosedRectangle
#print axioms ModifiedCartan.LocalLpConvergence.rectangle_integral_norm_sub

