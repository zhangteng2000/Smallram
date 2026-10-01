import ModifiedCartan.LocalConvergence
import Mathlib.MeasureTheory.Function.Jacobian

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Compact-set L1 pullback bound obtained from the derivative of an actual
inverse map. This is the measure transport needed for the conformal change
in `prop:homogeneity`; the bound is valid for arbitrary representatives. -/
theorem eLpNorm_one_comp_le_of_inverse {E : Type*} [NormedAddCommGroup E]
    {K : Set ℂ} (hK : IsCompact K) {ψ φ : ℂ → ℂ} (hψ : ContinuousOn ψ K)
    (hinv : ∀ z ∈ K, φ (ψ z) = z) {D : ℂ → ℂ →L[ℝ] ℂ}
    (hD : ∀ z ∈ ψ '' K, HasFDerivWithinAt φ (D z) (ψ '' K) z)
    {M : ℝ} (hM : ∀ z ∈ ψ '' K, |(D z).det| ≤ M) (f : ℂ → E) :
    eLpNorm (fun z => f (ψ z)) 1 (volume.restrict K) ≤
      ENNReal.ofReal M * eLpNorm f 1 (volume.restrict (ψ '' K)) := by
  have hJ : IsCompact (ψ '' K) := hK.image_of_continuousOn hψ
  have hright : ∀ z ∈ ψ '' K, ψ (φ z) = z := by
    rintro z ⟨x, hx, rfl⟩
    rw [hinv x hx]
  have hinj : InjOn φ (ψ '' K) := by
    intro x hx y hy hxy
    rw [← hright x hx, ← hright y hy, hxy]
  have himage : φ '' (ψ '' K) = K := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [hinv z hz] using hz
    · intro hx
      exact ⟨ψ x, mem_image_of_mem ψ hx, hinv x hx⟩
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hJ.measurableSet hD hinj
    (fun z => ‖f (ψ z)‖ₑ)
  rw [himage] at he
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
  calc
    (∫⁻ z in K, ‖f (ψ z)‖ₑ) = ∫⁻ z in ψ '' K, ENNReal.ofReal |(D z).det| * ‖f z‖ₑ := by
      rw [he]
      apply setLIntegral_congr_fun hJ.measurableSet
      intro z hz
      change ENNReal.ofReal |(D z).det| * ‖f (ψ (φ z))‖ₑ = _
      rw [hright z hz]
    _ ≤ ∫⁻ z in ψ '' K, ENNReal.ofReal M * ‖f z‖ₑ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hJ.measurableSet] with z hz
      gcongr
      exact hM z hz
    _ = ENNReal.ofReal M * ∫⁻ z in ψ '' K, ‖f z‖ₑ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end ModifiedCartan
#print axioms ModifiedCartan.eLpNorm_one_comp_le_of_inverse

