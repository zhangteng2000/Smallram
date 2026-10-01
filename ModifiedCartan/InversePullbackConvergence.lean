import ModifiedCartan.InversePullbackBound
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem integrableOn_comp_of_inverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set ℂ} (hK : IsCompact K) {ψ φ : ℂ → ℂ} (hψ : ContinuousOn ψ K)
    (hinv : ∀ z ∈ K, φ (ψ z) = z) {D : ℂ → ℂ →L[ℝ] ℂ}
    (hD : ∀ z ∈ ψ '' K, HasFDerivWithinAt φ (D z) (ψ '' K) z)
    (hDc : ContinuousOn (fun z => |(D z).det|) (ψ '' K)) {f : ℂ → E}
    (hf : IntegrableOn f (ψ '' K)) : IntegrableOn (fun z => f (ψ z)) K := by
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
  have hi : IntegrableOn (fun z => |(D z).det| • f (ψ (φ z))) (ψ '' K) := by
    apply (hf.continuousOn_smul hDc hJ).congr
    filter_upwards [ae_restrict_mem hJ.measurableSet] with z hz
    rw [hright z hz]
  have ht := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hJ.measurableSet hD hinj (fun z => f (ψ z))).mpr hi
  rwa [himage] at ht

/-- Local L1 convergence is transported through an actual differentiable
inverse with continuous Jacobian. Compact bounds are proved from continuity. -/
theorem LocalLpConvergence.comp_inverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U G : Set ℂ} {f : ℕ → ℂ → E} {u : ℂ → E} (h : LocalLpConvergence 1 U f u)
    {ψ φ : ℂ → ℂ} (hψ : ContinuousOn ψ G) (hψU : MapsTo ψ G U)
    (hinv : ∀ z ∈ G, φ (ψ z) = z) {D : ℂ → ℂ →L[ℝ] ℂ}
    (hD : ∀ z ∈ ψ '' G, HasFDerivWithinAt φ (D z) (ψ '' G) z)
    (hDc : ContinuousOn (fun z => |(D z).det|) (ψ '' G)) :
    LocalLpConvergence 1 G (fun ν z => f ν (ψ z)) (fun z => u (ψ z)) := by
  have hJ (K : Set ℂ) (hK : IsCompact K) (hKG : K ⊆ G) : IsCompact (ψ '' K) :=
    hK.image_of_continuousOn (hψ.mono hKG)
  have hJU (K : Set ℂ) (hKG : K ⊆ G) : ψ '' K ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact hψU (hKG hx)
  have hder (K : Set ℂ) (hKG : K ⊆ G) :
      ∀ z ∈ ψ '' K, HasFDerivWithinAt φ (D z) (ψ '' K) z :=
    fun z hz => (hD z ((image_mono hKG) hz)).mono (image_mono hKG)
  have hci (K : Set ℂ) (hK : IsCompact K) (hKG : K ⊆ G) {v : ℂ → E}
      (hv : IntegrableOn v (ψ '' K)) : IntegrableOn (fun z => v (ψ z)) K :=
    integrableOn_comp_of_inverse hK (hψ.mono hKG) (fun z hz => hinv z (hKG hz))
      (hder K hKG) (hDc.mono (image_mono hKG)) hv
  refine ⟨?_, ?_, ?_⟩
  · intro K hK hKG ν
    exact memLp_one_iff_integrable.mpr (hci K hK hKG
      (memLp_one_iff_integrable.mp (h.source_mem _ (hJ K hK hKG) (hJU K hKG) ν)))
  · intro K hK hKG
    exact memLp_one_iff_integrable.mpr (hci K hK hKG
      (memLp_one_iff_integrable.mp (h.limit_mem _ (hJ K hK hKG) (hJU K hKG))))
  · intro K hK hKG
    obtain ⟨M, hM⟩ := (hJ K hK hKG).exists_bound_of_continuousOn (hDc.mono (image_mono hKG))
    have hbound : ∀ z ∈ ψ '' K, |(D z).det| ≤ M := by
      intro z hz
      simpa only [Real.norm_eq_abs, abs_abs] using hM z hz
    have ht : Tendsto (fun ν => ENNReal.ofReal M * eLpNorm (f ν - u) 1 (volume.restrict (ψ '' K)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul (h.tendsto _ (hJ K hK hKG) (hJU K hKG))
        (Or.inr ENNReal.ofReal_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal M ≠ ⊤)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro ν
    exact eLpNorm_one_comp_le_of_inverse hK (hψ.mono hKG) (fun z hz => hinv z (hKG hz))
      (hder K hKG) hbound (f ν - u)

end ModifiedCartan
#print axioms ModifiedCartan.LocalLpConvergence.comp_inverse

