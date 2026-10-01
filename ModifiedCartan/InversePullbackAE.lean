import ModifiedCartan.LocalConvergence
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- A differentiable actual inverse transports null exceptional sets. -/
theorem ae_comp_of_differentiable_inverse {U G : Set ℂ}
    (hU : MeasurableSet U) (hG : MeasurableSet G) {ψ φ : ℂ → ℂ}
    (hψU : MapsTo ψ G U) (hinv : ∀ z ∈ G, φ (ψ z) = z)
    (hφ : DifferentiableOn ℝ φ (ψ '' G)) {P : ℂ → Prop}
    (hP : ∀ᵐ z ∂volume.restrict U, P z) :
    ∀ᵐ z ∂volume.restrict G, P (ψ z) := by
  classical
  have hnull : volume {z | z ∈ U ∧ ¬ P z} = 0 := by
    simpa only [_root_.not_imp] using ae_iff.mp ((ae_restrict_iff' hU).mp hP)
  have hb : volume {z | z ∈ ψ '' G ∧ ¬ P z} = 0 := by
    apply measure_mono_null _ hnull
    rintro z ⟨⟨x, hx, rfl⟩, hz⟩
    exact ⟨hψU hx, hz⟩
  have hi : volume (φ '' {z | z ∈ ψ '' G ∧ ¬ P z}) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hφ.mono (fun _ hz => hz.1)) hb
  apply (ae_restrict_iff' hG).mpr
  apply ae_iff.mpr
  apply measure_mono_null _ hi
  intro z hz
  simp only [mem_ofPred_eq, _root_.not_imp] at hz
  exact ⟨ψ z, ⟨mem_image_of_mem ψ hz.1, hz.2⟩, hinv z hz.1⟩

/-- A continuous multiplier preserves actual local L1 convergence. -/
theorem LocalLpConvergence.continuousOn_mul {U : Set ℂ}
    {f : ℕ → ℂ → ℂ} {u m : ℂ → ℂ} (h : LocalLpConvergence 1 U f u)
    (hm : ContinuousOn m U) :
    LocalLpConvergence 1 U (fun ν z => m z * f ν z) (fun z => m z * u z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K hK hKU ν
    have hi : IntegrableOn (f ν) K := memLp_one_iff_integrable.mp (h.source_mem K hK hKU ν)
    exact memLp_one_iff_integrable.mpr (hi.continuousOn_mul (hm.mono hKU) hK)
  · intro K hK hKU
    have hi : IntegrableOn u K := memLp_one_iff_integrable.mp (h.limit_mem K hK hKU)
    exact memLp_one_iff_integrable.mpr (hi.continuousOn_mul (hm.mono hKU) hK)
  · intro K hK hKU
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hm.mono hKU)
    have ht : Tendsto (fun ν => ENNReal.ofReal M * eLpNorm (f ν - u) 1 (volume.restrict K))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul (h.tendsto K hK hKU)
        (Or.inr ENNReal.ofReal_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal M ≠ ⊤)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro ν
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    simp only [Pi.sub_apply, ← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM z hz) (norm_nonneg _)

end ModifiedCartan
#print axioms ModifiedCartan.ae_comp_of_differentiable_inverse
#print axioms ModifiedCartan.LocalLpConvergence.continuousOn_mul



