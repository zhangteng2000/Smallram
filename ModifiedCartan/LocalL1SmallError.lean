import ModifiedCartan.UniformLocalLp

open scoped Topology ENNReal
open Filter MeasureTheory Set
set_option autoImplicit false
namespace ModifiedCartan

/-- A uniformly vanishing AE error on the domain preserves local L1
convergence; measurability supplies the required source membership. -/
theorem LocalLpConvergence.of_ae_uniform_error {U : Set ℂ}
    {f g : ℕ → ℂ → ℝ} {v : ℂ → ℝ} {δ : ℕ → ℝ}
    (hg : LocalLpConvergence 1 U g v)
    (hf : ∀ K, IsCompact K → K ⊆ U → ∀ ν, AEStronglyMeasurable (f ν) (volume.restrict K))
    (hδ : Tendsto δ atTop (𝓝 0))
    (herr : ∀ ν, ∀ᵐ z ∂volume.restrict U, ‖f ν z - g ν z‖ ≤ δ ν) :
    LocalLpConvergence 1 U f v := by
  have herror {K : Set ℂ} (hKU : K ⊆ U) (ν : ℕ) :
      ∀ᵐ z ∂volume.restrict K, ‖(f ν - g ν) z‖ ≤ δ ν :=
    (herr ν).filter_mono (ae_mono (Measure.restrict_mono_set _ hKU))
  have hmem (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (ν : ℕ) :
      MemLp (f ν - g ν) 1 (volume.restrict K) := by
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    exact MemLp.of_bound ((hf K hK hKU ν).sub (hg.source_mem K hK hKU ν).aestronglyMeasurable)
      (δ ν) (herror hKU ν)
  have hfm (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (ν : ℕ) :
      MemLp (f ν) 1 (volume.restrict K) := by
    simpa only [sub_add_cancel] using (hmem K hK hKU ν).add (hg.source_mem K hK hKU ν)
  refine ⟨hfm, hg.limit_mem, ?_⟩
  intro K hK hKU
  have hδc : Tendsto (fun ν => ENNReal.ofReal (δ ν)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hδ
  have he : Tendsto (fun ν => volume K * ENNReal.ofReal (δ ν)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hδc
      (Or.inr hK.measure_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ volume K ≠ ⊤)
  have hlim := he.add (hg.tendsto K hK hKU)
  simp only [zero_add] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro ν
  have hdecomp : f ν - v = (f ν - g ν) + (g ν - v) := by abel
  dsimp only
  rw [hdecomp]
  apply (eLpNorm_add_le (hmem K hK hKU ν).aestronglyMeasurable
    ((hg.source_mem K hK hKU ν).sub (hg.limit_mem K hK hKU)).aestronglyMeasurable le_rfl).trans
  refine add_le_add ?_ le_rfl
  simpa only [ENNReal.toReal_one, inv_one, ENNReal.rpow_one,
    Measure.restrict_apply_univ, mul_comm] using eLpNorm_le_of_ae_bound (p := (1 : ℝ≥0∞)) (herror hKU ν)

end ModifiedCartan
#print axioms ModifiedCartan.LocalLpConvergence.of_ae_uniform_error
