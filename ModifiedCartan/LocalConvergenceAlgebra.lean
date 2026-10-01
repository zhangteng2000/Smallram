import ModifiedCartan.LocalConvergence

open scoped Topology ENNReal
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

/-! Algebraic and measure-theoretic closure properties of local convergence
used in `lem:logderivlimit`: subsequences, differences, AE representatives,
and the real integral norm form of local L1 convergence. -/

theorem LocalLpConvergence.comp_strictMono {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {U : Set ℂ} {f : ℕ → ℂ → E} {g : ℂ → E}
    (h : LocalLpConvergence p U f g) {ns : ℕ → ℕ} (hns : StrictMono ns) :
    LocalLpConvergence p U (fun n => f (ns n)) g where
  source_mem K hK hKU n := h.source_mem K hK hKU (ns n)
  limit_mem := h.limit_mem
  tendsto K hK hKU := (h.tendsto K hK hKU).comp hns.tendsto_atTop

theorem LocalLpConvergence.sub {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set ℂ} {f g : ℕ → ℂ → E} {f₀ g₀ : ℂ → E}
    (hf : LocalLpConvergence p U f f₀) (hg : LocalLpConvergence p U g g₀) :
    LocalLpConvergence p U (fun n => f n - g n) (f₀ - g₀) where
  source_mem K hK hKU n := (hf.source_mem K hK hKU n).sub (hg.source_mem K hK hKU n)
  limit_mem K hK hKU := (hf.limit_mem K hK hKU).sub (hg.limit_mem K hK hKU)
  tendsto K hK hKU := by
    have ht : Tendsto (fun n => eLpNorm (f n - f₀) p (volume.restrict K) +
        eLpNorm (g n - g₀) p (volume.restrict K)) atTop (𝓝 0) := by
      simpa only [add_zero] using (hf.tendsto K hK hKU).add (hg.tendsto K hK hKU)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro n
    have heq : (f n - g n) - (f₀ - g₀) = (f n - f₀) - (g n - g₀) := by abel
    dsimp only
    rw [heq]
    exact eLpNorm_sub_le
      ((hf.source_mem K hK hKU n).sub (hf.limit_mem K hK hKU)).aestronglyMeasurable
      ((hg.source_mem K hK hKU n).sub (hg.limit_mem K hK hKU)).aestronglyMeasurable hp

theorem LocalLpConvergence.congr_ae {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {U : Set ℂ} {f g : ℕ → ℂ → E} {f₀ g₀ : ℂ → E}
    (hf : LocalLpConvergence p U f f₀)
    (heq : ∀ n, f n =ᵐ[volume.restrict U] g n) (heq₀ : f₀ =ᵐ[volume.restrict U] g₀) :
    LocalLpConvergence p U g g₀ where
  source_mem K hK hKU n := (memLp_congr_ae
    ((heq n).filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)))).mp
      (hf.source_mem K hK hKU n)
  limit_mem K hK hKU := (memLp_congr_ae
    (heq₀.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)))).mp
      (hf.limit_mem K hK hKU)
  tendsto K hK hKU := by
    have hn (n : ℕ) : eLpNorm (g n - g₀) p (volume.restrict K) =
        eLpNorm (f n - f₀) p (volume.restrict K) := by
      apply eLpNorm_congr_ae
      filter_upwards [(heq n).filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)),
        heq₀.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU))] with z hz hz₀
      simp only [Pi.sub_apply, hz, hz₀]
    simpa only [hn] using hf.tendsto K hK hKU

theorem LocalLpConvergence.integral_norm_sub_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {U K : Set ℂ} {f : ℕ → ℂ → E} {g : ℂ → E}
    (h : LocalLpConvergence 1 U f g) (hK : IsCompact K) (hKU : K ⊆ U) :
    Tendsto (fun n => ∫ z in K, ‖f n z - g z‖) atTop (𝓝 0) := by
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp (h.tendsto K hK hKU)
  have heq (n : ℕ) : (eLpNorm (f n - g) 1 (volume.restrict K)).toReal =
      ∫ z in K, ‖f n z - g z‖ := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm]
    · rfl
    · exact ((h.source_mem K hK hKU n).sub (h.limit_mem K hK hKU)).aestronglyMeasurable
  simpa only [Function.comp_def, heq, ENNReal.toReal_zero] using ht


end ModifiedCartan
