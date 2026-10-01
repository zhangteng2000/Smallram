import ModifiedCartan.ClassicalWeakGradient
import ModifiedCartan.UniformLocalLp

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric InnerProductSpace

set_option autoImplicit false

namespace ModifiedCartan

/-! Convergence of classical harmonic gradients and addition of local Lp
limits, supporting `lem:logderivlimit`. -/

noncomputable def complexGradientCLM : (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)) -
    Complex.I • Complex.ofRealCLM.comp (ContinuousLinearMap.apply ℝ ℝ Complex.I)

theorem complexGradientCLM_apply (L : ℂ →L[ℝ] ℝ) :
    complexGradientCLM L = (L 1 : ℂ) - Complex.I * (L Complex.I : ℂ) := by
  simp [complexGradientCLM]

theorem classicalComplexGradient_tendstoUniformlyOn
    {Hn : ℕ → ℂ → ℝ} {H : ℂ → ℝ} {U : Set ℂ}
    (h : TendstoUniformlyOn (fun n => fderiv ℝ (Hn n)) (fderiv ℝ H) atTop U) :
    TendstoUniformlyOn (fun n => classicalComplexGradient (Hn n))
      (classicalComplexGradient H) atTop U := by
  simpa only [Function.comp_def, complexGradientCLM_apply, classicalComplexGradient] using!
    complexGradientCLM.uniformContinuous.comp_tendstoUniformlyOn h

theorem harmonicGradient_localLpConvergence
    {Hn : ℕ → ℂ → ℝ} {H : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hHn : ∀ n, HarmonicOnNhd (Hn n) U) (hH : HarmonicOnNhd H U)
    (h : TendstoUniformlyOn (fun n => fderiv ℝ (Hn n)) (fderiv ℝ H) atTop U) (p : ℝ≥0∞) :
    LocalLpConvergence p U (fun n => classicalComplexGradient (Hn n)) (classicalComplexGradient H) :=
  localLpConvergence_of_tendstoUniformlyOn p
    (fun n => continuousOn_classicalComplexGradient hU ((hHn n).contDiffOn.of_le (by norm_num)))
    (continuousOn_classicalComplexGradient hU (hH.contDiffOn.of_le (by norm_num)))
    (classicalComplexGradient_tendstoUniformlyOn h)

theorem LocalLpConvergence.add {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set ℂ} {f g : ℕ → ℂ → E} {f₀ g₀ : ℂ → E}
    (hf : LocalLpConvergence p U f f₀) (hg : LocalLpConvergence p U g g₀) :
    LocalLpConvergence p U (fun n => f n + g n) (f₀ + g₀) where
  source_mem K hK hKU n := (hf.source_mem K hK hKU n).add (hg.source_mem K hK hKU n)
  limit_mem K hK hKU := (hf.limit_mem K hK hKU).add (hg.limit_mem K hK hKU)
  tendsto K hK hKU := by
    have ht : Tendsto (fun n => eLpNorm (f n - f₀) p (volume.restrict K) +
        eLpNorm (g n - g₀) p (volume.restrict K)) atTop (𝓝 0) := by
      simpa only [add_zero] using (hf.tendsto K hK hKU).add (hg.tendsto K hK hKU)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro n
    have heq : (f n + g n) - (f₀ + g₀) = (f n - f₀) + (g n - g₀) := by abel
    dsimp only
    rw [heq]
    exact eLpNorm_add_le
      ((hf.source_mem K hK hKU n).sub (hf.limit_mem K hK hKU)).aestronglyMeasurable
      ((hg.source_mem K hK hKU n).sub (hg.limit_mem K hK hKU)).aestronglyMeasurable hp



end ModifiedCartan


