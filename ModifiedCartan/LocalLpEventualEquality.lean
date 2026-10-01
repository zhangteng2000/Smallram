import ModifiedCartan.LocalConvergenceAlgebra

open scoped Topology ENNReal
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Eventual AE equality transfers a local Lp limit once membership of every
term of the new sequence is proved, including the exceptional initial terms. -/
theorem LocalLpConvergence.congr_eventually_ae {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {U : Set ℂ} {f g : ℕ → ℂ → E} {u : ℂ → E}
    (h : LocalLpConvergence p U f u)
    (hg : ∀ K, IsCompact K → K ⊆ U → ∀ ν, MemLp (g ν) p (volume.restrict K))
    (heq : ∀ᶠ ν in atTop, f ν =ᵐ[volume.restrict U] g ν) :
    LocalLpConvergence p U g u where
  source_mem := hg
  limit_mem := h.limit_mem
  tendsto K hK hKU := by
    apply (h.tendsto K hK hKU).congr'
    filter_upwards [heq] with ν hν
    apply eLpNorm_congr_ae
    filter_upwards [hν.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU))] with z hz
    simp only [Pi.sub_apply, hz]

end ModifiedCartan
#print axioms ModifiedCartan.LocalLpConvergence.congr_eventually_ae
