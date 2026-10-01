import ModifiedCartan.UniformLocalLp

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem dist_toL1_eq_integral_norm {μ : Measure ℂ} {f g : ℂ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ z, ‖f z - g z‖ ∂μ := by
  rw [Lp.dist_edist, Integrable.edist_toL1_toL1]
  simp_rw [edist_dist, dist_eq_norm]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun z => norm_nonneg _))
    (hf.sub hg).aestronglyMeasurable.norm).symm

theorem uniformCauchySeqOn_toL1 {K : Set ℂ} (hK : IsCompact K) {f : ℕ → ℂ → ℝ}
    (hf : ∀ n, IntegrableOn (f n) K volume) (h : UniformCauchySeqOn f atTop K) :
    CauchySeq (fun n => (hf n).toL1 (μ := volume.restrict K) (f n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ := ε / (volume.real K + 1)
  have hden : 0 < volume.real K + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp h δ hδ
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_toL1_eq_integral_norm (hf m) (hf n)]
  have hbound : ∀ᵐ z ∂volume.restrict K, ‖f m z - f n z‖ ≤ δ := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact (by simpa only [dist_eq_norm] using (hN m hm n hn z hz).le)
  have hint := norm_setIntegral_le_of_norm_le_const_ae (f := fun z => ‖f m z - f n z‖) hK.measure_lt_top
    (hbound.mono (fun z hz => by simpa only [norm_norm] using hz))
  have hnonneg : 0 ≤ ∫ z in K, ‖f m z - f n z‖ :=
    integral_nonneg (fun z => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hint
  have heq : δ * (volume.real K + 1) = ε := div_mul_cancel₀ _ hden.ne'
  exact hint.trans_lt (by nlinarith)


end ModifiedCartan
