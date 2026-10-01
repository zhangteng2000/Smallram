import ModifiedCartan.MeasureDilationCompatibility
import ModifiedCartan.MeasureConvergenceLocality

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Local convergence in measure is preserved by a fixed nonzero real
dilation of the variable and a fixed complex multiplier. -/
theorem LocalMeasureConvergence.dilate_const_mul {U : Set ℂ} (hU : IsOpen U)
    {f : ℕ → ℂ → ℂ} {a : ℂ → ℂ} {R : ℝ} (hR : R ≠ 0) (c : ℂ)
    (hf : ∀ ν, Measurable (f ν)) (h : LocalMeasureConvergence U f a) :
    LocalMeasureConvergence ((fun z : ℂ => (R : ℂ) * z) ⁻¹' U)
      (fun ν z => c * f ν ((R : ℂ) * z)) (fun z => c * a ((R : ℂ) * z)) := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun ν =>
    (measurable_const.mul ((hf ν).comp (measurable_const.mul measurable_id))).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hm⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae hU
  refine ⟨ms, hms, ?_⟩
  have hg := (ae_restrict_iff' hU.measurableSet).mp hm
  have hp := (Measure.quasiMeasurePreserving_smul (volume : Measure ℂ) hR).ae hg
  simp only [Complex.real_smul] at hp
  filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem hK.measurableSet] with z hz hzK
  exact (hz (hKU hzK)).const_mul c

end ModifiedCartan
#print axioms ModifiedCartan.LocalMeasureConvergence.dilate_const_mul
