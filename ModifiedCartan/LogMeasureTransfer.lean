import ModifiedCartan.ExponentialLogComparison
import ModifiedCartan.LocalMeasureUniqueness

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Exponential approximation transfers the actual normalized logarithm
limit in measure whenever that limit is nonnegative AE. -/
theorem localMeasure_log_transfer_of_exponential_close {U : Set ℂ} (hU : IsOpen U)
    {x y : ℕ → ℂ → ℝ} {s : ℕ → ℝ} {u : ℂ → ℝ} {A C : ℝ}
    (hA : 0 < A) (hs : Tendsto s atTop atTop)
    (hxpos : ∀ ν z, z ∈ U → 0 < x ν z)
    (hymeas : ∀ K, IsCompact K → K ⊆ U → ∀ ν, AEStronglyMeasurable (y ν) (volume.restrict K))
    (hxlim : LocalMeasureConvergence U (fun ν z => Real.log (x ν z) / s ν) u)
    (hu : ∀ᵐ z ∂volume.restrict U, 0 ≤ u z)
    (hclose : ∀ᶠ ν in atTop, ∀ z ∈ U, |y ν z - x ν z| ≤ C * Real.exp (-A * s ν)) :
    LocalMeasureConvergence U (fun ν z => Real.log (y ν z) / s ν) u := by
  intro K hK hKU
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun ν => by
    simpa only [div_eq_mul_inv] using
      ((hymeas K hK hKU ν).aemeasurable.log.aestronglyMeasurable).mul_const (s ν)⁻¹)).mpr
  intro ns hns
  obtain ⟨ms, hms, hm⟩ := (hxlim.comp hns.tendsto_atTop).exists_seq_tendsto_ae hU
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hm.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)),
    hu.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)),
    ae_restrict_mem hK.measurableSet] with z hz hzu hzK
  apply normalized_log_tendsto_of_exponential_close hA
    (hs.comp (hns.tendsto_atTop.comp hms.tendsto_atTop))
    (Eventually.of_forall (fun ν => hxpos (ns (ms ν)) z (hKU hzK))) hz hzu
  filter_upwards [(hns.tendsto_atTop.comp hms.tendsto_atTop).eventually hclose] with ν hν
  exact hν z (hKU hzK)

end ModifiedCartan
#print axioms ModifiedCartan.localMeasure_log_transfer_of_exponential_close
