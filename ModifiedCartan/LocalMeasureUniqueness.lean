import ModifiedCartan.LocalSubsequence
import ModifiedCartan.MeasureLimitTransfer

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem LocalMeasureConvergence.ae_unique {E : Type*} [EMetricSpace E]
    {U : Set ℂ} (hU : IsOpen U) {f : ℕ → ℂ → E} {u v : ℂ → E}
    (hu : LocalMeasureConvergence U f u) (hv : LocalMeasureConvergence U f v) :
    u =ᵐ[volume.restrict U] v := by
  obtain ⟨ns, hns, hnu⟩ := hu.exists_seq_tendsto_ae hU
  obtain ⟨ms, hms, hmv⟩ := (hv.comp hns.tendsto_atTop).exists_seq_tendsto_ae hU
  filter_upwards [hnu, hmv] with z hzu hzv
  exact tendsto_nhds_unique (hzu.comp hms.tendsto_atTop) hzv

theorem LocalMeasureConvergence.congr_limit_ae {E : Type*} [PseudoEMetricSpace E]
    {U : Set ℂ} {f : ℕ → ℂ → E} {u v : ℂ → E}
    (hu : LocalMeasureConvergence U f u) (huv : u =ᵐ[volume.restrict U] v) :
    LocalMeasureConvergence U f v := by
  intro K hK hKU
  exact (hu K hK hKU).congr' (Eventually.of_forall (fun _ => EventuallyEq.rfl))
    (huv.filter_mono (ae_mono (Measure.restrict_mono_set _ hKU)))

end ModifiedCartan
#print axioms ModifiedCartan.LocalMeasureConvergence.ae_unique
