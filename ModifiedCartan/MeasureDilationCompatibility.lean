import ModifiedCartan.LocalSubsequence
import ModifiedCartan.MeasureLimitTransfer
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open scoped Topology
open Filter MeasureTheory Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Uniqueness on overlapping domains after a fixed nonzero real dilation.
Only subsequences with almost-everywhere convergence are needed. -/
theorem LocalMeasureConvergence.dilation_compatible
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {A B : ℕ → ℂ → ℂ} {a b : ℂ → ℂ} {R : ℝ} (hR : R ≠ 0) (c : ℂ)
    (hA : LocalMeasureConvergence U A a) (hB : LocalMeasureConvergence V B b)
    (ha : ContinuousOn a U) (hb : ContinuousOn b V)
    (hVU : MapsTo (fun z : ℂ => (R : ℂ) * z) V U)
    (hrel : ∀ ν z, z ∈ V → A ν ((R : ℂ) * z) = c * B ν z) :
    EqOn (fun z => a ((R : ℂ) * z)) (fun z => c * b z) V := by
  obtain ⟨ns, hns, hAlim⟩ := hA.exists_seq_tendsto_ae hU
  obtain ⟨ms, hms, hBlim⟩ := (hB.comp hns.tendsto_atTop).exists_seq_tendsto_ae hV
  have hAglo := (ae_restrict_iff' hU.measurableSet).mp hAlim
  have hApull := (Measure.quasiMeasurePreserving_smul (volume : Measure ℂ) hR).ae hAglo
  simp only [Complex.real_smul] at hApull
  have hcompat : (fun z => a ((R : ℂ) * z)) =ᵐ[volume.restrict V] (fun z => c * b z) := by
    filter_upwards [ae_restrict_of_ae hApull, hBlim, ae_restrict_mem hV.measurableSet]
      with z haz hbz hz
    have hla := (haz (hVU hz)).comp hms.tendsto_atTop
    have hlb := hbz.const_mul c
    have hsame : (fun ν => c * B (ns (ms ν)) z) =
        (fun ν => A (ns (ms ν)) ((R : ℂ) * z)) := by
      funext ν
      exact (hrel _ z hz).symm
    rw [hsame] at hlb
    exact tendsto_nhds_unique hla hlb
  exact Measure.eqOn_open_of_ae_eq hcompat hV
    (ha.comp (continuous_const.mul continuous_id).continuousOn hVU)
    (continuousOn_const.mul hb)

end ModifiedCartan
#print axioms ModifiedCartan.LocalMeasureConvergence.dilation_compatible
