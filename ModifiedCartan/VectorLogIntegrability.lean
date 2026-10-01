import ModifiedCartan.NormalizedNormMax
import ModifiedCartan.AnalyticLogSubharmonic
import Mathlib.MeasureTheory.Function.LpOrder

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem memLp_finset_sup' {ι : Type*} {μ : Measure ℂ} {f : ι → ℂ → ℝ}
    (s : Finset ι) (hne : s.Nonempty) (hf : ∀ i ∈ s, MemLp (f i) 1 μ) :
    MemLp (fun z => s.sup' hne (fun i => f i z)) 1 μ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hne).elim
  | @insert a s hnot ih =>
    by_cases hs : s.Nonempty
    · have hh := (hf a (Finset.mem_insert_self a s)).sup
        (ih hs (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      simpa only [Finset.sup'_insert hs] using! hh
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simpa using hf a (Finset.mem_insert_self a ∅)

theorem memLp_log_euclideanNorm_of_components {n : ℕ} {μ : Measure ℂ} [IsFiniteMeasure μ]
    {f : Index n → ℂ → ℂ}
    (hmeas : AEStronglyMeasurable (fun z => Real.log (euclideanNorm (fun j => f j z))) μ)
    (hlog : ∀ j, MemLp (fun z => Real.log ‖f j z‖) 1 μ)
    (hnz : ∀ᵐ z ∂μ, ∀ j, f j z ≠ 0) :
    MemLp (fun z => Real.log (euclideanNorm (fun j => f j z))) 1 μ := by
  let m : ℂ → ℝ := fun z => Finset.univ.sup' Finset.univ_nonempty (fun j => Real.log ‖f j z‖)
  have hm : MemLp m 1 μ := memLp_finset_sup' Finset.univ Finset.univ_nonempty (fun j _ => hlog j)
  have hd : MemLp ((fun z => Real.log (euclideanNorm (fun j => f j z))) - m) 1 μ := by
    apply MemLp.of_bound (hmeas.sub hm.aestronglyMeasurable) (Real.log (Real.sqrt (n + 1)))
    filter_upwards [hnz] with z hz
    simpa only [inv_one, one_mul, Pi.sub_apply, m] using
      normalized_log_euclideanNorm_sub_max_bound (fun j => f j z) zero_lt_one hz
  simpa only [sub_add_cancel] using hd.add hm

theorem integrableOn_log_euclideanNorm_on_compact {n : ℕ} {D K : Set ℂ}
    (hD : IsOpen D) (hDc : IsPreconnected D) {f : Index n → ℂ → ℂ}
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) D) (hnz : ∀ j, ∃ z ∈ D, f j z ≠ 0)
    (hK : IsCompact K) (hKD : K ⊆ D) :
    IntegrableOn (fun z => Real.log (euclideanNorm (fun j => f j z))) K := by
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply memLp_one_iff_integrable.mp
  apply memLp_log_euclideanNorm_of_components
  · have hv : ContinuousOn (fun z => (fun j => f j z)) K :=
      continuousOn_pi.mpr (fun j => (hf j).continuousOn.mono hKD)
    exact (((euclideanNorm_continuous.comp_continuousOn hv).aestronglyMeasurable
      hK.measurableSet).aemeasurable.log).aestronglyMeasurable
  · intro j
    exact memLp_one_iff_integrable.mpr (integrableOn_log_norm_on_compact (hf j) hKD hK)
  · exact (ae_all_iff.mpr (fun j => analytic_ae_ne_zero hD hDc (hf j) (hnz j))).filter_mono
      (ae_mono (Measure.restrict_mono_set _ hKD))

end ModifiedCartan
#print axioms ModifiedCartan.integrableOn_log_euclideanNorm_on_compact
