import ModifiedCartan.SubmeanEnvelopeRepresentative
import ModifiedCartan.SubharmonicMeanCriterion
import ModifiedCartan.SubharmonicLimitMeans

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem submeanEnvelope_isSubharmonicOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (hsub : ∀ᵐ z ∂volume.restrict U, ∀ r : ℝ, 0 < r → closedBall z r ⊆ U →
      f z ≤ diskAverage r f z) : IsSubharmonicOn U (submeanEnvelope U f) := by
  apply isSubharmonicOn_of_real_disk_means (upperSemicontinuousOn_submeanEnvelope hU hf)
    (fun z hz => submeanEnvelope_ne_top hU f hz) hf (submeanEnvelope_ae_eq hU hf hsub)
  intro c r hr hball
  simpa only [diskAverage_eq hr.le] using submeanEnvelope_le (f := f) hr hball

theorem exists_subharmonic_representative_of_localL1_limit
    {U : Set ℂ} (hU : IsOpen U) {u : ℕ → ℂ → EReal}
    (hu : ∀ n, IsSubharmonicOn U (u n))
    (hfinite : ∀ n, ∀ᵐ z ∂volume.restrict U, u n z ≠ ⊥ ∧ u n z ≠ ⊤)
    {f : ℂ → ℝ} (hconv : LocalLpConvergence 1 U (fun n z => (u n z).toReal) f) :
    ∃ v : ℂ → EReal, IsSubharmonicOn U v ∧
      v =ᵐ[volume.restrict U] (fun z => (f z : EReal)) := by
  have hfi : LocallyIntegrableOn f U := (locallyIntegrableOn_iff hU.isLocallyClosed).mpr
    (fun K hKU hK => memLp_one_iff_integrable.mp (hconv.limit_mem K hK hKU))
  have hsub := ae_le_diskAverage_of_subharmonic_limit hU hu hfinite hconv
  exact ⟨submeanEnvelope U f, submeanEnvelope_isSubharmonicOn hU hfi hsub,
    submeanEnvelope_ae_eq hU hfi hsub⟩

theorem exists_nontrivial_subharmonic_representative_of_localL1_limit
    {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) {u : ℕ → ℂ → EReal}
    (hu : ∀ n, IsSubharmonicOn U (u n))
    (hfinite : ∀ n, ∀ᵐ z ∂volume.restrict U, u n z ≠ ⊥ ∧ u n z ≠ ⊤)
    {f : ℂ → ℝ} (hconv : LocalLpConvergence 1 U (fun n z => (u n z).toReal) f) :
    ∃ v : ℂ → EReal, IsSubharmonicOn U v ∧ (∃ z ∈ U, v z ≠ ⊥) ∧
      v =ᵐ[volume.restrict U] (fun z => (f z : EReal)) := by
  obtain ⟨v, hv, hrep⟩ := exists_subharmonic_representative_of_localL1_limit hU hu hfinite hconv
  obtain ⟨z, hzU, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hU.measure_ne_zero volume hne) hrep
  refine ⟨v, hv, ⟨z, hzU, ?_⟩, hrep⟩
  rw [hz]
  exact EReal.coe_ne_bot _


end ModifiedCartan
