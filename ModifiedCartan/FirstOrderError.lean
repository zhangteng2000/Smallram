import ModifiedCartan.IntegrableSystem
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {A : Type*} [NormedRing A] [NormedSpace ℝ A] [CompleteSpace A]

noncomputable def linearGauge (C : A) (t : ℝ) : A := 1 + t⁻¹ • C

noncomputable def inverseLinearGauge (C : A) (t : ℝ) : A := Ring.inverse (linearGauge C t)

noncomputable def firstOrderError (C D : A) (t : ℝ) : A :=
  (t⁻¹ ^ 2) • (inverseLinearGauge C t * D)

theorem linearGauge_tendsto (C : A) : Tendsto (linearGauge C) atTop (𝓝 1) := by
  unfold linearGauge
  simpa only [zero_smul, add_zero] using!
    (tendsto_const_nhds.add ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul_const C))

theorem inverseLinearGauge_tendsto (C : A) : Tendsto (inverseLinearGauge C) atTop (𝓝 1) := by
  have hi := (NormedRing.inverse_continuousAt (1 : Aˣ)).tendsto.comp (linearGauge_tendsto C)
  unfold inverseLinearGauge
  simpa only [Units.val_one, Ring.inverse_one, Function.comp_apply] using! hi

theorem linearGauge_eventually_unit_bound (C : A) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t, T ≤ t →
      IsUnit (linearGauge C t) ∧ ‖inverseLinearGauge C t‖ ≤ ‖(1 : A)‖ + 1 := by
  have hu : ∀ᶠ t in atTop, IsUnit (linearGauge C t) :=
    (linearGauge_tendsto C).eventually (Units.nhds (1 : Aˣ))
  have hb : ∀ᶠ t : ℝ in atTop, ‖inverseLinearGauge C t‖ < ‖(1 : A)‖ + 1 :=
    Filter.Tendsto.eventually_lt_const (by linarith) (inverseLinearGauge_tendsto C).norm
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hu.and hb)
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro t ht
  have hh := hT t ((le_max_right _ _).trans ht)
  exact ⟨hh.1, hh.2.le⟩

theorem linearGauge_continuousOn (C : A) {T : ℝ} (hT : 0 < T) :
    ContinuousOn (linearGauge C) (Ici T) := by
  apply continuousOn_const.add
  exact (continuousOn_id.inv₀ (fun t ht => (hT.trans_le ht).ne')).smul continuousOn_const

theorem inverseLinearGauge_continuousOn (C : A) {T : ℝ} (hT : 0 < T)
    (hu : ∀ t, T ≤ t → IsUnit (linearGauge C t)) :
    ContinuousOn (inverseLinearGauge C) (Ici T) := by
  intro t ht
  have hi : ContinuousAt Ring.inverse (linearGauge C t) := by
    obtain ⟨u, he⟩ := hu t ht
    rw [← he]
    exact NormedRing.inverse_continuousAt u
  exact hi.comp_continuousWithinAt (linearGauge_continuousOn C hT t ht)

theorem firstOrderError_continuousOn (C D : A) {T : ℝ} (hT : 0 < T)
    (hu : ∀ t, T ≤ t → IsUnit (linearGauge C t)) :
    ContinuousOn (firstOrderError C D) (Ici T) := by
  exact ((continuousOn_id.inv₀ (fun t ht => (hT.trans_le ht).ne')).pow 2).smul
    ((inverseLinearGauge_continuousOn C hT hu).mul continuousOn_const)

theorem firstOrderError_norm_le (C D : A) {t K : ℝ} (ht : 0 < t)
    (hbound : ‖inverseLinearGauge C t‖ ≤ K) :
    ‖firstOrderError C D t‖ ≤ (K * ‖D‖) * t ^ (-2 : ℝ) := by
  rw [firstOrderError, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ t⁻¹ ^ 2 * (‖inverseLinearGauge C t‖ * ‖D‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (sq_nonneg _)
    _ ≤ t⁻¹ ^ 2 * (K * ‖D‖) := by gcongr
    _ = _ := by rw [Real.rpow_neg ht.le, Real.rpow_two, inv_pow]; ring

theorem firstOrderError_integrableOn (C D : A) {T K : ℝ} (hT : 0 < T)
    (hu : ∀ t, T ≤ t → IsUnit (linearGauge C t))
    (hb : ∀ t, T ≤ t → ‖inverseLinearGauge C t‖ ≤ K) :
    IntegrableOn (firstOrderError C D) (Ici T) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ici T) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hT)
  apply Integrable.mono' (hi.const_mul (K * ‖D‖))
    ((firstOrderError_continuousOn C D hT hu).aestronglyMeasurable measurableSet_Ici)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact firstOrderError_norm_le C D (hT.trans_le ht) (hb t ht)

/-- The error in the manuscript's near-identity conjugation is an actual
continuous integrable function on an explicitly justified tail. -/
theorem firstOrderError_tail_exists (C D : A) :
    ∃ T : ℝ, 1 ≤ T ∧
      (∀ t, T ≤ t → IsUnit (linearGauge C t)) ∧
      ContinuousOn (firstOrderError C D) (Ici T) ∧
      IntegrableOn (firstOrderError C D) (Ici T) ∧
      (∀ t, T ≤ t → ‖firstOrderError C D t‖ ≤
        ((‖(1 : A)‖ + 1) * ‖D‖) * t ^ (-2 : ℝ)) := by
  obtain ⟨T, hT, hb⟩ := linearGauge_eventually_unit_bound C
  have hTp := zero_lt_one.trans_le hT
  have hu := fun t ht => (hb t ht).1
  refine ⟨T, hT, hu, firstOrderError_continuousOn C D hTp hu,
    firstOrderError_integrableOn C D hTp hu (fun t ht => (hb t ht).2), ?_⟩
  intro t ht
  exact firstOrderError_norm_le C D (hTp.trans_le ht) (hb t ht).2

end ModifiedCartan
#print axioms ModifiedCartan.inverseLinearGauge_tendsto
#print axioms ModifiedCartan.firstOrderError_tail_exists


