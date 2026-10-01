import ModifiedCartan.ExtendedLogConvergence
import Mathlib.Topology.Semicontinuity.Basic

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- Standard disk-area submean definition for extended-valued subharmonic
functions. The nonnegative deficit makes the inequality meaningful also at
negative infinity. No integrability, representation, or compactness result is
part of the definition. Used for manuscript `lem:subharmonic-compactness`. -/
structure IsSubharmonicOn (U : Set ℂ) (u : ℂ → EReal) : Prop where
  upperSemicontinuousOn : UpperSemicontinuousOn u U
  ne_top : ∀ z ∈ U, u z ≠ ⊤
  disk_submean : ∀ (c : ℂ) (r : ℝ), 0 < r → closedBall c r ⊆ U →
    ∀ M : ℝ, (∀ z ∈ closedBall c r, u z ≤ (M : EReal)) →
      ∫⁻ z in ball c r, ((M : EReal) - u z).toENNReal ≤
        volume (ball c r) * ((M : EReal) - u c).toENNReal

theorem IsSubharmonicOn.mono {U V : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hVU : V ⊆ U) : IsSubharmonicOn V u where
  upperSemicontinuousOn := hu.upperSemicontinuousOn.mono hVU
  ne_top z hz := hu.ne_top z (hVU hz)
  disk_submean c r hr hball M hM := hu.disk_submean c r hr (hball.trans hVU) M hM

theorem isSubharmonicOn_const (U : Set ℂ) (a : EReal) (ha : a ≠ ⊤) :
    IsSubharmonicOn U (fun _ => a) where
  upperSemicontinuousOn := upperSemicontinuousOn_const
  ne_top _ _ := ha
  disk_submean c r _ _ M _ := by
    simp only [setLIntegral_const, mul_comm, le_refl]

theorem isSubharmonicOn_bot (U : Set ℂ) : IsSubharmonicOn U (fun _ => ⊥) :=
  isSubharmonicOn_const U ⊥ bot_ne_top

theorem IsSubharmonicOn.exists_real_upper_bound {U K : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, ∀ z ∈ K, u z ≤ (M : EReal) := by
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha, hmax⟩ := (hu.upperSemicontinuousOn.mono hKU).exists_isMaxOn hne hK
    obtain ⟨M, hM, _⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr (hu.ne_top a (hKU ha)))
    exact ⟨M, fun z hz => (isMaxOn_iff.mp hmax z hz).trans (le_of_lt hM)⟩
  · exact ⟨0, fun z hz => False.elim (hne ⟨z, hz⟩)⟩

theorem IsSubharmonicOn.aemeasurable {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hU : MeasurableSet U) : AEMeasurable u (volume.restrict U) := by
  apply aemeasurable_restrict_of_measurable_subtype hU
  exact (upperSemicontinuousOn_iff_restrict.mpr hu.upperSemicontinuousOn).measurable

theorem IsSubharmonicOn.deficit_aemeasurable {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hU : MeasurableSet U) (M : ℝ) :
    AEMeasurable (fun z => ((M : EReal) - u z).toENNReal) (volume.restrict U) :=
  (aemeasurable_const.sub (hu.aemeasurable hU)).ereal_toENNReal

theorem IsSubharmonicOn.deficit_lintegral_lt_top {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ U) (hc : u c ≠ ⊥)
    {M : ℝ} (hM : ∀ z ∈ closedBall c r, u z ≤ (M : EReal)) :
    ∫⁻ z in ball c r, ((M : EReal) - u z).toENNReal < ⊤ := by
  have hc' := hu.ne_top c (hball (mem_closedBall_self hr.le))
  have hfinite : ((M : EReal) - u c).toENNReal < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    apply EReal.toENNReal_ne_top_iff.mpr
    rw [← EReal.coe_toReal hc' hc, ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  have hvol : volume (ball c r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  exact (hu.disk_submean c r hr hball M hM).trans_lt (ENNReal.mul_lt_top hvol hfinite)

theorem IsSubharmonicOn.ae_finite_on_ball {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ U) (hc : u c ≠ ⊥) :
    ∀ᵐ z ∂volume.restrict (ball c r), u z ≠ ⊥ ∧ u z ≠ ⊤ := by
  obtain ⟨M, hM⟩ := hu.exists_real_upper_bound (isCompact_closedBall c r) hball
  have hdef := (hu.mono (ball_subset_closedBall.trans hball)).deficit_aemeasurable isOpen_ball.measurableSet M
  have hfin := ae_lt_top' hdef (ne_of_lt (hu.deficit_lintegral_lt_top hr hball hc hM))
  filter_upwards [hfin, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzball
  refine ⟨?_, hu.ne_top z (hball (ball_subset_closedBall hzball))⟩
  intro hzbot
  simp only [hzbot, EReal.coe_sub_bot, EReal.toENNReal_top, lt_self_iff_false] at hz

theorem ereal_deficit_toReal {a : EReal} {M : ℝ} (ha : a ≠ ⊤) (ha' : a ≠ ⊥)
    (hM : a ≤ (M : EReal)) : ((M : EReal) - a).toENNReal.toReal = M - a.toReal := by
  have hle : a.toReal ≤ M := by
    rwa [← EReal.coe_toReal ha ha', EReal.coe_le_coe_iff] at hM
  rw [← EReal.coe_toReal ha ha', ← EReal.coe_sub,
    EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hle)]
  simp only [EReal.toReal_coe]

theorem IsSubharmonicOn.integrableOn_toReal_ball {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ U) (hc : u c ≠ ⊥) :
    IntegrableOn (fun z => (u z).toReal) (ball c r) := by
  obtain ⟨M, hM⟩ := hu.exists_real_upper_bound (isCompact_closedBall c r) hball
  have hdef := (hu.mono (ball_subset_closedBall.trans hball)).deficit_aemeasurable isOpen_ball.measurableSet M
  have hint := integrable_toReal_of_lintegral_ne_top hdef
    (ne_of_lt (hu.deficit_lintegral_lt_top hr hball hc hM))
  have : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top⟩
  apply ((integrable_const M).sub hint).congr
  filter_upwards [hu.ae_finite_on_ball hr hball hc, ae_restrict_mem isOpen_ball.measurableSet]
    with z hz hzball
  change M - ((M : EReal) - u z).toENNReal.toReal = (u z).toReal
  rw [ereal_deficit_toReal hz.2 hz.1 (hM z (ball_subset_closedBall hzball))]
  ring


end ModifiedCartan

