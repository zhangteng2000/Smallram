import ModifiedCartan.PhaseConePropagation

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem not_isEssentialPhaseAt_iff {g : ℂ → ℂ} {a c : ℂ} :
    ¬ IsEssentialPhaseAt g a c ↔ ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ z ∂volume.restrict (ball c δ), g z ≠ a := by
  have heq (δ : ℝ) : (∀ᵐ z ∂volume.restrict (ball c δ), g z ≠ a) ↔
      volume {z | z ∈ ball c δ ∧ g z = a} = 0 := by
    rw [ae_restrict_iff' measurableSet_ball, ae_iff]
    simp only [_root_.not_imp, not_not]
  simp only [IsEssentialPhaseAt, not_forall, _root_.not_imp, ne_eq, not_not, heq, exists_prop]

theorem exists_radius_excluding_nonessential (g : ℂ → ℂ) (c : ℂ) (A : Finset ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ᵐ z ∂volume.restrict (ball c r),
      ∀ a ∈ A, ¬ IsEssentialPhaseAt g a c → g z ≠ a := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    exact ⟨1, zero_lt_one, Eventually.of_forall (by simp)⟩
  | @insert a A ha ih =>
    obtain ⟨r, hr, hAr⟩ := ih
    by_cases he : IsEssentialPhaseAt g a c
    · refine ⟨r, hr, ?_⟩
      filter_upwards [hAr] with z hz b hb hbne
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact False.elim (hbne he)
      · exact hz b hb hbne
    · obtain ⟨δ, hδ, hδae⟩ := not_isEssentialPhaseAt_iff.mp he
      refine ⟨min r δ, lt_min hr hδ, ?_⟩
      filter_upwards [hAr.filter_mono (ae_mono (Measure.restrict_mono_set _
        (ball_subset_ball (min_le_left r δ)))),
        hδae.filter_mono (ae_mono (Measure.restrict_mono_set _
        (ball_subset_ball (min_le_right r δ))))] with z hz hza b hb hbne
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hza
      · exact hz b hb hbne

noncomputable def essentialPhasesAt (A : Finset ℂ) (g : ℂ → ℂ) (c : ℂ) : Finset ℂ := by
  classical
  exact A.filter (fun a => IsEssentialPhaseAt g a c)

theorem mem_essentialPhasesAt {A : Finset ℂ} {g : ℂ → ℂ} {a c : ℂ} :
    a ∈ essentialPhasesAt A g c ↔ a ∈ A ∧ IsEssentialPhaseAt g a c := by
  classical
  exact Finset.mem_filter

/-- A finite-valued measurable gradient has, near each interior point,
only phases that occur with positive measure in every neighborhood there. -/
theorem exists_local_essential_phases {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (A : Finset ℂ) (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A) {c : ℂ} (hc : c ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall c r ⊆ U ∧
      (∀ᵐ z ∂volume.restrict (ball c r), g z ∈ essentialPhasesAt A g c) ∧
      (essentialPhasesAt A g c).Nonempty := by
  classical
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  obtain ⟨δ, hδ, hδae⟩ := exists_radius_excluding_nonessential g c A
  let r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hrδ : r ≤ δ := ((half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)).le
  have hb : closedBall c r ⊆ U := (closedBall_subset_ball hrε).trans hεU
  have hae : ∀ᵐ z ∂volume.restrict (ball c r), g z ∈ essentialPhasesAt A g c := by
    filter_upwards [hA.filter_mono (ae_mono (Measure.restrict_mono_set _ (ball_subset_closedBall.trans hb))),
      hδae.filter_mono (ae_mono (Measure.restrict_mono_set _ (ball_subset_ball hrδ)))] with z hz he
    apply mem_essentialPhasesAt.mpr
    refine ⟨hz, ?_⟩
    by_contra hnot
    exact he (g z) hz hnot rfl
  obtain ⟨z, hz, hza⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr hr)) hae
  exact ⟨r, hr, hb, hae, ⟨g z, hza⟩⟩

end ModifiedCartan
#print axioms ModifiedCartan.exists_local_essential_phases
