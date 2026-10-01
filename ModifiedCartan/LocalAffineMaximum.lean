import ModifiedCartan.SubharmonicLocalConvexity

open scoped Topology NNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The exact local affine maximum, retaining the information used to prove
finite-gradient convexity. Auxiliary to the scalar conclusion of `thm:A`. -/
theorem IsSubharmonicOn.locally_eq_phaseAffineMax_continuous
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    (A : Finset ℂ) (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A) {c : ℂ} (hcU : c ∈ U) :
    ∃ (s : ℝ) (B : Finset ℂ) (hB : B.Nonempty),
      0 < s ∧ ball c s ⊆ U ∧ B ⊆ A ∧
      EqOn u (phaseAffineMax B hB (u c) c) (ball c s) := by
  obtain ⟨δ, hδ, hδU, hB, hne⟩ := exists_local_essential_phases hU A hA hcU
  let B := essentialPhasesAt A g c
  have hsub : ball c δ ⊆ U := ball_subset_closedBall.trans hδU
  let C : ℝ≥0 := A.sup (fun a => ‖a‖₊)
  have hb : ∀ᵐ z ∂volume.restrict (ball c δ), ‖g z‖ ≤ (C : ℝ) := by
    filter_upwards [hA.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub))] with z hz
    exact_mod_cast (show ‖g z‖₊ ≤ C from Finset.le_sup hz)
  have hball : closedBall c (δ / 2) ⊆ ball c δ := closedBall_subset_ball (half_lt_self hδ)
  have heq := (hu.mono hsub).eqOn_phaseAffineMax_of_essential isOpen_ball hc (hw.restrict hsub)
    C.coe_nonneg hb hB hne (by positivity : 0 < δ / 8)
    (by linarith : δ / 8 < δ / 4) (by linarith : δ / 4 < δ / 2) hball
    (fun a ha => (mem_essentialPhasesAt.mp ha).2)
  refine ⟨δ / 8, B, hne, by positivity,
    (ball_subset_ball (by linarith : δ / 8 ≤ δ)).trans hsub, ?_, heq⟩
  intro a ha
  exact (mem_essentialPhasesAt.mp ha).1

/-- A finite weak gradient supplies the exact local phase maximum of the
original subharmonic representative, without global continuity premises. -/
theorem IsSubharmonicOn.locally_eq_phaseAffineMax
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → EReal} {v : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U u)
    (hrep : u =ᵐ[volume.restrict U] (fun z => (v z : EReal)))
    (hw : HasWeakComplexGradient U v g)
    (A : Finset ℂ) (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A) {c : ℂ} (hc : c ∈ U) :
    ∃ (s : ℝ) (B : Finset ℂ) (hB : B.Nonempty),
      0 < s ∧ ball c s ⊆ U ∧ B ⊆ A ∧
      EqOn (fun z => (u z).toReal) (phaseAffineMax B hB (u c).toReal c) (ball c s) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  have hball : closedBall c (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hsub : ball c (ε / 4) ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : ε / 4 ≤ ε / 2))).trans hball
  let C : ℝ≥0 := A.sup (fun a => ‖a‖₊)
  have hb : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ (C : ℝ) := by
    filter_upwards [hA] with z hz
    exact_mod_cast (show ‖g z‖₊ ≤ C from Finset.le_sup hz)
  obtain ⟨w, hwc, hvw⟩ := hw.exists_lipschitz_rep_on_ball
    (by linarith : ε / 4 < ε / 2) hball hb
  have huw : u =ᵐ[volume.restrict (ball c (ε / 4))] (fun z => (w z : EReal)) := by
    filter_upwards [hrep.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub)), hvw] with z hz hz'
    rw [hz, hz']
  have hpoint := (hu.mono hsub).eqOn_of_ae_eq_continuous isOpen_ball hwc.continuous.continuousOn huw
  have hsw := (hu.mono hsub).congr_on hpoint
  have hww := (hw.restrict hsub).congr_function_ae isOpen_ball hvw
  obtain ⟨s, B, hB, hs, hsb, hBA, heq⟩ := hsw.locally_eq_phaseAffineMax_continuous isOpen_ball
    hwc.continuous hww A (hA.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub)))
    (mem_ball_self (by positivity : 0 < ε / 4))
  refine ⟨s, B, hB, hs, hsb.trans hsub, hBA, ?_⟩
  have hcval : (u c).toReal = w c := by
    rw [hpoint (mem_ball_self (by positivity : 0 < ε / 4)), EReal.toReal_coe]
  intro z hz
  change (u z).toReal = _
  rw [hpoint (hsb hz), EReal.toReal_coe, hcval]
  exact heq hz

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.locally_eq_phaseAffineMax
