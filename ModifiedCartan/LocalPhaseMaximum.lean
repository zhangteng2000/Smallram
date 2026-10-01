import ModifiedCartan.PhaseConeAffine
import ModifiedCartan.GenericPhaseDirections
import ModifiedCartan.PhaseAffineMax
import ModifiedCartan.EssentialPhases

open scoped Topology NNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem IsSubharmonicOn.eqOn_phaseAffineMax_of_essential
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ C)
    {A : Finset ℂ} (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A) (hne : A.Nonempty)
    {c : ℂ} {s r R : ℝ} (hs : 0 < s) (hsr : s < r) (hrR : r < R)
    (hball : closedBall c R ⊆ U) (hess : ∀ a ∈ A, IsEssentialPhaseAt g a c) :
    EqOn u (phaseAffineMax A hne (u c) c) (ball c s) := by
  have hd : Dense ((fun x : ℂ => x - c) ⁻¹' genericPhaseDirections A) := by
    simpa only [sub_eq_add_neg] using
      (dense_genericPhaseDirections A).preimage (isOpenMap_add_right (-c))
  have he : IsClosed {x | u x = phaseAffineMax A hne (u c) c x} :=
    isClosed_eq hc (continuous_phaseAffineMax A hne (u c) c)
  have hmem : ball c s ∩ (fun x => x - c) ⁻¹' genericPhaseDirections A ⊆
      {x | u x = phaseAffineMax A hne (u c) c x} := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := exists_strictPhaseCone_of_generic hne hx.2
    change u x = phaseAffineMax A hne (u c) c x
    rw [phaseAffineMax_eq_on_strict_cone hne (u c) ha hax]
    exact hu.affine_on_essential_strict_cone hU hc hw hC hbound hA a hs hsr hrR hball (hess a ha) hx.1 hax
  intro x hx
  exact (closure_minimal hmem he) (hd.open_subset_closure_inter isOpen_ball hx)

theorem IsSubharmonicOn.locally_convex_of_finite_gradient_continuous
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U (fun z => (u z : EReal)))
    (hc : Continuous u) (hw : HasWeakComplexGradient U u g)
    (A : Finset ℂ) (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A) {c : ℂ} (hcU : c ∈ U) :
    ∃ s : ℝ, 0 < s ∧ ball c s ⊆ U ∧ ConvexOn ℝ (ball c s) u := by
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
  refine ⟨δ / 8, by positivity, (ball_subset_ball (by linarith : δ / 8 ≤ δ)).trans hsub, ?_⟩
  exact (convexOn_phaseAffineMax (convex_ball c (δ / 8)) B hne (u c) c).congr heq.symm

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.locally_convex_of_finite_gradient_continuous

