import ModifiedCartan.LocalPhaseMaximum
import ModifiedCartan.SubharmonicLipschitz

open scoped Topology ENNReal NNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem IsSubharmonicOn.congr_on {U : Set ℂ} {u v : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (heq : EqOn u v U) : IsSubharmonicOn U v where
  upperSemicontinuousOn x hx :=
    UpperSemicontinuousWithinAt.congr_of_eventuallyEq (hu.upperSemicontinuousOn x hx) hx heq.eventuallyEq_nhdsWithin
  ne_top x hx := by rw [← heq hx]; exact hu.ne_top x hx
  disk_submean c r hr hball M hM := by
    have hcenter : c ∈ U := hball (mem_closedBall_self hr.le)
    have hM' : ∀ z ∈ closedBall c r, u z ≤ (M : EReal) := by
      intro z hz
      rw [heq (hball hz)]
      exact hM z hz
    have hi : (∫⁻ z in ball c r, ((M : EReal) - u z).toENNReal) =
        ∫⁻ z in ball c r, ((M : EReal) - v z).toENNReal := by
      apply setLIntegral_congr_fun measurableSet_ball
      intro z hz
      change ((M : EReal) - u z).toENNReal = ((M : EReal) - v z).toENNReal
      rw [heq (hball (ball_subset_closedBall hz))]
    rw [← hi, ← heq hcenter]
    exact hu.disk_submean c r hr hball M hM'

theorem IsSubharmonicOn.locally_convex_of_finite_gradient
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → EReal} {v : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U u)
    (hrep : u =ᵐ[volume.restrict U] (fun z => (v z : EReal)))
    (hw : HasWeakComplexGradient U v g)
    (A : Finset ℂ) (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A) {c : ℂ} (hc : c ∈ U) :
    ∃ s : ℝ, 0 < s ∧ ball c s ⊆ U ∧ ConvexOn ℝ (ball c s) (fun z => (u z).toReal) := by
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
  obtain ⟨s, hs, hsb, hconv⟩ := hsw.locally_convex_of_finite_gradient_continuous isOpen_ball
    hwc.continuous hww A (hA.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub)))
    (mem_ball_self (by positivity : 0 < ε / 4))
  refine ⟨s, hs, hsb.trans hsub, hconv.congr ?_⟩
  intro z hz
  change w z = (u z).toReal
  rw [hpoint (hsb hz), EReal.toReal_coe]

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.locally_convex_of_finite_gradient

