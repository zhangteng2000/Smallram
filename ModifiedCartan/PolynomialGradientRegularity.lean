import ModifiedCartan.MonicEquationBound
import ModifiedCartan.SubharmonicLipschitz

open scoped Topology NNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Step 1 of `prop:homogeneity`: the actual polynomial weak-gradient
relation implies local Lipschitz regularity of the original representative. -/
theorem IsSubharmonicOn.locallyLipschitzOn_of_gradient_equation
    {n : ℕ} {U : Set ℂ} (hU : IsOpen U) {u : ℂ → EReal} {v : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U u)
    (hrep : u =ᵐ[volume.restrict U] (fun z => (v z : EReal)))
    (hw : HasWeakComplexGradient U v g) {a : Index n → ℂ → ℂ}
    (ha : ∀ i, ContinuousOn (a i) U)
    (heq : ∀ᵐ z ∂volume.restrict U, g z ^ (n + 1) + ∑ i : Index n, a i z * g z ^ i.val = 0) :
    (∀ z ∈ U, u z = ((u z).toReal : EReal)) ∧ LocallyLipschitzOn U (fun z => (u z).toReal) := by
  have hlocal (c : ℂ) (hc : c ∈ U) : ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ ball c R, u z = ((u z).toReal : EReal)) ∧
      LocallyLipschitzOn (ball c R) (fun z => (u z).toReal) := by
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
    have hclosed : closedBall c (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hsub : ball c (ε / 2) ⊆ U := ball_subset_closedBall.trans hclosed
    obtain ⟨C, hC⟩ := monic_equation_gradient_bound_on_compact (isCompact_closedBall c (ε / 2)) hclosed ha heq
    have hb : ∀ᵐ z ∂volume.restrict (ball c (ε / 2)), ‖g z‖ ≤ (C : ℝ) :=
      hC.filter_mono (ae_mono (Measure.restrict_mono_set _ ball_subset_closedBall))
    exact ⟨ε / 2, half_pos hε,
      (hu.mono hsub).locallyLipschitzOn_of_weak_gradient_bound isOpen_ball
        (hrep.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub))) (hw.restrict hsub) hb⟩
  constructor
  · intro c hc
    obtain ⟨R, hR, hfinite, _⟩ := hlocal c hc
    exact hfinite c (mem_ball_self hR)
  · intro c hc
    obtain ⟨R, hR, _, hLip⟩ := hlocal c hc
    obtain ⟨C, V, hV, hVC⟩ := hLip (mem_ball_self hR)
    refine ⟨C, V, mem_nhdsWithin_of_mem_nhds ?_, hVC⟩
    rwa [nhdsWithin_eq_nhds.mpr (ball_mem_nhds c hR)] at hV

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.locallyLipschitzOn_of_gradient_equation
