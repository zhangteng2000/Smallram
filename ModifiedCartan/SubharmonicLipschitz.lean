import ModifiedCartan.WeakGradientLipschitz
import ModifiedCartan.SubharmonicContinuousRepresentative

open scoped Topology ENNReal NNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem IsSubharmonicOn.lipschitzOnWith_of_weak_gradient_bound_on_ball
    {U : Set ℂ} {u : ℂ → EReal} {v : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U u)
    (hrep : u =ᵐ[volume.restrict U] (fun z => (v z : EReal)))
    (hg : HasWeakComplexGradient U v g)
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U)
    {C : ℝ≥0} (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ (C : ℝ)) :
    (∀ z ∈ ball c r, u z = ((u z).toReal : EReal)) ∧
      LipschitzOnWith C (fun z => (u z).toReal) (ball c r) := by
  obtain ⟨w, hw, heq⟩ := hg.exists_lipschitz_rep_on_ball hrR hball hbound
  have hsub : ball c r ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hball
  have hrep' : u =ᵐ[volume.restrict (ball c r)] (fun z => (w z : EReal)) := by
    filter_upwards [hrep.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub)), heq]
      with z hz hz'
    rw [hz, hz']
  have hpoint := (hu.mono hsub).eqOn_of_ae_eq_continuous isOpen_ball hw.continuous.continuousOn hrep'
  have hreal (z : ℂ) (hz : z ∈ ball c r) : (u z).toReal = w z := by
    rw [hpoint hz, EReal.toReal_coe]
  constructor
  · intro z hz
    rw [hpoint hz, EReal.toReal_coe]
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hreal x hx, hreal y hy]
    exact hw.dist_le_mul x y

/-- Local boundedness of the actual weak gradient proves finiteness and
local Lipschitz continuity of the original subharmonic representative. -/
theorem IsSubharmonicOn.locallyLipschitzOn_of_weak_gradient_bound
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → EReal} {v : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U u)
    (hrep : u =ᵐ[volume.restrict U] (fun z => (v z : EReal)))
    (hg : HasWeakComplexGradient U v g)
    {C : ℝ≥0} (hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ (C : ℝ)) :
    (∀ z ∈ U, u z = ((u z).toReal : EReal)) ∧
      LocallyLipschitzOn U (fun z => (u z).toReal) := by
  have hlocal (x : ℂ) (hx : x ∈ U) : ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ ball x r, u z = ((u z).toReal : EReal)) ∧
      LipschitzOnWith C (fun z => (u z).toReal) (ball x r) := by
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    have hb : closedBall x (ε / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hh := hu.lipschitzOnWith_of_weak_gradient_bound_on_ball hrep hg
      (r := ε / 4) (by linarith : ε / 4 < ε / 2) hb hbound
    exact ⟨ε / 4, by positivity, hh⟩
  constructor
  · intro x hx
    obtain ⟨r, hr, hfinite, _⟩ := hlocal x hx
    exact hfinite x (mem_ball_self hr)
  · intro x hx
    obtain ⟨r, hr, _, hlip⟩ := hlocal x hx
    refine ⟨C, ball x r, ?_, hlip⟩
    exact mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr)

/-- Finite gradient values imply the regularity required in
`lem:finite-gradient-convex`; convexity itself is proved separately. -/
theorem IsSubharmonicOn.locallyLipschitzOn_of_finite_gradient
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → EReal} {v : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : IsSubharmonicOn U u)
    (hrep : u =ᵐ[volume.restrict U] (fun z => (v z : EReal)))
    (hg : HasWeakComplexGradient U v g)
    (A : Finset ℂ) (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A) :
    (∀ z ∈ U, u z = ((u z).toReal : EReal)) ∧
      LocallyLipschitzOn U (fun z => (u z).toReal) := by
  apply hu.locallyLipschitzOn_of_weak_gradient_bound hU hrep hg (C := A.sup (fun a => ‖a‖₊))
  filter_upwards [hA] with z hz
  exact_mod_cast (show ‖g z‖₊ ≤ A.sup (fun a => ‖a‖₊) from Finset.le_sup hz)

end ModifiedCartan
#print axioms ModifiedCartan.IsSubharmonicOn.locallyLipschitzOn_of_finite_gradient
