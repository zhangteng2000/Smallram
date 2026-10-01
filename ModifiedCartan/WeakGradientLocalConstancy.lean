import ModifiedCartan.WeakGradientLipschitz

open scoped Topology NNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem HasWeakComplexGradient.eq_on_ball_of_ae_zero
    {U : Set ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ} (hu : HasWeakComplexGradient U u g)
    (hc : Continuous u) (hg : g =ᵐ[volume.restrict U] (fun _ => 0))
    {c : ℂ} {r R : ℝ} (hrR : r < R) (hball : closedBall c R ⊆ U)
    {x y : ℂ} (hx : x ∈ ball c r) (hy : y ∈ ball c r) : u x = u y := by
  have hbound : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ ((0 : ℝ≥0) : ℝ) := by
    filter_upwards [hg] with z hz
    simp only [hz, norm_zero, NNReal.coe_zero, le_refl]
  obtain ⟨v, hv, heq⟩ := hu.exists_lipschitz_rep_on_ball hrR hball hbound
  have hpoint := Measure.eqOn_open_of_ae_eq heq isOpen_ball hc.continuousOn hv.continuous.continuousOn
  rw [hpoint hx, hpoint hy]
  have hd : dist (v x) (v y) ≤ 0 := by simpa using hv.dist_le_mul x y
  exact dist_eq_zero.mp (le_antisymm hd dist_nonneg)

theorem HasWeakComplexGradient.locally_constant_of_ae_zero
    {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : HasWeakComplexGradient U u g) (hc : Continuous u)
    (hg : g =ᵐ[volume.restrict U] (fun _ => 0)) {x : ℂ} (hx : x ∈ U) :
    u =ᶠ[𝓝 x] (fun _ => u x) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hball : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hr : 0 < ε / 4 := by positivity
  filter_upwards [ball_mem_nhds x hr] with y hy
  exact hu.eq_on_ball_of_ae_zero hc hg (by linarith : ε / 4 < ε / 2) hball hy (mem_ball_self hr)

theorem HasWeakComplexGradient.exists_const_of_ae_zero
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : HasWeakComplexGradient U u g) (hc : Continuous u)
    (hg : g =ᵐ[volume.restrict U] (fun _ => 0)) :
    ∃ k : ℝ, ∀ x ∈ U, u x = k := by
  have hd (x : ℂ) (hx : x ∈ U) : HasFDerivAt u (0 : ℂ →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (u x) x).congr_of_eventuallyEq (hu.locally_constant_of_ae_zero hU hc hg hx)
  exact hU.exists_is_const_of_fderiv_eq_zero hUc
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hd x hx).fderiv)

end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.exists_const_of_ae_zero

