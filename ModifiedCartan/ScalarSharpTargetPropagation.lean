import ModifiedCartan.ScalarFixedRateMovingConnections
import ModifiedCartan.ScalarMovingLines

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem HasRectangleCrossesAtRate.moving_box
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (h : HasRectangleCrossesAtRate f r s Ω κ)
    {a : ℕ → ℂ} {b : ℂ} (ha : Tendsto a atTop (𝓝 b))
    {ε : ℝ} (hε : 0 < ε) (hball : closedBall b (4 * ε) ⊆ Ω) :
    ∀ᶠ ν in atTop,
      ScalarGoodCross f (r ν) (s ν) κ (ComplexRect.box (a ν) ε ε hε hε) := by
  let H := ComplexRect.box b (2 * ε) (ε / 2) (by positivity) (half_pos hε)
  let V := ComplexRect.box b (ε / 2) (2 * ε) (half_pos hε) (by positivity)
  have hHΩ : H.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall b (by positivity) (half_pos hε)).trans
      ((closedBall_subset_closedBall (by linarith : 2 * ε + ε / 2 ≤ 4 * ε)).trans hball)
  have hVΩ : V.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall b (half_pos hε) (by positivity)).trans
      ((closedBall_subset_closedBall (by linarith : ε / 2 + 2 * ε ≤ 4 * ε)).trans hball)
  have hn : Tendsto (fun ν => ‖a ν - b‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (ha.sub_const b).norm
  filter_upwards [h H hHΩ, h V hVΩ, hn.eventually_lt_const (half_pos hε)] with ν hH hV hn
  exact scalarGoodCross_box_of_fixed hε hn.le hH hV

/-- The rate of an actual reference segment's approach to a fixed target
propagates to a whole actual horizontal segment near any moving center in
the same connected level region. Every new line is constructed. -/
theorem HasRectangleCrossesAtRate.moving_box_to_fixed_target
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (h : HasRectangleCrossesAtRate f r s Ω κ) (hκ : 0 < κ)
    (hr : Tendsto r atTop atTop) (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    {b : ℕ → ℂ} {b₀ : ℂ} (hb : Tendsto b atTop (𝓝 b₀))
    {θ : ℝ} (hθ : 0 < θ) (hballB : closedBall b₀ (4 * θ) ⊆ Ω)
    {yB : ℕ → ℝ} {β : WithTop ℂ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hB : ∀ᶠ ν in atTop, yB ν ∈ Icc ((b ν).im - θ) ((b ν).im + θ) ∧
      ∀ t ∈ Icc ((b ν).re - θ) ((b ν).re + θ),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yB ν⟩ : ℂ)) ≤ Real.exp (-κ * s ν))
    (hclose : ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f ((r ν : ℂ) * (⟨(b ν).re - θ, yB ν⟩ : ℂ)) -
        scalarSphereValue β‖ ≤ C₀ * Real.exp (-κ * s ν))
    {a : ℕ → ℂ} {a₀ : ℂ} (ha : Tendsto a atTop (𝓝 a₀)) (ha₀ : a₀ ∈ Ω) :
    ∃ ε > 0, ∃ y : ℕ → ℝ, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      (y ν ∈ Icc ((a ν).im - ε) ((a ν).im + ε) ∧
        ∀ t ∈ Icc ((a ν).re - ε) ((a ν).re + ε),
          r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)) ≤ Real.exp (-κ * s ν)) ∧
      ∀ t ∈ Icc ((a ν).re - ε) ((a ν).re + ε),
        ‖scalarCurveSphere f ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)) - scalarSphereValue β‖ ≤
          C * Real.exp (-κ * s ν) := by
  obtain ⟨d, hd, hdΩ⟩ := (isCompact_singleton (x := a₀)).exists_cthickening_subset_open hΩ
    (singleton_subset_iff.mpr ha₀)
  let ε := d / 4
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hballA : closedBall a₀ (4 * ε) ⊆ Ω := by
    have he : 4 * ε = d := by dsimp only [ε]; ring
    rw [he]
    exact (closedBall_subset_cthickening_singleton a₀ d).trans hdΩ
  obtain ⟨y, hy⟩ := exists_moving_horizontal_lines hε (h.moving_box ha hε hballA)
  obtain ⟨C₁, hC₁, hconnect⟩ := h.two_variable_box_anchors hκ hr hΩ hc ha hb
    tendsto_const_nhds tendsto_const_nhds hε hθ hballA hballB hy hB
  refine ⟨ε, hε, y, 2 * ε + C₁ + C₀, by positivity, ?_⟩
  filter_upwards [hy, hconnect, hclose, hr.eventually_ge_atTop 0] with ν hyν hcν hbν hrν
  refine ⟨hyν, ?_⟩
  intro t ht
  have hd := scalar_curve_horizontal_diameter f hrν (Real.exp_pos (-κ * s ν)).le hyν.2 ht
    (show (a ν).re - ε ∈ Icc ((a ν).re - ε) ((a ν).re + ε) from ⟨le_rfl, by linarith⟩)
  have hd' : ‖scalarCurveSphere f ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)) -
      scalarCurveSphere f ((r ν : ℂ) * (⟨(a ν).re - ε, y ν⟩ : ℂ))‖ ≤
        (2 * ε) * Real.exp (-κ * s ν) := by
    convert hd using 1 <;> ring
  have hh₁ := norm_sub_le_norm_sub_add_norm_sub
    (scalarCurveSphere f ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)))
    (scalarCurveSphere f ((r ν : ℂ) * (⟨(a ν).re - ε, y ν⟩ : ℂ)))
    (scalarCurveSphere f ((r ν : ℂ) * (⟨(b ν).re - θ, yB ν⟩ : ℂ)))
  have hh₂ := norm_sub_le_norm_sub_add_norm_sub
    (scalarCurveSphere f ((r ν : ℂ) * (⟨t, y ν⟩ : ℂ)))
    (scalarCurveSphere f ((r ν : ℂ) * (⟨(b ν).re - θ, yB ν⟩ : ℂ))) (scalarSphereValue β)
  nlinarith

end ModifiedCartan
#print axioms ModifiedCartan.HasRectangleCrossesAtRate.moving_box
#print axioms ModifiedCartan.HasRectangleCrossesAtRate.moving_box_to_fixed_target
