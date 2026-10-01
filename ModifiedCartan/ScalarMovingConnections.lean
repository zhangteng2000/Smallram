import ModifiedCartan.ScalarMovingAnchors
import ModifiedCartan.ScalarExponentialBounds

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Two moving horizontal anchors in one positive connected domain are
exponentially close. Both endpoint bridges and the finite interior chain are
constructed from the actual cross estimates. -/
theorem HasSmallRectangleCrosses.two_moving_box_anchors_exponential
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}
    (h : HasSmallRectangleCrosses f r s Ω)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    {a b : ℕ → ℂ} {a₀ b₀ : ℂ} (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ)
    (hballA : closedBall a₀ (4 * ε) ⊆ Ω) (hballB : closedBall b₀ (4 * θ) ⊆ Ω)
    {δA δB : ℝ} (hδA : 0 < δA) (hδB : 0 < δB) {yA yB : ℕ → ℝ}
    (hA : ∀ᶠ ν in atTop, yA ν ∈ Icc ((a ν).im - ε) ((a ν).im + ε) ∧
      ∀ t ∈ Icc ((a ν).re - ε) ((a ν).re + ε),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yA ν⟩ : ℂ)) ≤ Real.exp (-δA * s ν))
    (hB : ∀ᶠ ν in atTop, yB ν ∈ Icc ((b ν).im - θ) ((b ν).im + θ) ∧
      ∀ t ∈ Icc ((b ν).re - θ) ((b ν).re + θ),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yB ν⟩ : ℂ)) ≤ Real.exp (-δB * s ν)) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f ((r ν : ℂ) * (⟨(a ν).re - ε, yA ν⟩ : ℂ)) -
        scalarCurveSphere f ((r ν : ℂ) * (⟨(b ν).re - θ, yB ν⟩ : ℂ))‖ ≤
          C * Real.exp (-δ * s ν) := by
  obtain ⟨q⟩ := h.exists_horizontal_selection
  let A := ComplexRect.box a₀ (ε / 2) (ε / 2) (half_pos hε) (half_pos hε)
  let B := ComplexRect.box b₀ (θ / 2) (θ / 2) (half_pos hθ) (half_pos hθ)
  have hAΩ : A.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall a₀ (half_pos hε) (half_pos hε)).trans
      ((closedBall_subset_closedBall (by linarith : ε / 2 + ε / 2 ≤ 4 * ε)).trans hballA)
  have hBΩ : B.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall b₀ (half_pos hθ) (half_pos hθ)).trans
      ((closedBall_subset_closedBall (by linarith : θ / 2 + θ / 2 ≤ 4 * θ)).trans hballB)
  have h₁ := h.moving_box_anchors_exponential hr hs ha hε hballA hδA
    (q.rate_pos ⟨A, hAΩ⟩) hA (q.good ⟨A, hAΩ⟩)
  have h₂ := q.anchors_exponentially_close h hr hs hΩ hc ⟨A, hAΩ⟩ ⟨B, hBΩ⟩
  have h₃ := h.moving_box_anchors_exponential hr hs hb hθ hballB hδB
    (q.rate_pos ⟨B, hBΩ⟩) hB (q.good ⟨B, hBΩ⟩)
  have h₃' : ∃ δ > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖q.anchor ⟨B, hBΩ⟩ ν -
        scalarCurveSphere f ((r ν : ℂ) * (⟨(b ν).re - θ, yB ν⟩ : ℂ))‖ ≤ C * Real.exp (-δ * s ν) := by
    simpa only [ScalarHorizontalSelection.anchor, B, ComplexRect.box, norm_sub_rev] using h₃
  exact exponential_distance_trans hs (exponential_distance_trans hs h₁ h₂) h₃'

end ModifiedCartan
#print axioms ModifiedCartan.HasSmallRectangleCrosses.two_moving_box_anchors_exponential