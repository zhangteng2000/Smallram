import ModifiedCartan.ScalarFixedRateMovingAnchors

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Two moving endpoint segments in a connected level region retain its
specified rate, including when both widths vary. -/
theorem HasRectangleCrossesAtRate.two_variable_box_anchors
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (h : HasRectangleCrossesAtRate f r s Ω κ) (hκ : 0 < κ)
    (hr : Tendsto r atTop atTop) (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    {a b : ℕ → ℂ} {a₀ b₀ : ℂ} (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    {w v : ℕ → ℝ} {ε θ : ℝ} (hw : Tendsto w atTop (𝓝 ε)) (hv : Tendsto v atTop (𝓝 θ))
    (hε : 0 < ε) (hθ : 0 < θ)
    (hballA : closedBall a₀ (4 * ε) ⊆ Ω) (hballB : closedBall b₀ (4 * θ) ⊆ Ω)
    {yA yB : ℕ → ℝ}
    (hA : ∀ᶠ ν in atTop, yA ν ∈ Icc ((a ν).im - w ν) ((a ν).im + w ν) ∧
      ∀ t ∈ Icc ((a ν).re - w ν) ((a ν).re + w ν),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yA ν⟩ : ℂ)) ≤ Real.exp (-κ * s ν))
    (hB : ∀ᶠ ν in atTop, yB ν ∈ Icc ((b ν).im - v ν) ((b ν).im + v ν) ∧
      ∀ t ∈ Icc ((b ν).re - v ν) ((b ν).re + v ν),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yB ν⟩ : ℂ)) ≤ Real.exp (-κ * s ν)) :
    ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f ((r ν : ℂ) * (⟨(a ν).re - w ν, yA ν⟩ : ℂ)) -
        scalarCurveSphere f ((r ν : ℂ) * (⟨(b ν).re - v ν, yB ν⟩ : ℂ))‖ ≤
          C * Real.exp (-κ * s ν) := by
  obtain ⟨q, hq⟩ := h.exists_horizontal_selection hκ
  let A := ComplexRect.box a₀ (ε / 2) (ε / 2) (half_pos hε) (half_pos hε)
  let B := ComplexRect.box b₀ (θ / 2) (θ / 2) (half_pos hθ) (half_pos hθ)
  have hAΩ : A.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall a₀ (half_pos hε) (half_pos hε)).trans
      ((closedBall_subset_closedBall (by linarith : ε / 2 + ε / 2 ≤ 4 * ε)).trans hballA)
  have hBΩ : B.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall b₀ (half_pos hθ) (half_pos hθ)).trans
      ((closedBall_subset_closedBall (by linarith : θ / 2 + θ / 2 ≤ 4 * θ)).trans hballB)
  have hgA := q.good ⟨A, hAΩ⟩
  have hgB := q.good ⟨B, hBΩ⟩
  rw [hq] at hgA hgB
  have h₁ := h.variable_box_anchors hr ha hw hε hballA hA hgA
  obtain ⟨C, hC, h₂⟩ := q.anchors_close_at_rate hq h hr hΩ hc ⟨A, hAΩ⟩ ⟨B, hBΩ⟩
  have h₃ := h.variable_box_anchors hr hb hv hθ hballB hB hgB
  refine ⟨8 * ε + C + 8 * θ, by positivity, ?_⟩
  filter_upwards [h₁, h₂, h₃] with ν h₁ν h₂ν h₃ν
  have h₃' : ‖q.anchor ⟨B, hBΩ⟩ ν -
      scalarCurveSphere f ((r ν : ℂ) * (⟨(b ν).re - v ν, yB ν⟩ : ℂ))‖ ≤
        (8 * θ) * Real.exp (-κ * s ν) := by
    simpa only [ScalarHorizontalSelection.anchor, B, ComplexRect.box, norm_sub_rev] using h₃ν
  calc
    _ ≤ ‖scalarCurveSphere f ((r ν : ℂ) * (⟨(a ν).re - w ν, yA ν⟩ : ℂ)) - q.anchor ⟨A, hAΩ⟩ ν‖ +
        ‖q.anchor ⟨A, hAΩ⟩ ν - q.anchor ⟨B, hBΩ⟩ ν‖ +
        ‖q.anchor ⟨B, hBΩ⟩ ν - scalarCurveSphere f ((r ν : ℂ) * (⟨(b ν).re - v ν, yB ν⟩ : ℂ))‖ := by
      have hh₁ := norm_sub_le_norm_sub_add_norm_sub
        (scalarCurveSphere f ((r ν : ℂ) * (⟨(a ν).re - w ν, yA ν⟩ : ℂ)))
        (q.anchor ⟨A, hAΩ⟩ ν) (q.anchor ⟨B, hBΩ⟩ ν)
      have hh₂ := norm_sub_le_norm_sub_add_norm_sub
        (scalarCurveSphere f ((r ν : ℂ) * (⟨(a ν).re - w ν, yA ν⟩ : ℂ)))
        (q.anchor ⟨B, hBΩ⟩ ν)
        (scalarCurveSphere f ((r ν : ℂ) * (⟨(b ν).re - v ν, yB ν⟩ : ℂ)))
      linarith
    _ ≤ (8 * ε) * Real.exp (-κ * s ν) + C * Real.exp (-κ * s ν) +
        (8 * θ) * Real.exp (-κ * s ν) := add_le_add (add_le_add h₁ν h₂ν) h₃'
    _ = _ := by ring

end ModifiedCartan
#print axioms ModifiedCartan.HasRectangleCrossesAtRate.two_variable_box_anchors
