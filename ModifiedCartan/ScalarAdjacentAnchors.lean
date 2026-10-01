import ModifiedCartan.ScalarRectangleCrosses

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem exp_neg_mul_tendsto_zero {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) : Tendsto (fun ν => Real.exp (-δ * s ν)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.Tendsto.const_mul_atTop hδ hs)

/-- The actual physical anchors on independently selected good horizontal
lines of adjacent rectangles have distance tending to zero. A third selected
vertical line supplies their geometric connection. Auxiliary to `thm:A` (b). -/
theorem HasSmallRectangleCrosses.adjacent_horizontal_anchors
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}
    (h : HasSmallRectangleCrosses f r s Ω)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    {R S : ComplexRect} (hR : R.closed ⊆ Ω) (hS : S.closed ⊆ Ω) (hRS : R.Overlaps S)
    {δR δS : ℝ} (hδR : 0 < δR) (hδS : 0 < δS) {yR yS : ℕ → ℝ}
    (hH₁ : ∀ᶠ ν in atTop, yR ν ∈ Icc R.bottom R.top ∧
      ∀ t ∈ Icc R.left R.right,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yR ν⟩ : ℂ)) ≤ Real.exp (-δR * s ν))
    (hH₂ : ∀ᶠ ν in atTop, yS ν ∈ Icc S.bottom S.top ∧
      ∀ t ∈ Icc S.left S.right,
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yS ν⟩ : ℂ)) ≤ Real.exp (-δS * s ν)) :
    Tendsto (fun ν => ‖scalarCurveSphere f ((r ν : ℂ) * (⟨R.left, yR ν⟩ : ℂ)) -
      scalarCurveSphere f ((r ν : ℂ) * (⟨S.left, yS ν⟩ : ℂ))‖) atTop (𝓝 0) := by
  let B := R.verticalBridge S hRS
  have hBΩ : B.closed ⊆ Ω := (ComplexRect.verticalBridge_closed_subset hRS).trans (union_subset hR hS)
  obtain ⟨δB, hδB, hB⟩ := h B hBΩ
  let C : ℕ → ℝ := fun ν => Real.exp (-δR * s ν) + Real.exp (-δS * s ν) + Real.exp (-δB * s ν)
  let L : ℝ := (R.right - R.left) + (max R.top S.top - min R.bottom S.bottom) + (S.right - S.left)
  have hC : Tendsto C atTop (𝓝 0) := by
    simpa only [zero_add] using ((exp_neg_mul_tendsto_zero hs hδR).add
      (exp_neg_mul_tendsto_zero hs hδS)).add (exp_neg_mul_tendsto_zero hs hδB)
  have hlim : Tendsto (fun ν => C ν * L) atTop (𝓝 0) := by simpa only [zero_mul] using hC.mul_const L
  apply squeeze_zero' (Eventually.of_forall (fun ν => norm_nonneg _)) _ hlim
  filter_upwards [hH₁, hH₂, hB, hr.eventually_ge_atTop 0] with ν h₁ h₂ hBν hrν
  obtain ⟨x, hx, y, hy, _, hV⟩ := hBν
  have hxR : x ∈ Icc R.left R.right :=
    ⟨(le_max_left _ _).trans hx.1, hx.2.trans (min_le_left _ _)⟩
  have hxS : x ∈ Icc S.left S.right :=
    ⟨(le_max_right _ _).trans hx.1, hx.2.trans (min_le_right _ _)⟩
  have hCν : 0 ≤ C ν := by dsimp only [C]; positivity
  have hRC : Real.exp (-δR * s ν) ≤ C ν := by
    dsimp only [C]
    linarith [Real.exp_pos (-δS * s ν), Real.exp_pos (-δB * s ν)]
  have hSC : Real.exp (-δS * s ν) ≤ C ν := by
    dsimp only [C]
    linarith [Real.exp_pos (-δR * s ν), Real.exp_pos (-δB * s ν)]
  have hBC : Real.exp (-δB * s ν) ≤ C ν := by
    dsimp only [C]
    linarith [Real.exp_pos (-δR * s ν), Real.exp_pos (-δS * s ν)]
  exact scalar_curve_rectangle_bridge_diameter f hrν hCν hxR hxS h₁.1 h₂.1
    (fun t ht => (h₁.2 t ht).trans hRC) (fun t ht => (h₂.2 t ht).trans hSC)
    (fun t ht => (hV t ht).trans hBC)
    ⟨le_rfl, R.horizontal_pos.le⟩ ⟨le_rfl, S.horizontal_pos.le⟩

end ModifiedCartan
#print axioms ModifiedCartan.HasSmallRectangleCrosses.adjacent_horizontal_anchors
