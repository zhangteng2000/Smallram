import ModifiedCartan.ScalarFixedRateConnections

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A moving endpoint with a converging positive width can be attached to
a fixed rectangle without decreasing the specified rate. -/
theorem HasRectangleCrossesAtRate.variable_box_anchors
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ} {κ : ℝ}
    (h : HasRectangleCrossesAtRate f r s Ω κ) (hr : Tendsto r atTop atTop)
    {a : ℕ → ℂ} {b : ℂ} (ha : Tendsto a atTop (𝓝 b))
    {w : ℕ → ℝ} {ε : ℝ} (hw : Tendsto w atTop (𝓝 ε)) (hε : 0 < ε)
    (hball : closedBall b (4 * ε) ⊆ Ω) {yR yS : ℕ → ℝ}
    (hH₁ : ∀ᶠ ν in atTop, yR ν ∈ Icc ((a ν).im - w ν) ((a ν).im + w ν) ∧
      ∀ t ∈ Icc ((a ν).re - w ν) ((a ν).re + w ν),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yR ν⟩ : ℂ)) ≤ Real.exp (-κ * s ν))
    (hH₂ : ∀ᶠ ν in atTop, yS ν ∈ Icc (b.im - ε / 2) (b.im + ε / 2) ∧
      ∀ t ∈ Icc (b.re - ε / 2) (b.re + ε / 2),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yS ν⟩ : ℂ)) ≤ Real.exp (-κ * s ν)) :
    ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f ((r ν : ℂ) * (⟨(a ν).re - w ν, yR ν⟩ : ℂ)) -
        scalarCurveSphere f ((r ν : ℂ) * (⟨b.re - ε / 2, yS ν⟩ : ℂ))‖ ≤
          (8 * ε) * Real.exp (-κ * s ν) := by
  let B := ComplexRect.box b (ε / 4) (2 * ε) (by positivity) (by positivity)
  have hBΩ : B.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall b (by positivity) (by positivity)).trans
      ((closedBall_subset_closedBall (by linarith : ε / 4 + 2 * ε ≤ 4 * ε)).trans hball)
  have hn : Tendsto (fun ν => ‖a ν - b‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (ha.sub_const b).norm
  filter_upwards [hH₁, hH₂, h B hBΩ, hr.eventually_ge_atTop 0,
    hn.eventually_lt_const (by positivity : 0 < ε / 4),
    hw.eventually_const_lt (by linarith : 3 * ε / 4 < ε),
    hw.eventually_lt_const (by linarith : ε < 5 * ε / 4)]
    with ν h₁ h₂ hBν hrν hnν hwlo hwhi
  obtain ⟨x, hx, _, _, _, hV⟩ := hBν
  change b.re - ε / 4 ≤ x ∧ x ≤ b.re + ε / 4 at hx
  have hre := (Complex.abs_re_le_norm (a ν - b)).trans hnν.le
  have him := (Complex.abs_im_le_norm (a ν - b)).trans hnν.le
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  have hxR : x ∈ Icc ((a ν).re - w ν) ((a ν).re + w ν) :=
    ⟨by linarith [hx.1, hre.2], by linarith [hx.2, hre.1]⟩
  have hxS : x ∈ Icc (b.re - ε / 2) (b.re + ε / 2) :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlo : b.im - 2 * ε ≤ min ((a ν).im - w ν) (b.im - ε / 2) :=
    le_min (by linarith [him.1]) (by linarith)
  have hhi : max ((a ν).im + w ν) (b.im + ε / 2) ≤ b.im + 2 * ε :=
    max_le (by linarith [him.2]) (by linarith)
  have hh := scalar_curve_rectangle_bridge_diameter f hrν (Real.exp_pos (-κ * s ν)).le
    hxR hxS h₁.1 h₂.1 h₁.2 h₂.2
    (fun t ht => hV t ⟨hlo.trans ht.1, ht.2.trans hhi⟩)
    (show (a ν).re - w ν ∈ Icc ((a ν).re - w ν) ((a ν).re + w ν) from ⟨le_rfl, by linarith⟩)
    (show b.re - ε / 2 ∈ Icc (b.re - ε / 2) (b.re + ε / 2) from ⟨le_rfl, by linarith⟩)
  have hL : ((a ν).re + w ν - ((a ν).re - w ν)) +
      (max ((a ν).im + w ν) (b.im + ε / 2) - min ((a ν).im - w ν) (b.im - ε / 2)) +
      (b.re + ε / 2 - (b.re - ε / 2)) ≤ 8 * ε := by linarith
  exact hh.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le)

end ModifiedCartan
#print axioms ModifiedCartan.HasRectangleCrossesAtRate.variable_box_anchors
