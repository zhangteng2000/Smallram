import ModifiedCartan.ScalarMovingCrosses
import ModifiedCartan.ScalarAnchorExponential

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A selected horizontal line in a moving square is exponentially close to
one in a smaller fixed square. A fixed vertical strip gives the connection. -/
theorem HasSmallRectangleCrosses.moving_box_anchors_exponential
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}
    (h : HasSmallRectangleCrosses f r s Ω)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    {a : ℕ → ℂ} {b : ℂ} (ha : Tendsto a atTop (𝓝 b))
    {ε : ℝ} (hε : 0 < ε) (hball : closedBall b (4 * ε) ⊆ Ω)
    {δR δS : ℝ} (hδR : 0 < δR) (hδS : 0 < δS) {yR yS : ℕ → ℝ}
    (hH₁ : ∀ᶠ ν in atTop, yR ν ∈ Icc ((a ν).im - ε) ((a ν).im + ε) ∧
      ∀ t ∈ Icc ((a ν).re - ε) ((a ν).re + ε),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yR ν⟩ : ℂ)) ≤ Real.exp (-δR * s ν))
    (hH₂ : ∀ᶠ ν in atTop, yS ν ∈ Icc (b.im - ε / 2) (b.im + ε / 2) ∧
      ∀ t ∈ Icc (b.re - ε / 2) (b.re + ε / 2),
        r ν * scalarSphericalSpeed f.coord ((r ν : ℂ) * (⟨t, yS ν⟩ : ℂ)) ≤ Real.exp (-δS * s ν)) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ᶠ ν in atTop,
      ‖scalarCurveSphere f ((r ν : ℂ) * (⟨(a ν).re - ε, yR ν⟩ : ℂ)) -
        scalarCurveSphere f ((r ν : ℂ) * (⟨b.re - ε / 2, yS ν⟩ : ℂ))‖ ≤
          C * Real.exp (-δ * s ν) := by
  let B := ComplexRect.box b (ε / 4) (2 * ε) (by positivity) (by positivity)
  have hBΩ : B.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall b (by positivity) (by positivity)).trans
      ((closedBall_subset_closedBall (by linarith : ε / 4 + 2 * ε ≤ 4 * ε)).trans hball)
  obtain ⟨δB, hδB, hB⟩ := h B hBΩ
  let δ := min δR (min δS δB)
  have hδ : 0 < δ := lt_min hδR (lt_min hδS hδB)
  have hn : Tendsto (fun ν => ‖a ν - b‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (ha.sub_const b).norm
  refine ⟨δ, hδ, 7 * ε, by positivity, ?_⟩
  filter_upwards [hH₁, hH₂, hB, hr.eventually_ge_atTop 0, hs.eventually_ge_atTop 0,
    hn.eventually_lt_const (half_pos hε)] with ν h₁ h₂ hBν hrν hsν hnν
  obtain ⟨x, hx, _, _, _, hV⟩ := hBν
  change b.re - ε / 4 ≤ x ∧ x ≤ b.re + ε / 4 at hx
  have hre := (Complex.abs_re_le_norm (a ν - b)).trans hnν.le
  have him := (Complex.abs_im_le_norm (a ν - b)).trans hnν.le
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  have hxR : x ∈ Icc ((a ν).re - ε) ((a ν).re + ε) :=
    ⟨by linarith [hx.1, hre.2], by linarith [hx.2, hre.1]⟩
  have hxS : x ∈ Icc (b.re - ε / 2) (b.re + ε / 2) :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlo : b.im - 2 * ε ≤ min ((a ν).im - ε) (b.im - ε / 2) :=
    le_min (by linarith [him.1]) (by linarith)
  have hhi : max ((a ν).im + ε) (b.im + ε / 2) ≤ b.im + 2 * ε :=
    max_le (by linarith [him.2]) (by linarith)
  have hmono {η : ℝ} (hη : δ ≤ η) : Real.exp (-η * s ν) ≤ Real.exp (-δ * s ν) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hη) hsν)
  have hRC := hmono (show δ ≤ δR from min_le_left _ _)
  have hSC := hmono (show δ ≤ δS from (min_le_right _ _).trans (min_le_left _ _))
  have hBC := hmono (show δ ≤ δB from (min_le_right _ _).trans (min_le_right _ _))
  have hh := scalar_curve_rectangle_bridge_diameter f hrν (Real.exp_pos (-δ * s ν)).le
    hxR hxS h₁.1 h₂.1 (fun t ht => (h₁.2 t ht).trans hRC)
    (fun t ht => (h₂.2 t ht).trans hSC)
    (fun t ht => (hV t ⟨hlo.trans ht.1, ht.2.trans hhi⟩).trans hBC)
    (show (a ν).re - ε ∈ Icc ((a ν).re - ε) ((a ν).re + ε) from ⟨le_rfl, by linarith⟩)
    (show b.re - ε / 2 ∈ Icc (b.re - ε / 2) (b.re + ε / 2) from ⟨le_rfl, by linarith⟩)
  have hL : ((a ν).re + ε - ((a ν).re - ε)) +
      (max ((a ν).im + ε) (b.im + ε / 2) - min ((a ν).im - ε) (b.im - ε / 2)) +
      (b.re + ε / 2 - (b.re - ε / 2)) ≤ 7 * ε := by linarith
  exact hh.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le)

end ModifiedCartan
#print axioms ModifiedCartan.HasSmallRectangleCrosses.moving_box_anchors_exponential