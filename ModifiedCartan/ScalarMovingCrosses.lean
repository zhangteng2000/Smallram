import ModifiedCartan.ScalarPeakDisks
import ModifiedCartan.ScalarRectangleCrosses

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Literal physical speed estimates on the horizontal and vertical segments
of a selected cross; auxiliary to LaTeX thm:A (b). -/
def ScalarGoodCross (f : Curve 1) (r s δ : ℝ) (R : ComplexRect) : Prop :=
  ∃ x ∈ Icc R.left R.right, ∃ y ∈ Icc R.bottom R.top,
    (∀ t ∈ Icc R.left R.right,
      r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨t, y⟩ : ℂ)) ≤ Real.exp (-δ * s)) ∧
    (∀ t ∈ Icc R.bottom R.top,
      r * scalarSphericalSpeed f.coord ((r : ℂ) * (⟨x, t⟩ : ℂ)) ≤ Real.exp (-δ * s))

theorem ScalarGoodCross.mono_rate {f : Curve 1} {r s δ ε : ℝ} {R : ComplexRect}
    (h : ScalarGoodCross f r s δ R) (hs : 0 ≤ s) (hεδ : ε ≤ δ) :
    ScalarGoodCross f r s ε R := by
  obtain ⟨x, hx, y, hy, hH, hV⟩ := h
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hεδ) hs)
  exact ⟨x, hx, y, hy, fun t ht => (hH t ht).trans he, fun t ht => (hV t ht).trans he⟩

/-- Wide and narrow fixed rectangles supply a full cross in a nearby moving
square, without any pointwise control off the selected lines. -/
theorem scalarGoodCross_box_of_fixed {f : Curve 1} {r s δ : ℝ} {a b : ℂ}
    {ε : ℝ} (hε : 0 < ε) (hab : ‖a - b‖ ≤ ε / 2)
    (hH : ScalarGoodCross f r s δ
      (ComplexRect.box b (2 * ε) (ε / 2) (by positivity) (half_pos hε)))
    (hV : ScalarGoodCross f r s δ
      (ComplexRect.box b (ε / 2) (2 * ε) (half_pos hε) (by positivity))) :
    ScalarGoodCross f r s δ (ComplexRect.box a ε ε hε hε) := by
  obtain ⟨_, _, y, hy, hH, _⟩ := hH
  obtain ⟨x, hx, _, _, _, hV⟩ := hV
  have hre := (Complex.abs_re_le_norm (a - b)).trans hab
  have him := (Complex.abs_im_le_norm (a - b)).trans hab
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  change b.im - ε / 2 ≤ y ∧ y ≤ b.im + ε / 2 at hy
  change b.re - ε / 2 ≤ x ∧ x ≤ b.re + ε / 2 at hx
  refine ⟨x, ⟨by dsimp [ComplexRect.box]; linarith [hx.1, hre.2],
    by dsimp [ComplexRect.box]; linarith [hx.2, hre.1]⟩,
    y, ⟨by dsimp [ComplexRect.box]; linarith [hy.1, him.2],
    by dsimp [ComplexRect.box]; linarith [hy.2, him.1]⟩, ?_, ?_⟩
  · intro t ht
    apply hH t
    change a.re - ε ≤ t ∧ t ≤ a.re + ε at ht
    change b.re - 2 * ε ≤ t ∧ t ≤ b.re + 2 * ε
    constructor <;> linarith [ht.1, ht.2, hre.1, hre.2]
  · intro t ht
    apply hV t
    change a.im - ε ≤ t ∧ t ≤ a.im + ε at ht
    change b.im - 2 * ε ≤ t ∧ t ≤ b.im + 2 * ε
    constructor <;> linarith [ht.1, ht.2, him.1, him.2]

/-- Fixed-domain cross estimates persist in squares whose centers converge.
The positive rate is constructed from two fixed rectangles. -/
theorem HasSmallRectangleCrosses.moving_box
    {f : Curve 1} {r s : ℕ → ℝ} {Ω : Set ℂ}
    (h : HasSmallRectangleCrosses f r s Ω) (hs : Tendsto s atTop atTop)
    {a : ℕ → ℂ} {b : ℂ} (ha : Tendsto a atTop (𝓝 b))
    {ε : ℝ} (hε : 0 < ε) (hball : closedBall b (4 * ε) ⊆ Ω) :
    ∃ δ > 0, ∀ᶠ ν in atTop,
      ScalarGoodCross f (r ν) (s ν) δ (ComplexRect.box (a ν) ε ε hε hε) := by
  let H := ComplexRect.box b (2 * ε) (ε / 2) (by positivity) (half_pos hε)
  let V := ComplexRect.box b (ε / 2) (2 * ε) (half_pos hε) (by positivity)
  have hHΩ : H.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall b (by positivity) (half_pos hε)).trans
      ((closedBall_subset_closedBall (by linarith : 2 * ε + ε / 2 ≤ 4 * ε)).trans hball)
  have hVΩ : V.closed ⊆ Ω :=
    (ComplexRect.box_closed_subset_closedBall b (half_pos hε) (by positivity)).trans
      ((closedBall_subset_closedBall (by linarith : ε / 2 + 2 * ε ≤ 4 * ε)).trans hball)
  obtain ⟨δH, hδH, hH⟩ := h H hHΩ
  obtain ⟨δV, hδV, hV⟩ := h V hVΩ
  have hnear : ∀ᶠ ν in atTop, ‖a ν - b‖ ≤ ε / 2 := by
    have hh : Tendsto (fun ν => ‖a ν - b‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using (ha.sub_const b).norm
    simpa only [sub_self, norm_zero] using (hh.eventually_lt_const (half_pos hε)).mono
      (fun _ hh => hh.le)
  refine ⟨min δH δV, lt_min hδH hδV, ?_⟩
  filter_upwards [hH, hV, hnear, hs.eventually_ge_atTop 0] with ν hHν hVν hnearν hsν
  exact scalarGoodCross_box_of_fixed hε hnearν
    ((show ScalarGoodCross f (r ν) (s ν) δH H from hHν).mono_rate hsν (min_le_left _ _))
    ((show ScalarGoodCross f (r ν) (s ν) δV V from hVν).mono_rate hsν (min_le_right _ _))

end ModifiedCartan
#print axioms ModifiedCartan.scalarGoodCross_box_of_fixed
#print axioms ModifiedCartan.HasSmallRectangleCrosses.moving_box