import ModifiedCartan.PolynomialVerticalLine
import ModifiedCartan.ScalarSharpComparableLines
import ModifiedCartan.ClassicalWeakGradient

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Polynomial vertical good lines transfer bounds on constructed horizontal
segments to a smooth local logarithmic limit. Subsequences and segment heights
may depend on the width. Auxiliary to target identification in `thm:A` (b). -/
theorem LocalLpConvergence.polynomial_limit_le_of_horizontal_caps
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    {P : ℕ → Polynomial ℂ} (hP : ∀ ν, P ν ≠ 0) {s : ℕ → ℝ} {u : ℂ → ℝ}
    (hlog : LocalLpConvergence 1 Ω (fun ν w => (s ν)⁻¹ * Real.log ‖(P ν).eval w‖) u)
    (hs : Tendsto s atTop atTop) (hu : ContDiffOn ℝ 1 u Ω)
    {z : ℂ} (hz : z ∈ Ω) {B ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hcaps : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∃ y : ℕ → ℝ, ∀ᶠ ν in atTop,
        y ν ∈ Icc (z.im - 2 * ε) (z.im + 2 * ε) ∧
        ∀ t ∈ Icc (z.re - ε) (z.re + ε),
          ‖(P (ns ν)).eval (⟨t, y ν⟩ : ℂ)‖ ≤ Real.exp (B * s (ns ν))) :
    u z ≤ B := by
  by_contra hn
  have hBu : B < u z := lt_of_not_ge hn
  let η := (u z - B) / 2
  have hη : 0 < η := by dsimp only [η]; linarith
  have hBuη : B + η < u z := by dsimp only [η]; linarith
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ Ω ∧ B + η < u w :=
    (show ∀ᶠ w in 𝓝 z, w ∈ Ω from hΩ.mem_nhds hz).and
      ((hu.continuousOn.continuousAt (hΩ.mem_nhds hz)).eventually
      (lt_mem_nhds hBuη))
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  let ε := min ε₀ (d / 4)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεd : ε ≤ d / 4 := min_le_right _ _
  have h3ε : ε + 2 * ε < d := by linarith
  have hrect : ∀ w ∈ complexClosedRectangle (z.re - ε) (z.re + ε)
      (z.im - 2 * ε) (z.im + 2 * ε), w ∈ Ω ∧ B + η < u w := by
    intro w hw
    have hb : w ∈ closedBall z (ε + 2 * ε) :=
      ComplexRect.box_closed_subset_closedBall z hε (by positivity) hw
    exact hball w ((closedBall_subset_ball h3ε) hb)
  have hK : complexClosedRectangle (z.re - ε) (z.re + ε)
      (z.im - 2 * ε) (z.im + 2 * ε) ⊆ Ω := fun w hw => (hrect w hw).1
  obtain ⟨ns, hns, y, hy⟩ := hcaps ε hε (min_le_left _ _)
  have hg := contDiffOn_hasWeakComplexGradient hΩ hu
  have hV := (hlog.comp_tendsto hns.tendsto_atTop).polynomial_good_vertical_lines hΩ hc
    (fun ν => hP (ns ν)) (hs.comp hns.tendsto_atTop) hg
    (show z.im - 2 * ε < z.im + 2 * ε by linarith)
    (show z.re - ε < z.re + ε by linarith) hK
    (fun x hx t ht => hasDerivAt_vertical_of_differentiableAt
      ((hu.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds (hK ⟨hx, ht⟩)))) hη
  obtain ⟨ν, hν, hVν, hsν⟩ := (hy.and (hV.and
    ((hs.comp hns.tendsto_atTop).eventually_gt_atTop 0))).exists
  obtain ⟨x, hx, hnonzero, herr⟩ := hVν
  have hlower := (hrect (⟨x, y ν⟩ : ℂ) ⟨hx, hν.1⟩).2
  have he := (abs_lt.mp (herr (y ν) hν.1)).1
  have hb := Real.log_le_log (norm_pos_iff.mpr (hnonzero (y ν))) (hν.2 x hx)
  rw [Real.log_exp] at hb
  have hb' : (s (ns ν))⁻¹ * Real.log ‖(P (ns ν)).eval (⟨x, y ν⟩ : ℂ)‖ ≤ B := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hsν).2 hb
  dsimp only [polynomialLogError] at he
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.LocalLpConvergence.polynomial_limit_le_of_horizontal_caps
