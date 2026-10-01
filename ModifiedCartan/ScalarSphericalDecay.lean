import ModifiedCartan.ArbitraryScaleHypotheses
import ModifiedCartan.ScalarSphericalSpeed
import ModifiedCartan.ArbitraryRadiusData
import ModifiedCartan.SmallPolynomialLog

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- A monic polynomial with bounded roots and degree negligible on scale s
has the required uniform exponential upper bound; auxiliary to `thm:A` (b). -/
theorem small_monic_polynomial_uniform_exp_bound (P : ℕ → Polynomial ℂ)
    (hP : ∀ ν, (P ν).Monic) (hroots : ∀ ν a, (P ν).eval a = 0 → ‖a‖ ≤ 64)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    ∀ᶠ ν in atTop, ∀ z ∈ closedBall (0 : ℂ) R,
      ‖(P ν).eval z‖ ≤ Real.exp (ε * s ν) := by
  have hlim := hm.mul_const (Real.log (R + 64))
  simp only [zero_mul] at hlim
  filter_upwards [hs.eventually_gt_atTop 0, hlim.eventually_lt_const hε] with ν hsν hν
  intro z hz
  have hsmall : ((P ν).natDegree : ℝ) * Real.log (R + 64) < ε * s ν := by
    apply (div_lt_iff₀ hsν).mp
    simpa only [div_mul_eq_mul_div] using hν
  exact (Real.le_exp_log _).trans (Real.exp_le_exp.mpr
    ((log_norm_monic_polynomial_le_of_roots_bounded (P ν) (hP ν) (hroots ν) hR hz).trans hsmall.le))

theorem scalarSphericalSpeed_le_exp {g : Index 1 → ℂ → ℂ} {z : ℂ} {b η : ℝ}
    (hne : (fun j => g j z) ≠ 0)
    (hW : ‖FewInflection.wronskian 1 g z‖ ≤ Real.exp b)
    (hg : η ≤ Real.log (euclideanNorm (fun j => g j z))) :
    scalarSphericalSpeed g z ≤ Real.exp (b - 2 * η) := by
  have hpos := euclideanNorm_pos hne
  have he : Real.exp (2 * Real.log (euclideanNorm (fun j => g j z))) =
      euclideanNorm (fun j => g j z) ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hpos, pow_two]
  have hden : Real.exp (2 * η) ≤ euclideanNorm (fun j => g j z) ^ 2 := by
    rw [← he]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    scalarSphericalSpeed g z ≤ Real.exp b / euclideanNorm (fun j => g j z) ^ 2 :=
      div_le_div_of_nonneg_right hW (sq_nonneg _)
    _ ≤ Real.exp b / Real.exp (2 * η) :=
      div_le_div_of_nonneg_left (Real.exp_pos b).le (Real.exp_pos _) hden
    _ = Real.exp (b - 2 * η) := (Real.exp_sub _ _).symm

/-- The actual normalized Wronskian supplies a uniform numerator bound. -/
theorem ArbitraryRadiusLimitData.scalar_rescaled_wronskian_exp_bound
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (hr : Tendsto r atTop atTop)
    (hN : Tendsto (fun ν => ValueDistribution.logCounting (FewInflection.wronskian 1 f.coord)
      (0 : WithTop ℂ) (256 * r (d.subseq ν)) / characteristic f (r (d.subseq ν))) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 4,
      ‖FewInflection.wronskian 1 (rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν)) z‖
        ≤ Real.exp (ε * characteristic f (r (d.subseq ν))) := by
  have hm := rescaledWronskianPolynomial_degree_small f hlin
    (hr.comp d.strictMono.tendsto_atTop) d.scale_tendsto hN
  have hp := small_monic_polynomial_uniform_exp_bound
    (fun ν => rescaledWronskianPolynomial f (r (d.subseq ν)))
    (fun ν => rescaledWronskianPolynomial_monic f (r (d.subseq ν)))
    (fun ν a ha => (show ‖a‖ < 64 by simpa only [mem_ball, dist_zero_right] using
      rescaledWronskianPolynomial_roots_mem f (r (d.subseq ν)) ha).le)
    d.scale_tendsto hm hε (by norm_num : (0 : ℝ) ≤ 4)
  filter_upwards [hp, d.replacement.gauge_wronskian] with ν hν hgν
  intro z hz
  rw [hgν z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) hz)]
  exact hν z (ball_subset_closedBall hz)

/-- Exponential spherical-speed decay wherever the actual reduced norm is large.
The numerator is derived from small ramification, not postulated. `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalar_rescaled_speed_exp_bound
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (hr : Tendsto r atTop atTop)
    (hN : Tendsto (fun ν => ValueDistribution.logCounting (FewInflection.wronskian 1 f.coord)
      (0 : WithTop ℂ) (256 * r (d.subseq ν)) / characteristic f (r (d.subseq ν))) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 4, ∀ η : ℝ,
      η * characteristic f (r (d.subseq ν)) ≤ Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z)) →
      scalarSphericalSpeed (rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν)) z ≤
        Real.exp ((ε - 2 * η) * characteristic f (r (d.subseq ν))) := by
  filter_upwards [d.scalar_rescaled_wronskian_exp_bound hlin hr hN hε] with ν hν
  intro z hz η hη
  have hne : (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z) ≠ 0 := by
    obtain ⟨j, hj⟩ := rescaledRepresentation_reduced f (r (d.subseq ν)) (d.gauge ν) z
    intro he
    exact hj (congrFun he j)
  have hh := scalarSphericalSpeed_le_exp hne (hν z hz) hη
  convert hh using 1
  congr 1
  ring

/-- The original small-ramification and growth-index hypotheses supply every
numerator estimate for the actual physical curve. No speed assumption is added. -/
theorem ArbitraryRadiusLimitData.scalar_physical_speed_exp_bound
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 4, ∀ η : ℝ,
      η * characteristic f (r (d.subseq ν)) ≤ Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r (d.subseq ν)) (d.gauge ν) j z)) →
      r (d.subseq ν) * scalarSphericalSpeed f.coord ((r (d.subseq ν) : ℂ) * z) ≤
        Real.exp ((ε - 2 * η) * characteristic f (r (d.subseq ν))) := by
  have ht := hr.comp d.strictMono.tendsto_atTop
  obtain ⟨C, hC, hsc⟩ := characteristic_arbitrary_scale_hypotheses f htrans hsmall
    hρ (ε := ρ / 2) (by positivity) (by linarith) hl hu ht
  have hsc1 := hsc 1 zero_lt_one
  simp only [arbitraryScaleWeight_one, one_mul] at hsc1
  have hN := hsc1.2.2.2.2
  filter_upwards [d.scalar_rescaled_speed_exp_bound hlin hr hN hε,
    d.replacement.gauge_analytic, ht.eventually_gt_atTop 0] with ν hν hA htν
  intro z hz η hη
  change 0 < r (d.subseq ν) at htν
  have hh := hν z hz η hη
  rw [scalarSphericalSpeed_rescaled f (r (d.subseq ν))
    (hA z ((ball_subset_ball (by norm_num : (4 : ℝ) ≤ 64)) hz)), abs_of_pos htν] at hh
  exact hh
end
end ModifiedCartan
#print axioms ModifiedCartan.small_monic_polynomial_uniform_exp_bound
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_rescaled_speed_exp_bound

#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_physical_speed_exp_bound


