import ModifiedCartan.ScalarComparablePeakLimits
import ModifiedCartan.ScalarSmoothTargetBound

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- At every smooth point in its own positive sector, the actual target
component has logarithmic limit at most the negative norm profile.
Auxiliary to LaTeX `thm:A` (b). -/
theorem scalar_target_component_le_neg_norm_of_smooth
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    (hstep : Tendsto (fun ν => a (ν + 1) - a ν) atTop (𝓝 0))
    (q : ScalarDyadicPeakTargetData f a ρ)
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    {c : ℕ → ℝ} (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hclim : Tendsto c atTop (𝓝 c₀))
    {a₀ : ℂ} (halim : Tendsto (fun ν => a (n ν)) atTop (𝓝 a₀))
    (d : ArbitraryRadiusLimitData f (fun ν => c ν * (2 : ℝ) ^ n ν) ρ)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hΩball : Ω ⊆ ball (0 : ℂ) 4)
    {u : ℂ → ℝ} (hsmooth : ContDiffOn ℝ 1 u Ω)
    (hP : ∀ ν, polynomialMatrixGauge (d.polynomial ν)
      (scalarTargetUnitary q.target : Matrix (Index 1) (Index 1) ℂ) 0 ≠ 0)
    (hlog : LocalLpConvergence 1 Ω
      (fun ν w => (characteristic f (c (d.subseq ν) * (2 : ℝ) ^ n (d.subseq ν)))⁻¹ *
        Real.log ‖(polynomialMatrixGauge (d.polynomial ν)
          (scalarTargetUnitary q.target : Matrix (Index 1) (Index 1) ℂ) 0).eval w‖) u)
    {z : ℂ} (hzΩ : z ∈ Ω)
    (hz : z ∈ scalarPositiveChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ))
    (hA : (d.U z).toReal ≤ d.A) :
    u z ≤ -(d.U z).toReal := by
  obtain ⟨ha₀norm, hroot⟩ := d.scalar_comparable_peak_limit
    f hlin htrans hsmall hρ hl hu hm ha hpeak hn hc halim
  have ha₀ : a₀ ≠ 0 := norm_ne_zero_iff.mp (by rw [ha₀norm]; norm_num)
  have hUpos := d.scalar_norm_positiveChart_pos hρ ha₀ _ hroot z hz
  by_contra hh
  have hgap : -(d.U z).toReal < u z := lt_of_not_ge hh
  have hmax : max 0 ((d.U z).toReal - u z) < 2 * (d.U z).toReal := by
    rw [max_lt_iff]; constructor <;> linarith
  obtain ⟨κ, hκlow, hκhigh⟩ := exists_between hmax
  obtain ⟨κ₁, hκ₁low, hκ₁high⟩ := exists_between hκhigh
  have hκ : 0 < κ := (le_max_left _ _).trans_lt hκlow
  have hlevel := d.scalarLevelChart_mem_of_lt hρ ha₀ _ hroot hz
    (show κ₁ / 2 < (d.U z).toReal by linarith)
  have hbound := scalar_target_component_le_norm_sub_rate_of_smooth f hlin htrans
    hsmall hρ hl hu hm ha hpeak hstep q hn hc hc₀ hclim halim d hΩ hconn hΩball
    hsmooth hP hlog hzΩ hκ hκ₁low hlevel (show κ - (d.U z).toReal ≤ d.A by linarith)
  have hh := (le_max_right 0 ((d.U z).toReal - u z)).trans_lt hκlow
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.scalar_target_component_le_neg_norm_of_smooth
