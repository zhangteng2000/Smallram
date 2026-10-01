import ModifiedCartan.ScalarTargetHorizontalCaps
import ModifiedCartan.ActualNormUpper
import ModifiedCartan.PolynomialCrossingCap

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Sharp local bound for the actual fixed-target polynomial logarithmic
limit at a point of smoothness. The horizontal caps are constructed from the
original curve, coherent dyadic peaks and their proved fixed target. -/
theorem scalar_target_component_le_norm_sub_rate_of_smooth
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
    {z : ℂ} (hzΩ : z ∈ Ω) {κ κ₁ : ℝ} (hκ : 0 < κ) (hκ₁ : κ < κ₁)
    (hz : z ∈ scalarLevelChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ) (κ₁ / 2))
    (hA : κ - (d.U z).toReal ≤ d.A) :
    u z ≤ (d.U z).toReal - κ := by
  by_contra hh
  have hgap : (d.U z).toReal - κ < u z := lt_of_not_ge hh
  let η := (u z - ((d.U z).toReal - κ)) / 4
  have hη : 0 < η := by dsimp only [η]; linarith
  obtain ⟨δ, hδ, hK, hN⟩ := d.actual_norm_near_point (hΩball hzΩ) hη
  obtain ⟨σ, hσ, ε₀, hε₀, hlines⟩ := scalar_sharp_target_lines_at_comparable_radii
    f hlin htrans hsmall hρ hl hu hm ha hpeak hstep q
    (hn.comp d.strictMono.tendsto_atTop) (fun ν => hc (d.subseq ν)) hc₀
    (hclim.comp d.strictMono.tendsto_atTop) (halim.comp d.strictMono.tendsto_atTop) hκ hκ₁ hz
  have hcap : u z ≤ (d.U z).toReal + η - κ + η := by
    apply hlog.polynomial_limit_le_of_horizontal_caps hΩ hconn hP d.scale_tendsto hsmooth hzΩ
      (lt_min hε₀ (show 0 < δ / 4 by positivity))
    intro ε hε hεmax
    have hε₀' : ε ≤ ε₀ := hεmax.trans (min_le_left _ _)
    have hεδ : 3 * ε ≤ δ := by have hh := hεmax.trans (min_le_right _ _); linarith
    obtain ⟨y, C, hC, hy⟩ := hlines ε hε hε₀'
    refine ⟨σ, hσ, y, ?_⟩
    exact (d.replacement.comp_tendsto hσ.tendsto_atTop).scalar_target_horizontal_caps q.target
      (d.scale_tendsto.comp hσ.tendsto_atTop) hC hε hη hεδ hK
      (show κ - ((d.U z).toReal + η) ≤ d.A by linarith)
      (hσ.tendsto_atTop.eventually hN) hy
  dsimp only [η] at hcap
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.scalar_target_component_le_norm_sub_rate_of_smooth
