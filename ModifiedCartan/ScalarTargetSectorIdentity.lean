import ModifiedCartan.ScalarTargetLogData
import ModifiedCartan.ScalarNegativeTargetSector

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual fixed-target logarithmic limit is exactly -U throughout its
matching sector. Both inequalities have been proved from the original curve
and constructed limit data. Auxiliary to LaTeX `thm:A` (b). -/
theorem ScalarTargetLogLimitData.eq_neg_norm_on_positive_chart
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
    {d : ArbitraryRadiusLimitData f (fun ν => c ν * (2 : ℝ) ^ n ν) ρ}
    (e : ScalarTargetLogLimitData d q.target)
    (hA : (Real.pi / 2) * (2 : ℝ) ^ ρ ≤ d.A) :
    EqOn (fun z => (e.u z).toReal) (fun z => -(d.U z).toReal)
      (scalarPositiveChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ)) := by
  have hupp := scalar_target_component_le_neg_norm_on_positive_chart f hlin htrans hsmall
    hρ hl hu hm ha hpeak hstep q hn hc hc₀ hclim halim d hA
    e.subharmonic e.representative e.convergence
  have ha₀norm : ‖a₀‖ = 1 := (d.scalar_comparable_peak_limit
    f hlin htrans hsmall hρ hl hu hm ha hpeak hn hc halim).1
  have ha₀ : a₀ ≠ 0 := norm_ne_zero_iff.mp (by rw [ha₀norm]; norm_num)
  have hsub : scalarPositiveChart a₀ ρ ((Real.pi / 2 : ℝ) : ℂ) ⊆ ball (0 : ℂ) 4 :=
    (scalarPositiveChart_subset ha₀ (lt_of_lt_of_le zero_lt_one hρ)).trans
      (ball_subset_ball (by norm_num))
  intro z hz
  exact le_antisymm (hupp z hz) (e.bounds z (hsub hz)).1

end ModifiedCartan
#print axioms ModifiedCartan.ScalarTargetLogLimitData.eq_neg_norm_on_positive_chart
