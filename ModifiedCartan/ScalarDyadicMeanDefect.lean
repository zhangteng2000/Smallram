import ModifiedCartan.ScalarSectorMeanDefect
import ModifiedCartan.ScalarDyadicSectorTargets
import ModifiedCartan.ScalarOtherTargetSector
import ModifiedCartan.ScalarProjectiveProximityLimits

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual prescribed-target limit has the exact multiplicity of the
coherently tracked dyadic targets. All sector signs and roots are proved.
Auxiliary to LaTeX `thm:A` (b). -/
theorem ScalarTargetLogLimitData.circle_mean_defect_eq_dyadic_multiplicity
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2)
    (q : (j : Fin m) → ScalarDyadicPeakTargetData f (scalarDyadicSectorCenter f m j) ρ)
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    {c : ℕ → ℝ} (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hclim : Tendsto c atTop (𝓝 c₀))
    {a₀ : ℂ} (halim : Tendsto (fun ν => scalarDyadicPeakCenter f m (n ν)) atTop (𝓝 a₀))
    {d : ArbitraryRadiusLimitData f (fun ν => c ν * (2 : ℝ) ^ n ν) ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β)
    (hA : (Real.pi / 2) * (2 : ℝ) ^ ρ ≤ d.A) :
    1 - Real.circleAverage (fun z => (e.u z).toReal) 0 1 =
      (scalarSectorMultiplicity (fun j => (q j).target) β : ℝ) / ρ := by
  have hm0 : m ≠ 0 := by intro hz; simp only [hz, Nat.cast_zero, zero_div] at hm; linarith
  have halimj (j : Fin m) : Tendsto (fun ν => scalarDyadicSectorCenter f m j (n ν)) atTop
      (𝓝 (scalarSectorCenter a₀ m j)) :=
    halim.mul_const (scalarSectorRotation m j.val)
  have hbase := d.scalar_comparable_peak_limit f hlin htrans hsmall hρ hl hu hm
    (scalarDyadicPeakCenter_norm f m) (scalarDyadicPeakCenter_peak f hm0) hn hc halim
  have hr : Tendsto (fun ν => c ν * (2 : ℝ) ^ n ν) atTop atTop := by
    apply tendsto_atTop_mono (fun ν => ?_)
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hn)
    simpa only [one_mul, Function.comp_def] using mul_le_mul_of_nonneg_right (hc ν).1
      (pow_pos (by norm_num : (0 : ℝ) < 2) (n ν)).le
  apply e.circle_mean_defect_eq_sectorMultiplicity hρ hr hm hbase.1 (fun j => (q j).target)
  · intro j
    exact (d.scalar_comparable_peak_limit f hlin htrans hsmall hρ hl hu hm
      (scalarDyadicSectorCenter_norm f m j) (scalarDyadicSectorCenter_peak f hm0 j)
      hn hc (halimj j)).2
  · intro j he
    subst β
    exact e.eq_neg_norm_on_positive_chart f hlin htrans hsmall hρ hl hu hm
      (scalarDyadicSectorCenter_norm f m j) (scalarDyadicSectorCenter_peak f hm0 j)
      (scalarDyadicSectorCenter_steps_tendsto_zero f hlin htrans hsmall hρ hl hu hm j)
      (q j) hn hc hc₀ hclim (halimj j) hA
  · intro j he
    exact e.eq_norm_on_other_positive_chart f hlin htrans hsmall hρ hl hu hm
      (scalarDyadicSectorCenter_norm f m j) (scalarDyadicSectorCenter_peak f hm0 j)
      (scalarDyadicSectorCenter_steps_tendsto_zero f hlin htrans hsmall hρ hl hu hm j)
      (q j) hn hc hc₀ hclim (halimj j) he hA

end ModifiedCartan
#print axioms ModifiedCartan.ScalarTargetLogLimitData.circle_mean_defect_eq_dyadic_multiplicity
