import ModifiedCartan.ScalarComparablePeaks
import ModifiedCartan.ScalarPhasePeakLimits
import ModifiedCartan.ScalarLevelChart

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Coherent dyadic peaks give the actual quadratic root even when the
physical radius varies by an arbitrary factor in [1,2]. Auxiliary to
LaTeX `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalar_comparable_peak_limit
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {c : ℕ → ℝ}
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2)
    {a₀ : ℂ} (halim : Tendsto (fun ν => a (n ν)) atTop (𝓝 a₀))
    (d : ArbitraryRadiusLimitData f (fun ν => c ν * (2 : ℝ) ^ n ν) ρ) :
    ‖a₀‖ = 1 ∧ (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic a₀ := by
  have hm0 : m ≠ 0 := by intro hz; simp only [hz, Nat.cast_zero, zero_div] at hm; linarith
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hr : Tendsto (fun ν => c ν * (2 : ℝ) ^ n ν) atTop atTop := by
    apply tendsto_atTop_mono (fun ν => ?_) (hpow.comp hn)
    change (2 : ℝ) ^ n ν ≤ c ν * (2 : ℝ) ^ n ν
    have hh := mul_le_mul_of_nonneg_right (hc ν).1 (pow_pos (by norm_num : (0 : ℝ) < 2) (n ν)).le
    simpa only [one_mul] using hh
  let b : ℕ → ℂ := fun ν => scalarComparablePeakCenter f m ((2 : ℝ) ^ n ν) (c ν) (a (n ν))
  have hdiff := scalarComparablePeakCenter_difference_tendsto_zero f hlin htrans hsmall
    hρ hl hu hm (hpow.comp hn) hc (fun ν => ha (n ν))
  have hb : Tendsto b atTop (𝓝 a₀) := by
    simpa only [b, Function.comp_def, sub_add_cancel, zero_add] using hdiff.add halim
  exact d.scalar_phase_peak_limit hlin htrans hsmall hρ hl hu hr hm
    (fun ν => scalarComparablePeakCenter_norm f m _ _ (ha (n (d.subseq ν))))
    (hb.comp d.strictMono.tendsto_atTop)
    (fun ν => scalarComparablePeakCenter_peak f hm0 _ _ (hpeak (n (d.subseq ν))))

/-- The actual norm profile identifies every strict level within a positive
power-chart sector. Auxiliary to LaTeX `thm:A` (b). -/
theorem ArbitraryRadiusLimitData.scalarLevelChart_mem_of_lt
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    (hb : b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2))
    {z : ℂ} (hz : z ∈ scalarPositiveChart a ρ b) {ℓ : ℝ}
    (hℓ : ℓ < (d.U z).toReal) : z ∈ scalarLevelChart a ρ b ℓ := by
  rcases hz with ⟨w, hw, rfl⟩
  refine ⟨w, ⟨hw.1, ?_⟩, rfl⟩
  exact hℓ.trans_eq (d.scalar_norm_positiveChart_pullback hρ ha b hb hw)

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_comparable_peak_limit
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalarLevelChart_mem_of_lt
