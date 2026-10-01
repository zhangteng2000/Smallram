import ModifiedCartan.ScalarDyadicTargets
import ModifiedCartan.ScalarRadialPeakDisks

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Construct the actual dyadic target data at any proved admissible width.
This allows later geometric refinements without altering the fixed target. -/
theorem scalar_exists_dyadic_peak_target_with_width
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    (hstep : Tendsto (fun ν => a (ν + 1) - a ν) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε)
    (hdisks : ∀ b : ℂ, ‖b‖ = 1 → closedBall b (4 * ε) ⊆ scalarFullSector b ρ ∧
      closedBall ((1 / 2 : ℂ) * b) (4 * ε) ⊆ scalarFullSector b ρ) :
    ∃ q : ScalarDyadicPeakTargetData f a ρ, q.width = ε := by
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨δ, hδ, hcross⟩ := scalar_phase_peak_moving_crosses f hlin htrans hsmall hρ hl hu hm
    hpow ha hpeak hε (fun b hb => (hdisks b hb).1)
  obtain ⟨y, hH⟩ := exists_moving_horizontal_lines hε hcross
  obtain ⟨η, hη, hsteps⟩ := scalar_dyadic_peak_anchor_steps f hlin htrans hsmall hρ hl hu hm
    ha hpeak hstep hε hdisks hδ hH
  have hsep : ∀ᶠ ν in atTop, Real.log 2 ≤ η *
      (characteristic f ((2 : ℝ) ^ (ν + 1)) - characteristic f ((2 : ℝ) ^ ν)) := by
    have hh := hpow.eventually (characteristic_doubled_increment_eventually f htrans hlin hsmall hρ hl hu hη)
    simpa only [pow_succ, mul_comm] using hh
  obtain ⟨β, hlim, hclose⟩ := scalarSphereImage_limit_of_eventually_exponential_steps
    (fun ν => scalarSphereProjection_mem _ _) hsep hsteps
  exact ⟨⟨ε, hε, hdisks, δ, hδ, y, hH, β, η, hη, hlim, hclose⟩, rfl⟩

/-- The dyadic target construction can use disks along the entire radial
corridor [1/2,1], uniformly over every possible limiting peak direction. -/
theorem scalar_exists_dyadic_peak_target_radial
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    (hstep : Tendsto (fun ν => a (ν + 1) - a ν) atTop (𝓝 0)) :
    ∃ q : ScalarDyadicPeakTargetData f a ρ, ∀ b : ℂ, ‖b‖ = 1 → ∀ t ∈ Icc (1 / 2 : ℝ) 1,
      closedBall ((t : ℂ) * b) (4 * q.width) ⊆ scalarFullSector b ρ := by
  obtain ⟨ε, hε, hdisks⟩ := scalarFullSector_uniform_radial_disks
    (lt_of_lt_of_le zero_lt_one hρ) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) < 2)
  have he (b : ℂ) (hb : ‖b‖ = 1) : closedBall b (4 * ε) ⊆ scalarFullSector b ρ ∧
      closedBall ((1 / 2 : ℂ) * b) (4 * ε) ⊆ scalarFullSector b ρ := by
    constructor
    · simpa only [Complex.ofReal_one, one_mul] using hdisks b hb 1 ⟨by norm_num, le_rfl⟩
    · simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
        hdisks b hb (1 / 2) ⟨le_rfl, by norm_num⟩
  obtain ⟨q, hq⟩ := scalar_exists_dyadic_peak_target_with_width f hlin htrans hsmall hρ hl hu hm
    ha hpeak hstep hε he
  exact ⟨q, by rw [hq]; exact hdisks⟩

end ModifiedCartan
#print axioms ModifiedCartan.scalar_exists_dyadic_peak_target_with_width
#print axioms ModifiedCartan.scalar_exists_dyadic_peak_target_radial