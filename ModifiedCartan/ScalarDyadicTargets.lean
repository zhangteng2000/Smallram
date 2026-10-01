import ModifiedCartan.ScalarDyadicAnchorSteps
import ModifiedCartan.ScalarEventualGluing
import ModifiedCartan.ScalarScaleSeparation

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Constructed actual dyadic line selections and their fixed sphere target,
with a quantitative rate. Auxiliary data for LaTeX thm:A (b). -/
structure ScalarDyadicPeakTargetData (f : Curve 1) (a : ℕ → ℂ) (ρ : ℝ) where
  width : ℝ
  width_pos : 0 < width
  sector_disks : ∀ b : ℂ, ‖b‖ = 1 →
    closedBall b (4 * width) ⊆ scalarFullSector b ρ ∧
    closedBall ((1 / 2 : ℂ) * b) (4 * width) ⊆ scalarFullSector b ρ
  lineRate : ℝ
  lineRate_pos : 0 < lineRate
  height : ℕ → ℝ
  good : ∀ᶠ ν in atTop, height ν ∈ Icc ((a ν).im - width) ((a ν).im + width) ∧
    ∀ t ∈ Icc ((a ν).re - width) ((a ν).re + width),
      (2 : ℝ) ^ ν * scalarSphericalSpeed f.coord
        ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨t, height ν⟩ : ℂ)) ≤
          Real.exp (-lineRate * characteristic f ((2 : ℝ) ^ ν))
  target : WithTop ℂ
  decayRate : ℝ
  decayRate_pos : 0 < decayRate
  limit : Tendsto (fun ν => scalarCurveSphere f
    ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨(a ν).re - width, height ν⟩ : ℂ))) atTop (𝓝 (scalarSphereValue target))
  close : ∀ᶠ ν in atTop, ‖scalarCurveSphere f
    ((((2 : ℝ) ^ ν : ℝ) : ℂ) * (⟨(a ν).re - width, height ν⟩ : ℂ)) - scalarSphereValue target‖ ≤
      2 * Real.exp (-decayRate * characteristic f ((2 : ℝ) ^ ν))

/-- All fields, including the fixed target and exponential approach, are
constructed from the original curve and a coherent actual phase peak. -/
theorem scalar_exists_dyadic_peak_target
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) {a : ℕ → ℂ}
    (ha : ∀ ν, ‖a ν‖ = 1)
    (hpeak : ∀ ν, scalarPhaseCoefficient f m ((2 : ℝ) ^ ν) * (a ν) ^ m =
      (((Real.pi / 2) ^ 2 : ℝ) : ℂ))
    (hstep : Tendsto (fun ν => a (ν + 1) - a ν) atTop (𝓝 0)) :
    Nonempty (ScalarDyadicPeakTargetData f a ρ) := by
  have hpow : Tendsto (fun ν : ℕ => (2 : ℝ) ^ ν) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨ε, hε, hdisks, hwidth⟩ := scalar_exists_phase_peak_cross_width f hlin htrans hsmall hρ hl hu hm
  obtain ⟨δ, hδ, hcross⟩ := hwidth (fun ν => (2 : ℝ) ^ ν) hpow a ha hpeak
  obtain ⟨y, hH⟩ := exists_moving_horizontal_lines hε hcross
  obtain ⟨η, hη, hsteps⟩ := scalar_dyadic_peak_anchor_steps f hlin htrans hsmall hρ hl hu hm
    ha hpeak hstep hε hdisks hδ hH
  have hsep : ∀ᶠ ν in atTop, Real.log 2 ≤ η *
      (characteristic f ((2 : ℝ) ^ (ν + 1)) - characteristic f ((2 : ℝ) ^ ν)) := by
    have hh := hpow.eventually (characteristic_doubled_increment_eventually f htrans hlin hsmall hρ hl hu hη)
    simpa only [pow_succ, mul_comm] using hh
  obtain ⟨β, hlim, hclose⟩ := scalarSphereImage_limit_of_eventually_exponential_steps
    (fun ν => scalarSphereProjection_mem _ _) hsep hsteps
  exact ⟨⟨ε, hε, hdisks, δ, hδ, y, hH, β, η, hη, hlim, hclose⟩⟩

/-- The recursively constructed dyadic phase peak has an actual fixed target.
No convergence of the angle or external asymptotic-value theorem is used. -/
theorem scalarDyadicPeakCenter_has_fixed_target
    (f : Curve 1) (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {m : ℕ} (hm : ρ = (m : ℝ) / 2) :
    Nonempty (ScalarDyadicPeakTargetData f (scalarDyadicPeakCenter f m) ρ) := by
  have hm0 : m ≠ 0 := by intro hz; simp only [hz, Nat.cast_zero, zero_div] at hm; linarith
  exact scalar_exists_dyadic_peak_target f hlin htrans hsmall hρ hl hu hm
    (scalarDyadicPeakCenter_norm f m) (scalarDyadicPeakCenter_peak f hm0)
    (scalarDyadicPeakCenter_steps_tendsto_zero f hlin htrans hsmall hρ hl hu hm)

end ModifiedCartan
#print axioms ModifiedCartan.scalar_exists_dyadic_peak_target
#print axioms ModifiedCartan.scalarDyadicPeakCenter_has_fixed_target