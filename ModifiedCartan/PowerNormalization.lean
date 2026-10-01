import ModifiedCartan.UniformPowerBounds
import ModifiedCartan.CharacteristicPeaks

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- Fixing the base radius in `eq:power-bounds` gives a genuine positive
power lower bound for every sufficiently large radius. -/
theorem uniform_power_lower_bound (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {ρ ε C r0 : ℝ}
    (hC : 0 < C) (hr0 : 0 < r0) (hε : 0 ≤ ε)
    (hb : ∀ t r, r0 ≤ r → r0 ≤ t * r →
      C⁻¹ * min (t ^ (ρ - ε)) (t ^ (ρ + ε)) ≤ T (t * r) / T r) :
    ∃ D : ℝ, 0 < D ∧ ∀ r, r0 ≤ r → D * r ^ (ρ - ε) ≤ T r := by
  let D := C⁻¹ * T r0 / r0 ^ (ρ - ε)
  have hD : 0 < D := div_pos (mul_pos (inv_pos.mpr hC) (hT r0 hr0))
    (Real.rpow_pos_of_pos hr0 _)
  refine ⟨D, hD, ?_⟩
  intro r hr
  have hrp := hr0.trans_le hr
  have htr : r / r0 * r0 = r := div_mul_cancel₀ r hr0.ne'
  have ht : 1 ≤ r / r0 := (one_le_div hr0).mpr hr
  have hpow : (r / r0) ^ (ρ - ε) ≤ (r / r0) ^ (ρ + ε) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have hh := hb (r / r0) r0 le_rfl (by rw [htr]; exact hr)
  rw [htr, min_eq_left hpow] at hh
  have hh' := (le_div_iff₀ (hT r0 hr0)).mp hh
  convert! hh' using 1
  dsimp only [D]
  rw [Real.div_rpow hrp.le hr0.le]
  ring

theorem log_div_of_power_lower_bound (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {D a r0 : ℝ}
    (hD : 0 < D) (ha : 0 < a) (hr0 : 0 < r0)
    (hb : ∀ r, r0 ≤ r → D * r ^ a ≤ T r) :
    Tendsto (fun r => Real.log r / T r) atTop (𝓝 0) := by
  have hbig : (fun r : ℝ => r ^ a) =O[atTop] T := by
    apply IsBigO.of_bound D⁻¹
    filter_upwards [eventually_ge_atTop r0] with r hr
    have hrp := hr0.trans_le hr
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hrp.le _), Real.norm_of_nonneg (hT r hrp).le]
    calc
      r ^ a ≤ T r / D := (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hb r hr)
      _ = D⁻¹ * T r := by ring
  exact ((isLittleO_log_rpow_atTop ha).trans_isBigO hbig).tendsto_div_nhds_zero

/-- The logarithmic normalization required in Section `sec:arbitrary-limits`.
It follows from the proved two-sided bounds and positive common index. -/
theorem characteristic_log_div_tendsto_zero_of_equal_positive_indices {n : ℕ}
    (f : Curve n) (htrans : f.Transcendental) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal)) :
    Tendsto (fun r => Real.log r / characteristic f r) atTop (𝓝 0) := by
  have hT := fun r hr => characteristic_pos_of_transcendental f htrans (r := r) hr
  obtain ⟨C, r0, hC, hr0, hb⟩ := Paper.lem_power_bounds (characteristic f) hT
    (characteristic_monotoneOn f) (characteristic_unbounded_of_transcendental f htrans)
    hρ hl hu (ε := ρ / 2) (by positivity) (by linarith)
  obtain ⟨D, hD, hbound⟩ := uniform_power_lower_bound (characteristic f) hT
    (zero_lt_one.trans_le hC) hr0 (by positivity : 0 ≤ ρ / 2)
    (fun t r hr htr => (hb t r hr htr).1)
  exact log_div_of_power_lower_bound (characteristic f) hT hD (by linarith) hr0 hbound

end ModifiedCartan
#print axioms ModifiedCartan.characteristic_log_div_tendsto_zero_of_equal_positive_indices
