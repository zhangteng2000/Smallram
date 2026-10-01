import ModifiedCartan.CharacteristicRatioLimit
import ModifiedCartan.CharacteristicMonotone

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem two_div_mem_Icc_one_two {c : ℝ} (hc : c ∈ Icc (1 : ℝ) 2) :
    2 / c ∈ Icc (1 : ℝ) 2 := by
  have hp : 0 < c := lt_of_lt_of_le zero_lt_one hc.1
  constructor
  · apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using hc.2
  · apply (div_le_iff₀ hp).mpr
    linarith [hc.1]

theorem characteristic_comparable_mono {n : ℕ} (f : Curve n) {r c : ℝ}
    (hr : 0 < r) (hc : c ∈ Icc (1 : ℝ) 2) :
    characteristic f r ≤ characteristic f (c * r) ∧
      characteristic f (c * r) ≤ characteristic f (2 * r) := by
  have hcr : 0 < c * r := mul_pos (lt_of_lt_of_le zero_lt_one hc.1) hr
  constructor
  · apply characteristic_monotoneOn f hr hcr
    nlinarith [hc.1]
  · apply characteristic_monotoneOn f hcr (mul_pos (by norm_num : (0 : ℝ) < 2) hr)
    exact mul_le_mul_of_nonneg_right hc.2 hr.le

/-- A single positive bound compares the actual characteristic at every
multiplier in [1,2]. The bound follows from proved regular variation. -/
theorem characteristic_comparable_uniform_upper {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal)) :
    ∃ B > 0, ∀ᶠ r : ℝ in atTop, ∀ c ∈ Icc (1 : ℝ) 2,
      characteristic f (c * r) ≤ B * characteristic f r := by
  let B : ℝ := 2 ^ ρ + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have ht := characteristic_tendsto_atTop_of_transcendental f htrans
  have hratio := characteristic_ratio_tendsto f htrans hlin hsmall hρ hl hu (by norm_num : (0 : ℝ) < 2)
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), ht.eventually_gt_atTop 0,
    hratio.eventually_lt_const (show (2 : ℝ) ^ ρ < B by dsimp only [B]; linarith)] with r hr htr hratio
  intro c hc
  exact (characteristic_comparable_mono f hr hc).2.trans ((div_lt_iff₀ htr).mp hratio).le

/-- Positive exponential rates on the lower radius scale transfer to the
actual comparable radius, using the proved characteristic bound. -/
theorem exponential_bound_convert_comparable_characteristic {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r c d : ℕ → ℝ} (hr : Tendsto r atTop atTop) (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2)
    {η : ℝ} (hη : 0 < η)
    (hd : ∀ᶠ ν in atTop, d ν ≤ Real.exp (-η * characteristic f (r ν))) :
    ∃ δ > 0, ∀ᶠ ν in atTop, d ν ≤ Real.exp (-δ * characteristic f (c ν * r ν)) := by
  obtain ⟨B, hB, hb⟩ := characteristic_comparable_uniform_upper f htrans hlin hsmall hρ hl hu
  refine ⟨η / B, div_pos hη hB, ?_⟩
  filter_upwards [hd, hr.eventually hb] with ν hdν hbν
  have hh := mul_le_mul_of_nonneg_left (hbν (c ν) (hc ν)) (div_pos hη hB).le
  have he : η / B * (B * characteristic f (r ν)) = η * characteristic f (r ν) := by field_simp
  rw [he] at hh
  exact hdν.trans (Real.exp_le_exp.mpr (by nlinarith))

end ModifiedCartan
#print axioms ModifiedCartan.characteristic_comparable_uniform_upper
#print axioms ModifiedCartan.exponential_bound_convert_comparable_characteristic