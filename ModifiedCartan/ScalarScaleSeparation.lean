import ModifiedCartan.CharacteristicRatioLimit

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual characteristic has enough separation between successive doubled
radii to preserve exponential errors under summation. Auxiliary to `thm:A` (b). -/
theorem characteristic_doubled_increment_eventually {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in atTop, Real.log 2 ≤ δ * (characteristic f (2 * r) - characteristic f r) := by
  have hρpos := lt_of_lt_of_le zero_lt_one hρ
  have hpow : (2 : ℝ) ≤ 2 ^ ρ := Real.self_le_rpow_of_one_le (by norm_num) hρ
  have hgap : (3 / 2 : ℝ) < 2 ^ ρ := by linarith
  have hratio := characteristic_ratio_tendsto f htrans hlin hsmall hρpos hl hu
    (by norm_num : (0 : ℝ) < 2)
  have hT := characteristic_tendsto_atTop_of_transcendental f htrans
  filter_upwards [hratio.eventually_const_lt hgap, hT.eventually_gt_atTop 0,
    hT.eventually_ge_atTop (2 * Real.log 2 / δ)] with r hrat ht htlarge
  have hm : (3 / 2 : ℝ) * characteristic f r ≤ characteristic f (2 * r) :=
    ((lt_div_iff₀ ht).mp hrat).le
  have hlarge := (div_le_iff₀ hδ).mp htlarge
  have hh := mul_le_mul_of_nonneg_left hm hδ.le
  nlinarith

theorem characteristic_doubled_exp_halving_eventually {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in atTop,
      Real.exp (-δ * characteristic f (2 * r)) ≤ (1 / 2 : ℝ) * Real.exp (-δ * characteristic f r) := by
  filter_upwards [characteristic_doubled_increment_eventually f htrans hlin hsmall hρ hl hu hδ] with r hr
  calc
    _ ≤ Real.exp (-δ * characteristic f r - Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring

end ModifiedCartan
#print axioms ModifiedCartan.characteristic_doubled_increment_eventually
#print axioms ModifiedCartan.characteristic_doubled_exp_halving_eventually
