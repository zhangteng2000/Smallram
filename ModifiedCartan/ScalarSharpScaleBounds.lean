import ModifiedCartan.CharacteristicComparableBounds
import ModifiedCartan.ScalarExponentialBounds

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- A fixed factor can be absorbed with any strictly positive loss of rate.
This retains sharp limiting coefficients in the later proximity formula. -/
theorem constant_mul_exp_neg_le_eventually {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) {δ κ C : ℝ} (hκδ : κ < δ) (hC : 0 ≤ C) :
    ∀ᶠ ν in atTop, C * Real.exp (-δ * s ν) ≤ Real.exp (-κ * s ν) := by
  rcases eq_or_lt_of_le hC with hzero | hpos
  · rw [← hzero]
    exact Eventually.of_forall (fun ν => by simpa only [zero_mul] using (Real.exp_pos _).le)
  · filter_upwards [hs.eventually_ge_atTop (Real.log C / (δ - κ))] with ν hν
    have hlog : Real.log C ≤ (δ - κ) * s ν := by
      simpa only [mul_comm] using (div_le_iff₀ (sub_pos.mpr hκδ)).mp hν
    have hCe : C ≤ Real.exp ((δ - κ) * s ν) := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr hlog
    calc
      _ ≤ Real.exp ((δ - κ) * s ν) * Real.exp (-δ * s ν) :=
        mul_le_mul_of_nonneg_right hCe (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Vanishing consecutive displacements give vanishing displacement under
every fixed finite shift of the coherent peak numbering. -/
theorem complex_fixed_shift_sub_tendsto_zero {a : ℕ → ℂ}
    (h : Tendsto (fun ν => a (ν + 1) - a ν) atTop (𝓝 0)) (K : ℕ) :
    Tendsto (fun ν => a (ν + K) - a ν) atTop (𝓝 0) := by
  induction K with
  | zero => simpa only [Nat.add_zero, sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  | succ K ih =>
    have hh := (h.comp (tendsto_add_atTop_nat K)).add ih
    simpa only [Function.comp_def, sub_add_sub_cancel, zero_add, Nat.add_assoc] using hh

/-- A fixed sufficiently large dyadic dilation makes any fixed positive
target rate dominate a prescribed rate at every comparable smaller radius.
The integer is chosen using the proved positive-index regular variation. -/
theorem characteristic_large_dyadic_multiple_eventually {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {η κ : ℝ} (hη : 0 < η) (hκ : 0 ≤ κ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ᶠ r : ℝ in atTop, ∀ c ∈ Icc (1 : ℝ) 2,
      κ * characteristic f (c * r) ≤ η * characteristic f ((2 : ℝ) ^ K * r) := by
  obtain ⟨B, hB, hbound⟩ := characteristic_comparable_uniform_upper f htrans hlin hsmall hρ hl hu
  have hpow : Tendsto (fun K : ℕ => (2 : ℝ) ^ K) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hgrow : Tendsto (fun K : ℕ => η * (((2 : ℝ) ^ K) ^ ρ)) atTop atTop :=
    Tendsto.const_mul_atTop hη ((tendsto_rpow_atTop hρ).comp hpow)
  obtain ⟨K, hbig, hK⟩ := ((hgrow.eventually_gt_atTop (κ * B)).and (eventually_ge_atTop 1)).exists
  have hr := characteristic_ratio_tendsto f htrans hlin hsmall hρ hl hu
    (pow_pos (by norm_num : (0 : ℝ) < 2) K)
  have hratio := (hr.const_mul η).eventually_const_lt hbig
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, hratio,
    (characteristic_tendsto_atTop_of_transcendental f htrans).eventually_gt_atTop 0]
    with r hb hr hTr
  intro c hc
  have hh : κ * B * characteristic f r ≤ η * characteristic f ((2 : ℝ) ^ K * r) := by
    have hx := mul_le_mul_of_nonneg_right hr.le hTr.le
    have he : (η * (characteristic f ((2 : ℝ) ^ K * r) / characteristic f r)) *
        characteristic f r = η * characteristic f ((2 : ℝ) ^ K * r) := by field_simp
    rwa [he] at hx
  calc
    _ ≤ κ * (B * characteristic f r) := mul_le_mul_of_nonneg_left (hb c hc) hκ
    _ = κ * B * characteristic f r := by ring
    _ ≤ _ := hh

end ModifiedCartan
#print axioms ModifiedCartan.constant_mul_exp_neg_le_eventually
#print axioms ModifiedCartan.complex_fixed_shift_sub_tendsto_zero
#print axioms ModifiedCartan.characteristic_large_dyadic_multiple_eventually
