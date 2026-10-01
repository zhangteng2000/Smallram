import ModifiedCartan.ScalarSharpScaleBounds
import ModifiedCartan.VariableScaling
import ModifiedCartan.Indices

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- A fixed distant dyadic scale admits an arbitrarily small sharp rate,
whose regular-variation rescaling is exactly the requested rate. -/
theorem exists_dyadic_sharp_rate {ρ c κ η : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ K : ℕ, 1 ≤ K ∧
      0 < c / (2 : ℝ) ^ K ∧ c / (2 : ℝ) ^ K ≤ 1 ∧
      0 < κ * (c / (2 : ℝ) ^ K) ^ ρ ∧
      κ * (c / (2 : ℝ) ^ K) ^ ρ < η ∧
      (κ * (c / (2 : ℝ) ^ K) ^ ρ) * (((2 : ℝ) ^ K / c) ^ ρ) = κ := by
  have hpow : Tendsto (fun K : ℕ => (2 : ℝ) ^ K) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsmall : Tendsto (fun K : ℕ => κ * (c / (2 : ℝ) ^ K) ^ ρ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((hpow.const_div_atTop c).rpow_const_nhds_zero hρ).const_mul κ
  obtain ⟨K, hK, hbig, hsmall⟩ := ((eventually_ge_atTop 1).and
    ((hpow.eventually_ge_atTop c).and (hsmall.eventually_lt_const hη))).exists
  have hp : 0 < (2 : ℝ) ^ K := pow_pos (by norm_num) K
  refine ⟨K, hK, div_pos hc hp, (div_le_one hp).2 hbig,
    mul_pos hκ (Real.rpow_pos_of_pos (div_pos hc hp) ρ), hsmall, ?_⟩
  rw [Real.div_rpow hc.le hp.le, Real.div_rpow hp.le hc.le]
  have hcp := (Real.rpow_pos_of_pos hc ρ).ne'
  have hpp := (Real.rpow_pos_of_pos hp ρ).ne'
  field_simp

/-- Exact ratio of a fixed larger radius to varying comparable radii. -/
theorem characteristic_fixed_to_variable_ratio_tendsto {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r c : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) {c₀ L : ℝ}
    (hc₀ : 0 < c₀) (hclim : Tendsto c atTop (𝓝 c₀)) (hL : 0 < L) :
    Tendsto (fun ν => characteristic f (L * r ν) / characteristic f (c ν * r ν))
      atTop (𝓝 ((L / c₀) ^ ρ)) := by
  have hreg := Paper.prop_regular_variation f htrans hlin hsmall
    (positive_index_order_admissible f hlin htrans hsmall hρ hl.le hu.ge) hl hu
  have hv := regularlyVarying_tendsto_variable_multiplier hreg isCompact_Icc
    (show Icc (1 : ℝ) 2 ⊆ Ioi 0 from fun x hx => by change 0 < x; linarith [hx.1])
    hc hc₀ hclim hr
  have hf := (characteristic_ratio_tendsto f htrans hlin hsmall hρ hl hu hL).comp hr
  have hh := hf.div hv (Real.rpow_pos_of_pos hc₀ ρ).ne'
  rw [← Real.div_rpow hL.le hc₀.le] at hh
  apply hh.congr'
  filter_upwards [((characteristic_tendsto_atTop_of_transcendental f htrans).comp hr).eventually_gt_atTop 0]
    with ν hν
  dsimp only [Function.comp_def] at hν ⊢
  change (characteristic f (L * r ν) / characteristic f (r ν)) /
    (characteristic f (c ν * r ν) / characteristic f (r ν)) = _
  exact div_div_div_cancel_right₀ hν.ne' _ _

/-- A strict inequality of limiting rates gives the corresponding eventual
comparison on actual characteristics, with no fixed loss of coefficient. -/
theorem characteristic_sharp_rate_transfer {n : ℕ} (f : Curve n)
    (htrans : f.Transcendental) (hlin : f.linearlyNonDegenerate)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r c : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hc : ∀ ν, c ν ∈ Icc (1 : ℝ) 2) {c₀ L δ κ : ℝ}
    (hc₀ : 0 < c₀) (hclim : Tendsto c atTop (𝓝 c₀)) (hL : 0 < L)
    (hκ : κ < δ * (L / c₀) ^ ρ) :
    ∀ᶠ ν in atTop, κ * characteristic f (c ν * r ν) ≤
      δ * characteristic f (L * r ν) := by
  have hh := ((characteristic_fixed_to_variable_ratio_tendsto f htrans hlin hsmall
    hρ hl hu hr hc hc₀ hclim hL).const_mul δ).eventually_const_lt hκ
  filter_upwards [hh, hr.eventually_gt_atTop 0] with ν hν hrν
  have ht := characteristic_pos_of_transcendental f htrans
    (mul_pos (lt_of_lt_of_le zero_lt_one (hc ν).1) hrν)
  have hm := mul_le_mul_of_nonneg_right hν.le ht.le
  have he : (δ * (characteristic f (L * r ν) / characteristic f (c ν * r ν))) *
      characteristic f (c ν * r ν) = δ * characteristic f (L * r ν) := by
    rw [mul_assoc, div_mul_cancel₀ _ ht.ne']
  rwa [he] at hm

end ModifiedCartan
#print axioms ModifiedCartan.exists_dyadic_sharp_rate
#print axioms ModifiedCartan.characteristic_fixed_to_variable_ratio_tendsto
#print axioms ModifiedCartan.characteristic_sharp_rate_transfer
