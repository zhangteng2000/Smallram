import ModifiedCartan.WeightedPrimitive
import ModifiedCartan.PowerExpProfile

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Positive-real-part exponential asymptotics survive one actual primitive.
This proves the integration assertion in Step 2 of `prop:sharpness-orders`;
the small error is controlled by a proved scalar derivative fence. -/
theorem powerExp_primitive_ratio_limit {f f' : ℝ → ℂ} {lam c : ℂ} {b : ℝ}
    (hlam : 0 < lam.re)
    (hdf : ∀ᶠ t in atTop, HasDerivAt f (f' t) t)
    (hf : Tendsto (fun t => f' t / powerExpProfile lam b t) atTop (𝓝 c)) :
    Tendsto (fun t => f t / powerExpProfile lam b t) atTop (𝓝 (c / lam)) := by
  let P := powerExpProfile lam b
  let w := powerExpWeight lam.re b
  let d := c / lam
  have hln : lam ≠ 0 := by intro he; simp [he] at hlam
  let F : ℝ → ℂ := fun t => f t - d * P t
  let F' : ℝ → ℂ := fun t => f' t - d * ((lam + ((b / t : ℝ) : ℂ)) * P t)
  have hsmall : Tendsto (fun t : ℝ => ((b / t : ℝ) : ℂ)) atTop (𝓝 0) := by
    have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (show Tendsto (fun t : ℝ => b / t) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop tendsto_id)
    change Tendsto (fun t : ℝ => ((b / t : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) at hh
    simpa only [Complex.ofReal_zero] using hh
  have hFlim : Tendsto (fun t => F' t / P t) atTop (𝓝 0) := by
    have hh := hf.sub ((hsmall.const_add lam).const_mul d)
    have hend : c - d * (lam + 0) = 0 := by simp only [d, add_zero, div_mul_cancel₀ _ hln, sub_self]
    rw [hend] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hp : P t ≠ 0 := powerExpProfile_ne_zero ht lam b
    change f' t / P t - d * (lam + ((b / t : ℝ) : ℂ)) =
      (f' t - d * ((lam + ((b / t : ℝ) : ℂ)) * P t)) / P t
    field_simp
    <;> ring
  have hFnorm : Tendsto (fun t => ‖F' t‖ / w t) atTop (𝓝 0) := by
    have hh := hFlim.norm
    simp only [norm_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_div, powerExpProfile_norm ht]
  obtain ⟨D, hD⟩ := eventually_atTop.mp hdf
  obtain ⟨S, hS, hSb⟩ := powerExpWeight_tail_deriv_lower hlam b
  let T := max D S
  have hTS : S ≤ T := le_max_right _ _
  have hTD : D ≤ T := le_max_left _ _
  have htpos (t : ℝ) (ht : T ≤ t) : 0 < t :=
    lt_of_lt_of_le zero_lt_one (hS.trans (hTS.trans ht))
  have hdF (t : ℝ) (ht : T ≤ t) : HasDerivAt F (F' t) t :=
    (hD t (hTD.trans ht)).sub ((powerExpProfile_hasDerivAt (htpos t ht) lam b).const_mul d)
  have hzero : Tendsto (fun t => ‖F t‖ / w t) atTop (𝓝 0) :=
    norm_primitive_div_weight_tendsto_zero (half_pos hlam)
      (fun t ht => powerExpWeight_pos (htpos t ht) lam.re b)
      (powerExpWeight_tendsto hlam b)
      (fun t ht => powerExpWeight_hasDerivAt (htpos t ht) lam.re b)
      (fun t ht => hSb t (hTS.trans ht)) hdF hFnorm
  have hFzero : Tendsto (fun t => F t / P t) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply hzero.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_div, powerExpProfile_norm ht]
  have hh := hFzero.add_const d
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hp : P t ≠ 0 := powerExpProfile_ne_zero ht lam b
  change (f t - d * P t) / P t + d = f t / P t
  rw [sub_div, mul_div_cancel_right₀ d hp]
  ring

/-- Normalization in the literal form used for the manuscript's ray solutions. -/
theorem powerExp_primitive_normalized_limit {f f' : ℝ → ℂ} {lam c : ℂ} {b : ℝ}
    (hlam : 0 < lam.re)
    (hdf : ∀ᶠ t in atTop, HasDerivAt f (f' t) t)
    (hf : Tendsto (fun t : ℝ => t ^ (-b) • (Complex.exp (-lam * (t : ℂ)) • f' t))
      atTop (𝓝 c)) :
    Tendsto (fun t : ℝ => t ^ (-b) • (Complex.exp (-lam * (t : ℂ)) • f t))
      atTop (𝓝 (c / lam)) := by
  have hrat : Tendsto (fun t => f' t / powerExpProfile lam b t) atTop (𝓝 c) := by
    apply hf.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact powerExpProfile_normalization ht lam (f' t) b
  apply (powerExp_primitive_ratio_limit hlam hdf hrat).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (powerExpProfile_normalization ht lam (f t) b).symm

end ModifiedCartan
#print axioms ModifiedCartan.powerExp_primitive_ratio_limit
#print axioms ModifiedCartan.powerExp_primitive_normalized_limit



