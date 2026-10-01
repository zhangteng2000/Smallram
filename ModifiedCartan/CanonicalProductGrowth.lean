import ModifiedCartan.GenusZeroProduct
import ModifiedCartan.ReciprocalRoots
import ModifiedCartan.ZeroCopyLogCounting
import ModifiedCartan.MaximumModulus

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem log_one_add_ratio_le_head {r a : ℝ} (ha : 0 < a) (har : a ≤ r) :
    Real.log (1 + r / a) ≤ Real.log 2 + Real.posLog (r / a) := by
  have hrat : 1 ≤ r / a := (one_le_div ha).mpr har
  rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; exact hrat),
    ← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : r / a ≠ 0)]
  apply Real.log_le_log (by positivity)
  linarith

theorem zeroCopy_head_sum {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 ≤ r) (c : ℝ) :
    (∑' a : entireZeroCopies f, if ‖a.1‖ ≤ r then c else 0) = zeroCount f r * c := by
  classical
  letI : Finite (zeroCopiesInClosedBall f r) := zeroCopiesInClosedBall_finite hf hr
  letI := Fintype.ofFinite (zeroCopiesInClosedBall f r)
  have ht := tsum_subtype {a : entireZeroCopies f | ‖a.1‖ ≤ r} (fun _ => c)
  have he : (∑' a : entireZeroCopies f, if ‖a.1‖ ≤ r then c else 0) =
      ∑' _a : zeroCopiesInClosedBall f r, c := by
    simpa only [Set.indicator, mem_setOf_eq] using! ht.symm
  rw [he, tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, zeroCopiesInClosedBall_card hf hr]

set_option maxHeartbeats 800000 in
/-- The literal head/count/tail decomposition from LaTeX
`eq:canonical-product-growth`, first for the majorizing root product. -/
theorem log_rootMajorantProduct_le_split {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) {r : ℝ} (hr : 0 < r) :
    Real.log (rootMajorantProduct f r) ≤ zeroCount f r * Real.log 2 +
      ValueDistribution.logCounting f (0 : WithTop ℂ) r +
      r * ∑' a : entireZeroCopies f, if r < ‖a.1‖ then ‖a.1‖⁻¹ else 0 := by
  classical
  have hfin : {a : entireZeroCopies f | ‖a.1‖ ≤ r}.Finite :=
    @Set.toFinite (entireZeroCopies f) {a | ‖a.1‖ ≤ r}
      (zeroCopiesInClosedBall_finite hf hr.le)
  have hhead : Summable (fun a : entireZeroCopies f =>
      if ‖a.1‖ ≤ r then Real.log 2 else 0) := by
    apply summable_of_hasFiniteSupport
    apply hfin.subset
    intro a ha
    by_contra hn
    change ¬ ‖a.1‖ ≤ r at hn
    exact ha (by simp [hn])
  have hcount : Summable (fun a : entireZeroCopies f => Real.posLog (r / ‖a.1‖)) :=
    summable_of_hasFiniteSupport (zeroCopy_posLog_hasFiniteSupport hf hr.le)
  have htail : Summable (fun a : entireZeroCopies f =>
      if r < ‖a.1‖ then ‖a.1‖⁻¹ else 0) := by
    simpa only [Set.indicator, mem_setOf_eq] using! hs.indicator {a | r < ‖a.1‖}
  have hpoint (a : entireZeroCopies f) :
      Real.log (1 + r / ‖a.1‖) ≤
      ((if ‖a.1‖ ≤ r then Real.log 2 else 0) + Real.posLog (r / ‖a.1‖)) +
        r * (if r < ‖a.1‖ then ‖a.1‖⁻¹ else 0) := by
    have ha : 0 < ‖a.1‖ := norm_pos_iff.mpr (entireZeroCopies_ne_zero hf h0 a)
    by_cases har : ‖a.1‖ ≤ r
    · simpa only [if_pos har, if_neg (not_lt.mpr har), mul_zero, add_zero] using
        log_one_add_ratio_le_head ha har
    · have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + r / ‖a.1‖ by positivity)
      rw [if_neg har, if_pos (lt_of_not_ge har),
        posLog_div_norm_eq_zero_of_lt hr.le (lt_of_not_ge har), zero_add, zero_add]
      simpa only [add_sub_cancel_left, div_eq_mul_inv] using hlog
  have hbound := (rootMajorant_log_summable hs r).tsum_le_tsum hpoint
    ((hhead.add hcount).add (htail.mul_left r))
  rw [(hhead.add hcount).tsum_add (htail.mul_left r), hhead.tsum_add hcount,
    htail.tsum_mul_left, zeroCopy_head_sum hf hr.le,
    ← entire_logCounting_eq_tsum_zeroCopies hf h0 hr,
    ← log_rootMajorantProduct hs hr.le] at hbound
  exact hbound

theorem rootMajorantProduct_mono {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    rootMajorantProduct f r ≤ rootMajorantProduct f s := by
  rw [rootMajorantProduct_eq_exp hs hr, rootMajorantProduct_eq_exp hs (hr.trans hrs)]
  apply Real.exp_le_exp.mpr
  apply (rootMajorant_log_summable hs r).tsum_le_tsum _ (rootMajorant_log_summable hs s)
  intro a
  apply Real.log_le_log (by positivity)
  have hh := div_le_div_of_nonneg_right hrs (norm_nonneg a.1)
  linarith

theorem genusZeroProduct_maximumModulus_le_rootMajorant {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus (genusZeroProduct f) r ≤ rootMajorantProduct f r := by
  apply maximumModulus_le hr
  intro z hz
  exact (genusZeroProduct_norm_le_rootMajorant hs z).trans
    (rootMajorantProduct_mono hs (norm_nonneg z)
      (by simpa only [mem_closedBall, dist_zero_right] using hz))

theorem one_le_genusZeroProduct_maximumModulus {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) {r : ℝ} (hr : 0 ≤ r) :
    1 ≤ maximumModulus (genusZeroProduct f) r := by
  simpa only [genusZeroProduct_zero, norm_one] using
    norm_le_maximumModulus (genusZeroProduct_differentiable hs).continuous (mem_closedBall_self hr)

namespace Paper
/-- LaTeX `eq:canonical-product-growth`, the exact head/count/tail
inequality for the single fixed actual canonical product. -/
theorem eq_canonical_product_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) {r : ℝ} (hr : 0 < r) :
    Real.log (maximumModulus (genusZeroProduct f) r) ≤ zeroCount f r * Real.log 2 +
      ValueDistribution.logCounting f (0 : WithTop ℂ) r +
      r * ∑' a : entireZeroCopies f, if r < ‖a.1‖ then ‖a.1‖⁻¹ else 0 :=
  (Real.log_le_log (zero_lt_one.trans_le (one_le_genusZeroProduct_maximumModulus hs hr.le))
    (genusZeroProduct_maximumModulus_le_rootMajorant hs hr.le)).trans
      (log_rootMajorantProduct_le_split hf h0 hs hr)
end Paper

theorem genusZeroProduct_posLog_power_bound {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {β C D : ℝ}
    (hβ1 : β < 1) (hC : 0 ≤ C)
    (hc : ∀ r, 1 ≤ r → zeroCount f r ≤ C * r ^ β)
    (hN : ∀ r, 1 ≤ r → ValueDistribution.logCounting f (0 : WithTop ℂ) r ≤ D * r ^ β)
    {r : ℝ} (hr : 1 ≤ r) :
    Real.posLog (maximumModulus (genusZeroProduct f) r) ≤
      (C * Real.log 2 + D + C / (1 - β)) * r ^ β := by
  have hs := entire_reciprocal_roots_summable_of_count_bound hf hC hβ1 hc
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [Real.posLog_eq_log (by
    rw [abs_of_nonneg (zero_le_one.trans (one_le_genusZeroProduct_maximumModulus hs hr0.le))]
    exact one_le_genusZeroProduct_maximumModulus hs hr0.le)]
  apply (Paper.eq_canonical_product_growth hf h0 hs hr0).trans
  have hh := mul_le_mul_of_nonneg_right (hc r hr) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have ht := mul_le_mul_of_nonneg_left
    (entire_reciprocal_tail_of_count_bound hf hC hβ1 hr hc).2 hr0.le
  have he : r * (C / (1 - β) * r ^ (β - 1)) = C / (1 - β) * r ^ β := by
    rw [Real.rpow_sub hr0, Real.rpow_one]
    field_simp
  rw [he] at ht
  have hn := hN r hr
  nlinarith

end ModifiedCartan
#print axioms ModifiedCartan.log_rootMajorantProduct_le_split
#print axioms ModifiedCartan.Paper.eq_canonical_product_growth
#print axioms ModifiedCartan.genusZeroProduct_posLog_power_bound
