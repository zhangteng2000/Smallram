import ModifiedCartan.TranslatedZeroCopies
import ModifiedCartan.TranslationWeightBound
import ModifiedCartan.NormalizedCoordinates
import ModifiedCartan.CountingDilation
import ModifiedCartan.WronskianReciprocalRoots
import ModifiedCartan.Convolution

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

#check Summable.tsum_le_tsum
#check Summable.tsum_add
#check Summable.mul_left

/-- A uniform bound for translation of the actual zero counting function.
The hypothesis is applied below to the normalized Wronskian, whose
reciprocal-root summability has already been proved from its order. -/
theorem translated_logCounting_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    (b : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    ValueDistribution.logCounting f (0 : WithTop ℂ) t ≤
      ValueDistribution.logCounting (fun z => f (z - b)) (0 : WithTop ℂ) (t + ‖b‖) +
        (‖b‖ + 1) * ∑' a : entireZeroCopies f, ‖a.1‖⁻¹ := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hR : 0 < t + ‖b‖ := by linarith [norm_nonneg b]
  have hleft : Summable (fun a : entireZeroCopies f => Real.posLog (t / ‖a.1‖)) :=
    summable_of_hasFiniteSupport (zeroCopy_posLog_hasFiniteSupport hf ht0.le)
  have hright := translated_zeroCopy_weights_summable hf b hR.le
  have herr := hs.mul_left (‖b‖ + 1)
  rw [entire_logCounting_eq_tsum_zeroCopies hf h0 ht0,
    translated_logCounting_eq_tsum hf b hR, ← tsum_mul_left, ← hright.tsum_add herr]
  exact hleft.tsum_le_tsum (fun a => rootCountingWeight_translate_bound
    (entireZeroCopies_ne_zero hf h0 a) b ht) (hright.add herr)

/-- Counting identity for the translated normalized Wronskian. -/
theorem normalizedCoordinates_translated_counting {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) {b : ℂ}
    (hW : FewInflection.wronskian n g b ≠ 0) (R : ℝ) :
    ValueDistribution.logCounting
      (fun z => FewInflection.wronskian n (normalizedCoordinates g b) (z - b))
      (0 : WithTop ℂ) R = ValueDistribution.logCounting (FewInflection.wronskian n g)
      (0 : WithTop ℂ) R := by
  have he : (fun z => FewInflection.wronskian n (normalizedCoordinates g b) (z - b)) =
      fun z => (FewInflection.jetMatrix g b)⁻¹.det * FewInflection.wronskian n g z := by
    funext z
    have hbz : b + (z - b) = z := by ring
    rw [normalizedCoordinates_wronskian hg, hbz, mul_comm]
  rw [he]
  exact logCounting_const_mul (entire_wronskian_differentiable hg) ⟨b, hW⟩
    (normalizedCoordinates_inverse_det_ne_zero hg hW) R

/-- LaTeX `eq:translated-count` before the zero-free scalar gauge.
All summability assumptions are derived from the component orders. -/
theorem normalizedCoordinates_counting_bound {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) (ho : ∀ j, entireOrder (g j) < 1)
    {b : ℂ} (hW : FewInflection.wronskian n g b ≠ 0) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → systemCounting (normalizedCoordinates g b) t ≤
      ValueDistribution.logCounting (FewInflection.wronskian n g) (0 : WithTop ℂ)
        (t + ‖b‖) + C := by
  have hy := normalizedCoordinates_differentiable hg b
  have hjets := normalizedCoordinates_initialJets hg hW
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := finite_entireOrder_exists_exponent_lt_one ho
  have hyorder (j : Index n) : entireOrder (normalizedCoordinates g b j) < 1 := by
    apply (normalizedCoordinates_entireOrder_le hg b (ρ := (ρ : EReal))
      (by exact_mod_cast hρ0.le) (fun k => (hρ k).le) j).trans_lt
    exact_mod_cast hρ1
  have hs := (normalized_entire_system_reciprocal_roots hy hyorder hjets).1
  refine ⟨(‖b‖ + 1) * ∑' a : entireZeroCopies
    (FewInflection.wronskian n (normalizedCoordinates g b)), ‖a.1‖⁻¹, ?_⟩
  intro t ht
  have hzero : FewInflection.wronskian n (normalizedCoordinates g b) 0 ≠ 0 := by
    rw [normalizedCoordinates_wronskian_zero hg hW]
    exact one_ne_zero
  have hh := translated_logCounting_bound (entire_wronskian_differentiable hy) hzero hs b ht
  rw [normalizedCoordinates_translated_counting hg hW] at hh
  exact hh

end ModifiedCartan
#print axioms ModifiedCartan.translated_logCounting_bound
#print axioms ModifiedCartan.normalizedCoordinates_counting_bound
