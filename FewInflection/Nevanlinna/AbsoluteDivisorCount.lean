import FewInflection.Nevanlinna.CountingBounds

/-!
# Absolute divisor mass in a fixed disk

The signed divisor of a meromorphic function splits into its positive and
negative parts.  This file records the exact finite-support identity for the
absolute mass on a closed disk and the corresponding logarithmic-counting
bound.  It is the bookkeeping needed to turn the singular-kernel estimate
into a characteristic estimate without assuming that zeros and poles have
one sign.
-/

open scoped BigOperators Topology
open Filter Function Function.locallyFinsuppWithin MeromorphicOn Metric Real Set
open ValueDistribution

namespace FewInflection

theorem toClosedBall_natAbs_finsum_eq_pos_neg_finsums
    {D : locallyFinsupp ℂ ℤ} :
    (∑ᶠ z : ℂ, (((toClosedBall 3 D) z).natAbs : ℝ)) =
      (∑ᶠ z : ℂ, (((toClosedBall 3 D⁺) z : ℤ) : ℝ)) +
      (∑ᶠ z : ℂ, (((toClosedBall 3 D⁻) z : ℤ) : ℝ)) := by
  let U : locallyFinsuppWithin (closedBall (0 : ℂ) |(3 : ℝ)|) ℤ :=
    toClosedBall 3 D
  let Up : locallyFinsuppWithin (closedBall (0 : ℂ) |(3 : ℝ)|) ℤ :=
    toClosedBall 3 D⁺
  let Un : locallyFinsuppWithin (closedBall (0 : ℂ) |(3 : ℝ)|) ℤ :=
    toClosedBall 3 D⁻
  have hUp : (Up.support).Finite := Up.finiteSupport (isCompact_closedBall _ _)
  have hUn : (Un.support).Finite := Un.finiteSupport (isCompact_closedBall _ _)
  have hfp : Function.HasFiniteSupport (fun z : ℂ => ((Up z : ℤ) : ℝ)) := by
    apply hUp.subset
    intro z hz
    change (Up z : ℝ) ≠ 0 at hz
    change Up z ≠ 0
    intro hz0
    apply hz
    simp [hz0]
  have hfn : Function.HasFiniteSupport (fun z : ℂ => ((Un z : ℤ) : ℝ)) := by
    apply hUn.subset
    intro z hz
    change (Un z : ℝ) ≠ 0 at hz
    change Un z ≠ 0
    intro hz0
    apply hz
    simp [hz0]
  have hpoint : ∀ z : ℂ,
      ((U z : ℤ).natAbs : ℝ) = Int.cast (Up z : ℤ) + Int.cast (Un z : ℤ) := by
    intro z
    by_cases hz : z ∈ closedBall (0 : ℂ) |(3 : ℝ)|
    · have hU : U z = D z := by
        dsimp [U]
        exact toClosedBall_eval_within D hz
      have hUp' : Up z = (D z)⁺ := by
        dsimp [Up]
        rw [toClosedBall_eval_within D⁺ hz]
        rfl
      have hUn' : Un z = (D z)⁻ := by
        dsimp [Un]
        rw [toClosedBall_eval_within D⁻ hz]
        rfl
      rw [hU, hUp', hUn']
      have habs : |D z| = (D z)⁺ + (D z)⁻ := by
        change |D z| = max (D z) 0 + max (-(D z)) 0
        rcases le_total 0 (D z) with hd | hd
        · rw [max_eq_left hd, max_eq_right (by omega), abs_of_nonneg hd]
          omega
        · rw [max_eq_right hd, max_eq_left (by omega), abs_of_nonpos hd]
          omega
      have habsR : ((D z).natAbs : ℝ) =
          Int.cast ((D z)⁺) + Int.cast ((D z)⁻) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        norm_cast
      exact habsR
    · have hU : U z = 0 := by
        dsimp [U]
        exact locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz
      have hUp' : Up z = 0 := by
        dsimp [Up]
        exact locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz
      have hUn' : Un z = 0 := by
        dsimp [Un]
        exact locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz
      rw [hU, hUp', hUn']
      norm_num
  have hadd :
      (∑ᶠ z : ℂ, (((Up z : ℤ) : ℝ) + ((Un z : ℤ) : ℝ))) =
        (∑ᶠ z : ℂ, ((Up z : ℤ) : ℝ)) +
          (∑ᶠ z : ℂ, ((Un z : ℤ) : ℝ)) :=
    finsum_add_distrib hfp hfn
  rw [← hadd]
  apply finsum_congr
  intro z
  simpa [U, Up, Un] using hpoint z

theorem toClosedBall_natAbs_finsum_mul_log_four_thirds_le_parts
    {D : locallyFinsupp ℂ ℤ} (hD0 : D 0 = 0) :
    (∑ᶠ z : ℂ, (((toClosedBall 3 D) z).natAbs : ℝ)) * Real.log (4 / 3) ≤
      D⁺.logCounting 4 + D⁻.logCounting 4 := by
  have hD0p : D⁺ 0 = 0 := by simp [hD0]
  have hD0n : D⁻ 0 = 0 := by simp [hD0]
  have hcount := add_divisor_count_mul_log_four_thirds_le_add_logCounting
    (D₁ := D⁺) (D₂ := D⁻) (posPart_nonneg D) (negPart_nonneg D) hD0p hD0n
  rw [toClosedBall_natAbs_finsum_eq_pos_neg_finsums]
  exact hcount

theorem meromorphic_toClosedBall_natAbs_finsum_mul_log_four_thirds_le_counts
    {f : ℂ → ℂ} (hf : Meromorphic f) (hfa : AnalyticAt ℂ f 0)
    (h0 : f 0 ≠ 0) :
    (∑ᶠ z : ℂ, (((toClosedBall 3 (divisor f Set.univ)) z).natAbs : ℝ)) *
        Real.log (4 / 3) ≤
      ValueDistribution.logCounting f ⊤ 4 +
        ValueDistribution.logCounting (fun z : ℂ => (f z)⁻¹) ⊤ 4 := by
  have hD0 : (divisor f Set.univ) 0 = 0 := by
    rw [hf.meromorphicOn.divisor_apply (Set.mem_univ _)]
    rw [hfa.meromorphicOrderAt_eq,
      hfa.analyticOrderAt_eq_zero.mpr h0]
    rfl
  have hparts := toClosedBall_natAbs_finsum_mul_log_four_thirds_le_parts hD0
  have htopf : ValueDistribution.logCounting f ⊤ 4 =
      (divisor f Set.univ)⁻.logCounting 4 := by
    rw [ValueDistribution.logCounting_top]
  have htopinv : ValueDistribution.logCounting (fun z : ℂ => (f z)⁻¹) ⊤ 4 =
      (divisor f Set.univ)⁺.logCounting 4 := by
    rw [ValueDistribution.logCounting_top, divisor_fun_inv]
    simp
  rw [htopf, htopinv]
  simpa [add_comm] using hparts

theorem finset_divisor_abs_sum_le_toClosedBall_natAbs_finsum
    {f : ℂ → ℂ} (hf : Meromorphic f) {R : ℝ}
    (hR3 : R ≤ 3) (s : Finset ℂ)
    (hsupport : ∀ a ∈ s, divisor f (ball 0 R) a ≠ 0) :
    ∑ a ∈ s, |(divisor f (ball 0 R) a : ℝ)| ≤
      ∑ᶠ z : ℂ, (((toClosedBall 3 (divisor f Set.univ)) z).natAbs : ℝ) := by
  let D : locallyFinsuppWithin (ball (0 : ℂ) R) ℤ := divisor f (ball 0 R)
  let G : locallyFinsuppWithin (closedBall (0 : ℂ) |(3 : ℝ)|) ℤ :=
    toClosedBall 3 (divisor f Set.univ)
  let u : ℂ → ℝ := fun a => if a ∈ s then |(D a : ℝ)| else 0
  let g : ℂ → ℝ := fun a => ((G a : ℤ).natAbs : ℝ)
  have hG : G.support.Finite := G.finiteSupport (isCompact_closedBall _ _)
  have hgf : Function.HasFiniteSupport g := by
    apply hG.subset
    intro a ha
    change ((G a).natAbs : ℝ) ≠ 0 at ha
    change G a ≠ 0
    intro hz
    apply ha
    simp [hz]
  have hus : Function.support u ⊆ (s : Set ℂ) := by
    intro a ha
    by_contra hna
    apply ha
    have hna' : a ∉ s := by simpa using hna
    simp [u, hna']
  have hterm : ∀ a ∈ s, u a = g a := by
    intro a ha
    have haD : D a ≠ 0 := by simpa [D] using hsupport a ha
    have haBall : a ∈ ball (0 : ℂ) R := D.supportWithinDomain haD
    have ha3 : a ∈ closedBall (0 : ℂ) |(3 : ℝ)| := by
      rw [mem_closedBall_zero_iff]
      have hanorm : ‖a‖ < R := by simpa [mem_ball_zero_iff] using haBall
      exact le_trans (le_of_lt hanorm) (by simpa using hR3)
    have hdiv : divisor f Set.univ a = divisor f (ball 0 R) a := by
      rw [hf.meromorphicOn.divisor_apply (Set.mem_univ _),
        (hf.meromorphicOn.mono_set (subset_univ _)).divisor_apply haBall]
    have hGval : G a = divisor f Set.univ a := by
      dsimp [G]
      exact toClosedBall_eval_within _ ha3
    simp only [u, if_pos ha, g]
    rw [hGval, hdiv, Nat.cast_natAbs, Int.cast_abs]
  have hleug : u ≤ g := by
    intro a
    by_cases ha : a ∈ s
    · exact le_of_eq (hterm a ha)
    · simp [u, ha]
      positivity
  have hu' : Function.HasFiniteSupport u := by
    apply s.finite_toSet.subset
    intro a ha
    exact hus ha
  have hsumu : ∑ᶠ a : ℂ, u a = ∑ a ∈ s, |(divisor f (ball 0 R) a : ℝ)| := by
    rw [finsum_eq_sum_of_support_subset u hus]
    simp [u, D]
  have hfinle := finsum_le_finsum' hu' hgf hleug
  rw [hsumu] at hfinle
  simpa [G, g] using hfinle

end FewInflection
