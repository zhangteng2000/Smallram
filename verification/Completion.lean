import FewInflection.Results
import FewInflection.TargetSnapshot
import FewInflection.ExplicitExamples
import FewInflection.ExplicitHigherDim
import FewInflection.ExplicitExponentialFamily

/-!
Completion gate for the five frozen propositions.  This file is deliberately
non-claiming while the analytic certificates are still under construction.
It contains one target certificate (the conditional radial-area proposition)
and identity checks for all five specifications.  The other four target
certificates remain to be proved.
-/

namespace FewInflection

#check FrozenMainTheoremStatement
#check FrozenSharpnessStatement
#check FrozenSmallOrderStatement
#check FrozenZeroOrderStatement
#check FrozenRadialAreaStatement

example : @FrozenMainTheoremStatement = @MainTheoremStatement :=
  frozen_main_target_matches

example : FrozenSharpnessStatement = SharpnessStatement :=
  frozen_sharpness_target_matches

example : @FrozenSmallOrderStatement = @SmallOrderStatement :=
  frozen_small_order_target_matches

example : @FrozenZeroOrderStatement = @ZeroOrderStatement :=
  frozen_zero_order_target_matches

example : @FrozenRadialAreaStatement = @RadialAreaStatement :=
  frozen_radial_area_target_matches

/- This is an actual proof of the frozen radial-area target.  Its analytic
   input is exactly the `MainConclusion` and area/characteristic limit that
   the frozen proposition quantifies over. -/
theorem completion_radial_area_statement
    {n : ℕ} (f : Curve n) : FrozenRadialAreaStatement f := by
  simpa only [frozen_radial_area_target_matches] using
    (radial_area_statement_of_mainConclusion f)

#print axioms completion_radial_area_statement

/- A concrete fully proved instance of the main target for the normalized
   exponential curve.  This is an instance check, not a replacement for the
   universal frozen main theorem. -/
theorem completion_explicit_main_statement :
    FrozenMainTheoremStatement normalizedExponentialCurve := by
  simpa only [frozen_main_target_matches] using
      normalizedExponentialCurve_mainTheoremStatement

/- A higher-dimensional sharpness instance at the admissible order one is
   checked separately; it is not substituted for the universal frozen
   sharpness proposition. -/
theorem completion_higher_dim_order_one_sharpness
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ w : RealizationWitness n 1,
      w.curve.Transcendental ∧ w.curve.linearlyNonDegenerate ∧
      (∀ z, wronskian n w.curve.coord z = 1) :=
  exponentialMonomialRealization_sharpness_instance hn

/- A second high-dimensional order-one realization uses distinct exponential
   rates and a Vandermonde normalization. -/
theorem completion_exponential_family_order_one_sharpness
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ w : RealizationWitness n 1,
      w.curve.Transcendental ∧ w.curve.linearlyNonDegenerate ∧
      (∀ z, wronskian n w.curve.coord z = 1) :=
  exponentialFamily_realization_sharpness_instance hn

theorem completion_exponential_family_main_instance
    {n : ℕ} (hn : 1 ≤ n) :
    ∃ c : ℂ, ∃ hc : c ≠ 0,
      c ^ (n + 1) = (exponentialFamilyVandermonde n)⁻¹ ∧
      FrozenMainTheoremStatement (normalizedExponentialFamilyCurve n c hc) := by
  obtain ⟨c, hcpow⟩ := exists_complex_pow_eq n
    (exponentialFamilyVandermonde n)⁻¹
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_pow (by omega)] at hcpow
    exact (inv_ne_zero (exponentialFamilyVandermonde_ne_zero n)) hcpow.symm
  refine ⟨c, hc, hcpow, ?_⟩
  simpa only [frozen_main_target_matches] using
    normalizedExponentialFamily_mainTheoremStatement hn c hc hcpow

#print axioms completion_explicit_main_statement
#print axioms completion_higher_dim_order_one_sharpness
#print axioms completion_exponential_family_order_one_sharpness
#print axioms completion_exponential_family_main_instance

end FewInflection
