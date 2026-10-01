import ModifiedCartan.ScalarRamificationBridge
import ModifiedCartan.LocalPairCharacteristic

open scoped Topology
open Filter Set Metric MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

/-- Global scalar Jensen in a reduced pair. The trailing coefficient allows
zeros of the denominator at the center, hence also a scalar pole at zero. -/
theorem scalarCharacteristic_eq_pair_mean {f p q : ℂ → ℂ} (hf : Meromorphic f)
    (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (hred : ∀ z, p z ≠ 0 ∨ q z ≠ 0) (hqn : ∃ z, q z ≠ 0)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => p z / q z))
    (hD : divisor q univ = (divisor f univ)⁻) {r : ℝ} (hr : r ≠ 0) :
    scalarCharacteristic f r =
      Real.circleAverage (fun z => Real.log (max ‖p z‖ ‖q z‖)) 0 r -
        Real.log ‖meromorphicTrailingCoeffAt q 0‖ := by
  have hqU : MeromorphicOn q univ := fun z _ => (hq.analyticAt z).meromorphicAt
  have hne := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hqU
    (fun z _ => entire_meromorphicOrder_ne_top hq hqn z)
  have hlogeq : (fun z => Real.posLog ‖f z‖) =ᶠ[codiscreteWithin (univ : Set ℂ)]
      (fun z => Real.log (max ‖p z‖ ‖q z‖) - Real.log ‖q z‖) := by
    filter_upwards [he, hne] with z hz hzq
    rw [hz]
    have h := log_max_norm_eq_posLog_div_add (p z) (q z) hzq
    linarith
  have hmaxc : Continuous (fun z => Real.log (max ‖p z‖ ‖q z‖)) :=
    continuousOn_univ.mp (local_pair_log_norm_continuous hp.continuous.continuousOn
      hq.continuous.continuousOn (fun z _ => hred z))
  have hmax : CircleIntegrable (fun z => Real.log (max ‖p z‖ ‖q z‖)) 0 r :=
    hmaxc.continuousOn.circleIntegrable'
  have hlogq : CircleIntegrable (fun z => Real.log ‖q z‖) 0 r :=
    (hqU.mono_set (subset_univ _)).circleIntegrable_log_norm
  have havg := Real.circleAverage_congr_codiscreteWithin
    (hlogeq.filter_mono (codiscreteWithin_mono (subset_univ (sphere (0 : ℂ) |r|)))) hr
  rw [Real.circleAverage_fun_sub hmax hlogq] at havg
  have hN : ValueDistribution.logCounting f ⊤ r =
      (divisor q univ).logCounting r := by rw [ValueDistribution.logCounting_top, ← hD]
  rw [scalarCharacteristic, ValueDistribution.characteristic, Pi.add_apply,
    ValueDistribution.proximity_top, havg, hN,
    Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
      (fun z => (hq.analyticAt z).meromorphicAt) hr]
  ring

theorem scalar_curve_vector_norm (F : Curve 1) (z : ℂ) :
    ‖F.vector z‖ = max ‖F.coord 1 z‖ ‖F.coord 0 z‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (le_max_left _ _))).mpr
    intro j
    fin_cases j
    · exact le_max_right _ _
    · exact le_max_left _ _
  · exact max_le (norm_le_pi_norm (F.vector z) 1) (norm_le_pi_norm (F.vector z) 0)

theorem scalarCharacteristic_eq_curve_max_mean {f : ℂ → ℂ} (hf : Meromorphic f)
    (F : Curve 1) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (hD : divisor (F.coord 0) univ = (divisor f univ)⁻) {r : ℝ} (hr : r ≠ 0) :
    scalarCharacteristic f r = FewInflection.characteristic F r +
      Real.log ‖F.vector 0‖ - Real.log ‖meromorphicTrailingCoeffAt (F.coord 0) 0‖ := by
  have hred (z : ℂ) : F.coord 1 z ≠ 0 ∨ F.coord 0 z ≠ 0 := by
    obtain ⟨j, hj⟩ := F.reduced z
    fin_cases j
    · exact Or.inr hj
    · exact Or.inl hj
  rw [scalarCharacteristic_eq_pair_mean hf (F.holomorphic 1) (F.holomorphic 0)
    hred (scalar_curve_coordinate_nontrivial F hlin 0) he hD hr]
  simp only [FewInflection.characteristic, scalar_curve_vector_norm]
  ring

/-- A uniform bounded difference between the classical scalar and manuscript
Euclidean curve characteristics, with no condition on the value at zero. -/
theorem scalarCharacteristic_abs_sub_curve_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (F : Curve 1) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (hD : divisor (F.coord 0) univ = (divisor f univ)⁻) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, r ≠ 0 →
      |scalarCharacteristic f r - characteristic F r| ≤ C := by
  let c := Real.log ‖F.vector 0‖ - Real.log ‖meromorphicTrailingCoeffAt (F.coord 0) 0‖
  refine ⟨|c| + |Real.log (Real.sqrt 2)| + 1, by positivity, fun r hr => ?_⟩
  have hb := characteristic_abs_sub_le F r
  have hid : scalarCharacteristic f r - characteristic F r =
      c + (FewInflection.characteristic F r - characteristic F r) := by
    rw [scalarCharacteristic_eq_curve_max_mean hf F hlin he hD hr]
    dsimp only [c]
    ring
  rw [hid]
  have htri := abs_add_le c (FewInflection.characteristic F r - characteristic F r)
  rw [abs_sub_comm (FewInflection.characteristic F r)] at htri
  have hlog := le_abs_self (Real.log (Real.sqrt 2))
  norm_num only [Nat.cast_one, one_add_one_eq_two] at hb
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.scalarCharacteristic_eq_pair_mean
#print axioms ModifiedCartan.scalarCharacteristic_abs_sub_curve_le
