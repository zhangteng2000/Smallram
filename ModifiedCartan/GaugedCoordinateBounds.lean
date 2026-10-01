import ModifiedCartan.CurveCoordinateCounting
import ModifiedCartan.CanonicalProductGrowth
import ModifiedCartan.GenusZeroGauge
import ModifiedCartan.EntirePoissonBound

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Coordinates of the single scalar gauge in `lem:small-order-coordinates`. -/
noncomputable def gaugedCoordinates {n : ℕ} (f : Curve n) (G : ℂ → ℂ)
    (j : Index n) (z : ℂ) : ℂ := Complex.exp (-G z) * f.coord j z

theorem gaugedCoordinates_differentiable {n : ℕ} (f : Curve n) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (j : Index n) : Differentiable ℂ (gaugedCoordinates f G j) := by
  exact (Complex.differentiable_exp.comp hG.neg).mul (f.holomorphic j)

theorem gaugedCoordinates_zero_eq_product {n : ℕ} (f : Curve n) {G : ℂ → ℂ}
    (he : ∀ z, f.coord 0 z = genusZeroProduct (f.coord 0) z * Complex.exp (G z)) (z : ℂ) :
    gaugedCoordinates f G 0 z = genusZeroProduct (f.coord 0) z := by
  unfold gaugedCoordinates
  rw [he z, Complex.exp_neg]
  field_simp

theorem gaugedCoordinates_eq_product_quotient {n : ℕ} (f : Curve n) {G : ℂ → ℂ}
    (h0 : f.coord 0 0 ≠ 0)
    (he : ∀ z, f.coord 0 z = genusZeroProduct (f.coord 0) z * Complex.exp (G z))
    (j : Index n) :
    gaugedCoordinates f G j =ᶠ[codiscrete ℂ]
      genusZeroProduct (f.coord 0) * (fun z => f.coord j z / f.coord 0 z) := by
  have hn : ∀ᶠ z in codiscrete ℂ, f.coord 0 z ≠ 0 :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (f.holomorphic 0)).preimage_zero_mem_codiscrete h0
  filter_upwards [hn] with z hz
  change Complex.exp (-G z) * f.coord j z =
    genusZeroProduct (f.coord 0) z * (f.coord j z / f.coord 0 z)
  have hp : genusZeroProduct (f.coord 0) z = Complex.exp (-G z) * f.coord 0 z :=
    (gaugedCoordinates_zero_eq_product f he z).symm
  rw [hp]
  field_simp

theorem entire_proximity_le_posLog_maximumModulus {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) :
    ValueDistribution.proximity f ⊤ r ≤ Real.posLog (maximumModulus f r) := by
  rw [ValueDistribution.proximity_top]
  apply Real.circleAverage_mono_on_of_le_circle
    (Real.continuous_posLog.comp hf.continuous.norm).continuousOn.circleIntegrable'
  intro z hz
  apply Real.posLog_le_posLog (norm_nonneg _)
  apply norm_le_maximumModulus hf.continuous
  rw [abs_of_pos hr] at hz
  exact sphere_subset_closedBall hz

/-- The scalar characteristic estimate used for the fixed gauge in
Step 1 of LaTeX `lem:small-order-coordinates`. -/
theorem gaugedCoordinates_characteristic_le {n : ℕ} (f : Curve n) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (h0 : f.coord 0 0 ≠ 0)
    (he : ∀ z, f.coord 0 z = genusZeroProduct (f.coord 0) z * Complex.exp (G z))
    (hs : Summable (fun a : entireZeroCopies (f.coord 0) => ‖a.1‖⁻¹))
    (j : Index n) {r : ℝ} (hr : 1 ≤ r) :
    ValueDistribution.characteristic (gaugedCoordinates f G j) ⊤ r ≤
      Real.posLog (maximumModulus (genusZeroProduct (f.coord 0)) r) +
        characteristic f r + Real.log (euclideanNorm (f.vector 0)) - Real.log ‖f.coord 0 0‖ := by
  have hp := genusZeroProduct_differentiable hs
  have hpm : Meromorphic (genusZeroProduct (f.coord 0)) := fun z => (hp.analyticAt z).meromorphicAt
  have hqm : Meromorphic (fun z => f.coord j z / f.coord 0 z) := fun z =>
    (f.holomorphic j |>.analyticAt z).meromorphicAt.div (f.holomorphic 0 |>.analyticAt z).meromorphicAt
  have hg := gaugedCoordinates_differentiable f hG j
  have hmul := ValueDistribution.proximity_mul_top_le hpm hqm r
  have hpbound := entire_proximity_le_posLog_maximumModulus hp (zero_lt_one.trans_le hr)
  have hqbound := Paper.eq_quotientbound f 0 j h0 hr
  have hqn : 0 ≤ ValueDistribution.logCounting (fun z => f.coord j z / f.coord 0 z) ⊤ r :=
    ValueDistribution.logCounting_nonneg hr
  rw [entire_characteristic_eq_circleAverage_posLog hg, ← ValueDistribution.proximity_top,
    ValueDistribution.proximity_congr_codiscrete
      (gaugedCoordinates_eq_product_quotient f h0 he j) (zero_lt_one.trans_le hr).ne']
  dsimp only [ValueDistribution.characteristic, Pi.add_apply] at hqbound hmul
  linarith

theorem coordinate_genusZeroProduct_power_bound {n : ℕ} (f : Curve n)
    (h0 : f.coord 0 0 ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβ : order f < (β : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      Real.posLog (maximumModulus (genusZeroProduct (f.coord 0)) r) ≤ C * r ^ β := by
  obtain ⟨C, hC, hc⟩ := coordinate_zeroCount_power_bound f 0 h0 hβ0 hβ
  obtain ⟨D, hD, hN⟩ := coordinate_logCounting_power_bound f 0 h0 hβ0 hβ
  refine ⟨C * Real.log 2 + D + C / (1 - β), ?_, fun r hr =>
    genusZeroProduct_posLog_power_bound (f.holomorphic 0) h0 hβ1 hC.le hc hN hr⟩
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 1 - β := by linarith
  positivity

theorem gaugedCoordinates_characteristic_power_bound {n : ℕ} (f : Curve n) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (h0 : f.coord 0 0 ≠ 0)
    (he : ∀ z, f.coord 0 z = genusZeroProduct (f.coord 0) z * Complex.exp (G z))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβ : order f < (β : EReal))
    (j : Index n) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ValueDistribution.characteristic (gaugedCoordinates f G j) ⊤ r ≤ C * r ^ β := by
  obtain ⟨C, hC, hP⟩ := coordinate_genusZeroProduct_power_bound f h0 hβ0 hβ1 hβ
  obtain ⟨D, hD, hT⟩ := order_exists_characteristic_power_bound f hβ
  have hs := coordinate_reciprocal_roots_summable f 0 h0 hβ0 hβ1 hβ
  let E := |Real.log (euclideanNorm (f.vector 0)) - Real.log ‖f.coord 0 0‖|
  refine ⟨C + D + E, by dsimp only [E]; positivity, ?_⟩
  intro r hr
  have hcount := gaugedCoordinates_characteristic_le f hG h0 he hs j hr
  have hp := hP r hr
  have ht := hT r hr
  have he0 : Real.log (euclideanNorm (f.vector 0)) - Real.log ‖f.coord 0 0‖ ≤ E := le_abs_self _
  have hE : 0 ≤ E := abs_nonneg _
  have hpow : 1 ≤ r ^ β := Real.one_le_rpow hr hβ0
  have hEp : E ≤ E * r ^ β := by nlinarith
  nlinarith

/-- Every exponent above the original curve order bounds the very same
gauged coordinate; G is not reselected when the exponent changes. -/
theorem gaugedCoordinates_posLog_power_bound {n : ℕ} (f : Curve n) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (h0 : f.coord 0 0 ≠ 0)
    (he : ∀ z, f.coord 0 z = genusZeroProduct (f.coord 0) z * Complex.exp (G z))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβ : order f < (β : EReal))
    (j : Index n) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      Real.posLog (maximumModulus (gaugedCoordinates f G j) r) ≤ C * r ^ β := by
  obtain ⟨C, hC, hc⟩ := gaugedCoordinates_characteristic_power_bound f hG h0 he hβ0 hβ1 hβ j
  refine ⟨3 * C * (2 : ℝ) ^ β, by positivity, ?_⟩
  intro r hr
  have hP := entire_posLog_maximumModulus_le_three_characteristic
    (gaugedCoordinates_differentiable f hG j) (zero_lt_one.trans_le hr)
  have hC2 := mul_le_mul_of_nonneg_left (hc (2 * r) (by linarith)) (by norm_num : (0 : ℝ) ≤ 3)
  apply hP.trans
  apply hC2.trans_eq
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (zero_le_one.trans hr)]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.gaugedCoordinates_characteristic_le
#print axioms ModifiedCartan.coordinate_genusZeroProduct_power_bound
#print axioms ModifiedCartan.gaugedCoordinates_posLog_power_bound
