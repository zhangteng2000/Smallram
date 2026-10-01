import FewInflection.PolynomialSpaces

open scoped BigOperators Topology
open Filter Asymptotics
open Metric Set

namespace FewInflection

noncomputable section

/-! ### The explicit polynomial model

For the finite-product norm used by `Curve.vector`, the monomial model has a
closed formula on every circle of radius at least one.  This is a small but
useful exact growth calculation: the largest coordinate is the degree-`n`
coordinate, and the circle average is consequently constant on the circle.
-/

lemma monomial_vector_norm_on_sphere {n : ℕ} {r : ℝ} (hr : 1 ≤ r)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) |r|) :
    ‖(monomialCurve n).vector z‖ = r ^ n := by
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have habs : |r| = r := abs_of_nonneg hr0
  have hzabs : ‖z‖ = r := by
    have hdist := (Metric.mem_sphere.mp hz)
    rw [dist_zero_right, habs] at hdist
    exact hdist
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonempty]
    intro k
    change ‖z ^ (k : ℕ)‖ ≤ r ^ n
    rw [norm_pow, hzabs]
    exact pow_le_pow_right₀ hr (Nat.le_of_lt_succ k.isLt)
  · let kn : Index n := ⟨n, Nat.lt_succ_self n⟩
    have hk : ‖z ^ (kn : ℕ)‖ ≤ ‖(monomialCurve n).vector z‖ :=
      norm_le_pi_norm ((monomialCurve n).vector z) kn
    change r ^ n ≤ ‖(monomialCurve n).vector z‖
    rw [show (kn : ℕ) = n by rfl, norm_pow, hzabs] at hk
    exact hk

lemma monomial_vector_norm_zero (n : ℕ) :
    ‖(monomialCurve n).vector 0‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonempty]
    intro k
    change ‖(0 : ℂ) ^ (k : ℕ)‖ ≤ 1
    rw [norm_pow]
    by_cases hk : (k : ℕ) = 0 <;> simp [hk]
  · have h0 := norm_le_pi_norm ((monomialCurve n).vector 0) (0 : Index n)
    have hcoord : ‖(monomialCurve n).vector 0 (0 : Index n)‖ = 1 := by
      simp [monomialCurve, Curve.vector, monomialFamily]
    rw [hcoord] at h0
    exact h0

lemma characteristic_monomialCurve_atTop {n : ℕ} {r : ℝ} (hr : 1 ≤ r) :
    characteristic (monomialCurve n) r = Real.log (r ^ n) := by
  unfold characteristic
  have havg : Real.circleAverage
      (fun z : ℂ => Real.log ‖(monomialCurve n).vector z‖) 0 r =
      Real.circleAverage (fun _ : ℂ => Real.log (r ^ n)) 0 r := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    change Real.log ‖(monomialCurve n).vector z‖ = Real.log (r ^ n)
    rw [monomial_vector_norm_on_sphere hr hz]
  rw [havg, Real.circleAverage_const, monomial_vector_norm_zero]
  simp

theorem monomialCurve_order_zero (n : ℕ) :
    order (monomialCurve n) = (0 : EReal) ∧
      lowerOrder (monomialCurve n) = (0 : EReal) := by
  by_cases hn : n = 0
  · subst n
    have heq : (fun r : ℝ => logGrowthRatio (monomialCurve 0) r) =ᶠ[atTop]
        (fun _ => (0 : EReal)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      unfold logGrowthRatio
      rw [characteristic_monomialCurve_atTop hr]
      simp
    have hlim : Tendsto (fun r : ℝ => logGrowthRatio (monomialCurve 0) r)
        atTop (𝓝 (0 : EReal)) := by
      exact (tendsto_const_nhds.congr' heq.symm)
    exact ⟨by unfold order; exact hlim.limsup_eq,
      by unfold lowerOrder; exact hlim.liminf_eq⟩
  · have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_ne_zero hn)
    have hnone : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    let q : ℝ → ℝ := fun r =>
      (Real.log (n : ℝ) + Real.log (Real.log r)) / Real.log r
    have hconst : Tendsto (fun r : ℝ => Real.log (n : ℝ) / Real.log r)
        atTop (𝓝 0) := Real.tendsto_log_atTop.const_div_atTop _
    have hllittle := Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    have hll : Tendsto (fun r : ℝ => Real.log (Real.log r) / Real.log r)
        atTop (𝓝 0) := by
      simpa [Function.comp_def] using hllittle.tendsto_div_nhds_zero
    have hq : Tendsto q atTop (𝓝 0) := by
      simpa [q, add_div] using hconst.add hll
    have hqE : Tendsto (fun r => (q r : EReal)) atTop (𝓝 (0 : EReal)) := by
      rw [tendsto_order]
      constructor
      · intro a ha
        cases a with
        | bot => filter_upwards [] with r; simp
        | coe a =>
          have ha' : a < (0 : ℝ) := by simpa using ha
          have h := (tendsto_order.1 hq).1 a ha'
          filter_upwards [h] with r hr
          exact EReal.coe_lt_coe_iff.2 hr
        | top => simp at ha
      · intro a ha
        cases a with
        | bot => simp at ha
        | coe a =>
          have ha' : (0 : ℝ) < a := by simpa using ha
          have h := (tendsto_order.1 hq).2 a ha'
          filter_upwards [h] with r hr
          exact EReal.coe_lt_coe_iff.2 hr
        | top => filter_upwards [] with r; simp
    let qE : ℝ → EReal := fun r => (q r : EReal)
    have heq : (fun r : ℝ => logGrowthRatio (monomialCurve n) r) =ᶠ[atTop] qE := by
      filter_upwards [eventually_ge_atTop (max (Real.exp 1) 2 : ℝ)] with r hr
      have hr2 : 2 ≤ r := le_trans (le_max_right _ _) hr
      have hr1 : 1 ≤ r := le_trans (by norm_num) hr2
      have hlog1 : 1 ≤ Real.log r := by
        apply (Real.le_log_iff_exp_le (by positivity)).2
        exact le_trans (le_max_left _ _) hr
      have hlogpos : 0 < Real.log r := lt_of_lt_of_le zero_lt_one hlog1
      have hnlog : 1 ≤ (n : ℝ) * Real.log r := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (n : ℝ) * Real.log r :=
            mul_le_mul hnone hlog1 (by positivity) (by positivity)
      unfold logGrowthRatio
      rw [characteristic_monomialCurve_atTop hr1, Real.log_pow]
      rw [max_eq_left hnlog, max_eq_left hr2]
      rw [Real.log_mul (ne_of_gt hnpos) (ne_of_gt hlogpos)]
    have hlim : Tendsto (fun r : ℝ => logGrowthRatio (monomialCurve n) r)
        atTop (𝓝 (0 : EReal)) := by
      simpa [qE] using hqE.congr' heq.symm
    exact ⟨by unfold order; exact hlim.limsup_eq,
      by unfold lowerOrder; exact hlim.liminf_eq⟩

theorem smallOrderStatement_monomialCurve (n : ℕ) :
    SmallOrderStatement (monomialCurve n) := by
  intro _ _ _ _
  exact ⟨monomialCurve_rationalNormalForm n,
    (monomialCurve_order_zero n).1⟩

end

end FewInflection
