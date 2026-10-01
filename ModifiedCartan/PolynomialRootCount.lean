import ModifiedCartan.PolynomialNegativeArea
import FewInflection.Nevanlinna.CountingBounds
import Mathlib.Analysis.Analytic.Polynomial
import ModifiedCartan.PolynomialApproximationCounting

open scoped Topology BigOperators Classical
open Filter Set Metric
set_option autoImplicit false

namespace ModifiedCartan
noncomputable section

 theorem meromorphicOrderAt_linear_factor (a z : ℂ) :
    meromorphicOrderAt (fun w => w - a) z = if z = a then 1 else 0 := by
  have han : AnalyticAt ℂ (fun w => w - a) z := by fun_prop
  rw [han.meromorphicOrderAt_eq]
  split_ifs with h
  · subst z
    simp
  · simp [analyticOrderAt_id_sub_const_of_ne h]

 theorem divisor_linear_factor_apply (a z : ℂ) (K : Set ℂ) :
    MeromorphicOn.divisor (fun w => w - a) K z = if z = a ∧ a ∈ K then 1 else 0 := by
  classical
  by_cases hz : z ∈ K
  · have hmer : MeromorphicOn (fun w : ℂ => w - a) K :=
      fun z _ => (show AnalyticAt ℂ (fun w => w - a) z by fun_prop).meromorphicAt
    rw [hmer.divisor_apply hz, meromorphicOrderAt_linear_factor]
    by_cases h : z = a
    · subst z; simp [hz]
    · simp [h]
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
    have hnot : ¬ (z = a ∧ a ∈ K) := by rintro ⟨rfl, ha⟩; exact hz ha
    simp only [hnot, ↓reduceIte]

 theorem divisor_const_mul (c : ℂ) (hc : c ≠ 0) {f : ℂ → ℂ} {K : Set ℂ}
    (hf : MeromorphicOn f K) :
    MeromorphicOn.divisor (fun z => c * f z) K = MeromorphicOn.divisor f K := by
  ext z
  by_cases hz : z ∈ K
  · have hprod : MeromorphicOn (fun z => c * f z) K :=
      fun z hz => (MeromorphicAt.const c z).mul (hf z hz)
    rw [hprod.divisor_apply hz, hf.divisor_apply hz]
    change (meromorphicOrderAt ((fun _ : ℂ => c) * f) z).untop₀ = _
    rw [meromorphicOrderAt_mul (by fun_prop) (hf z hz)]
    simp [meromorphicOrderAt_const, hc]
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

 theorem divisor_root_product_apply {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (K : Set ℂ) (z : ℂ) :
    MeromorphicOn.divisor (fun w => ∏ i ∈ S, (w - a i)) K z =
      ∑ i ∈ S, if z = a i ∧ a i ∈ K then (1 : ℤ) else 0 := by
  classical
  have he := MeromorphicOn.divisor_fun_prod
    (s := S) (f := fun i w => w - a i) (U := K)
    (fun i _ z _ => (show AnalyticAt ℂ (fun w => w - a i) z by fun_prop).meromorphicAt)
    (fun i _ z _ => by rw [meromorphicOrderAt_linear_factor]; split_ifs <;> simp)
  rw [he, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  simp only [divisor_linear_factor_apply]

 theorem divisor_root_product_count {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (K : Set ℂ) :
    (∑ᶠ z : ℂ, ((MeromorphicOn.divisor (fun w => ∏ i ∈ S, (w - a i)) K) z : ℝ)) =
      ((S.filter (fun i => a i ∈ K)).card : ℝ) := by
  classical
  simp_rw [divisor_root_product_apply, Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rw [finsum_sum_comm]
  · calc
      _ = ∑ i ∈ S, if a i ∈ K then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [finsum_eq_single _ (a i) (fun z hz => by simp [hz])]
        simp
      _ = _ := Finset.sum_boole _ _
  · intro i _
    apply (Set.finite_singleton (a i)).subset
    intro z hz
    by_contra h
    have hne : z ≠ a i := by simpa only [Set.mem_singleton_iff] using h
    simp [Function.mem_support, hne] at hz

 theorem polynomial_divisor_normalize (P : Polynomial ℂ) (K : Set ℂ) :
    MeromorphicOn.divisor (fun z => (normalize P).eval z) K =
      MeromorphicOn.divisor (fun z => P.eval z) K := by
  have he : (fun z => (normalize P).eval z) =
      (fun z => (normUnit P.leadingCoeff : ℂ) * P.eval z) := by
    funext z
    rw [normalize_apply, Polynomial.coe_normUnit, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [he]
  exact divisor_const_mul _ (normUnit P.leadingCoeff).ne_zero
    (fun z _ => (AnalyticOnNhd.eval_polynomial P z (mem_univ z)).meromorphicAt)

 theorem polynomial_root_list_count {M : ℕ} (P : Polynomial ℂ) (a : Fin M → ℂ)
    (hP : normalize P = ∏ i, (Polynomial.X - Polynomial.C (a i))) (K : Set ℂ) :
    (∑ᶠ z : ℂ, ((MeromorphicOn.divisor (fun w => P.eval w) K) z : ℝ)) =
      (((Finset.univ : Finset (Fin M)).filter (fun i => a i ∈ K)).card : ℝ) := by
  rw [← polynomial_divisor_normalize]
  have he : (fun z => (normalize P).eval z) = fun z => ∏ i, (z - a i) := by
    funext z
    rw [hP, Polynomial.eval_prod]
    simp
  rw [he]
  exact divisor_root_product_count Finset.univ a K

 theorem exists_normalized_polynomial_root_list (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ a : Fin P.natDegree → ℂ,
      normalize P = ∏ i, (Polynomial.X - Polynomial.C (a i)) := by
  have hd : (normalize P).natDegree = P.natDegree := by
    rw [normalize_apply, Polynomial.coe_normUnit,
      Polynomial.natDegree_mul_C (normUnit P.leadingCoeff).ne_zero]
  obtain ⟨a, ha⟩ := complex_monic_eq_prod_linear (normalize P)
    (Polynomial.monic_normalize hP) hd
  refine ⟨fun i => -a i, ?_⟩
  simpa only [map_neg, sub_neg_eq_add] using ha

theorem polynomial_approximation_root_count_le {M : ℕ} (P R : Polynomial ℂ)
    (hP : P.Monic) (a : Fin M → ℂ)
    (hR : normalize R = ∏ i, (Polynomial.X - Polynomial.C (a i)))
    (herr : ∀ z ∈ closedBall (0 : ℂ) 12, ‖R.eval z - P.eval z‖ ≤ 1 / 2) :
    (((Finset.univ : Finset (Fin M)).filter (fun i => ‖a i‖ ≤ 8)).card : ℝ) ≤
      localRootCountBound P.natDegree := by
  have hc := polynomial_approximation_divisor_count_le P R hP herr
  rw [polynomial_root_list_count R a hR] at hc
  simpa only [mem_closedBall, dist_zero_right] using hc

theorem localRootCountBound_div_scale_tendsto_zero (m : ℕ → ℕ) {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => (m ν : ℝ) / s ν) atTop (𝓝 0)) :
    Tendsto (fun ν => localRootCountBound (m ν) / s ν) atTop (𝓝 0) := by
  have hinv := tendsto_inv_atTop_zero.comp hs
  have ht := ((hinv.const_mul (Real.log 4)).add
    (hm.const_mul (1 + Real.log 12))).div_const (Real.log (10 / 9))
  simp only [mul_zero, add_zero, zero_div] at ht
  convert! ht using 1
  funext ν
  dsimp [localRootCountBound]
  ring

/-- The normalized interior root count tends to zero. The fixed split at
radius eight includes boundary roots on the inner side. This replaces only
the root-count input of `prop:localcompact`, not the Rouché equality. -/
theorem polynomial_approximation_root_count_tendsto_zero
    (P R : ℕ → Polynomial ℂ) (hP : ∀ ν, (P ν).Monic)
    (a : (ν : ℕ) → Fin (R ν).natDegree → ℂ)
    (hR : ∀ᶠ ν in atTop, normalize (R ν) = ∏ i, (Polynomial.X - Polynomial.C (a ν i)))
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((P ν).natDegree : ℝ) / s ν) atTop (𝓝 0))
    (herr : ∀ᶠ ν in atTop, ∀ z ∈ closedBall (0 : ℂ) 12,
      ‖(R ν).eval z - (P ν).eval z‖ ≤ 1 / 2) :
    Tendsto (fun ν =>
      (((Finset.univ : Finset (Fin (R ν).natDegree)).filter
        (fun i => ‖a ν i‖ ≤ 8)).card : ℝ) / s ν) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (localRootCountBound_div_scale_tendsto_zero (fun ν => (P ν).natDegree) hs hm)
  · filter_upwards [hs.eventually_gt_atTop 0] with ν hν
    exact div_nonneg (Nat.cast_nonneg _) hν.le
  · filter_upwards [hR, herr, hs.eventually_gt_atTop 0] with ν hRν heν hsν
    exact div_le_div_of_nonneg_right
      (polynomial_approximation_root_count_le (P ν) (R ν) (hP ν) (a ν) hRν heν) hsν.le

end
end ModifiedCartan
#print axioms ModifiedCartan.polynomial_root_list_count
#print axioms ModifiedCartan.exists_normalized_polynomial_root_list
#print axioms ModifiedCartan.polynomial_approximation_root_count_tendsto_zero
