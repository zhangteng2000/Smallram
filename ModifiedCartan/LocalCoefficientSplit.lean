import ModifiedCartan.LocalRootSeparation
import ModifiedCartan.SubsetProductBounds
import ModifiedCartan.PolynomialFamilyExpansion
import ModifiedCartan.MeasureConvergenceAlgebra

open scoped Topology BigOperators Classical
open Filter MeasureTheory Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

def scaledReciprocalRoot (a : ℂ) (s : ℝ) (z : ℂ) : ℂ := (z - a)⁻¹ / (s : ℂ)

def rootSubsetSum {M : ℕ} (S : Finset (Fin M)) (a : Fin M → ℂ)
    (γ : Finset (Fin M) → ℂ) (s : ℝ) (q : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ q * ∑ I ∈ S.powersetCard q, γ I * ∏ i ∈ I, scaledReciprocalRoot (a i) s z

def interiorRootSubsetSum {M : ℕ} (a : Fin M → ℂ) (γ : Finset (Fin M) → ℂ)
    (s : ℝ) (q : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ q *
    ∑ I ∈ ((Finset.univ : Finset (Fin M)).powersetCard q).filter
      (fun I => ¬Disjoint I (interiorRootIndices a)),
      γ I * ∏ i ∈ I, scaledReciprocalRoot (a i) s z

theorem prod_scaledReciprocalRoot {M : ℕ} (I : Finset (Fin M)) (a : Fin M → ℂ)
    (s : ℝ) (z : ℂ) :
    (∏ i ∈ I, scaledReciprocalRoot (a i) s z) =
      (∏ i ∈ I, (z - a i))⁻¹ / (s : ℂ) ^ I.card := by
  simp only [scaledReciprocalRoot, Finset.prod_div_distrib,
    Finset.prod_inv_distrib, Finset.prod_const]

theorem rootSubsetSum_eq_quotient {M : ℕ} (S : Finset (Fin M)) (a : Fin M → ℂ)
    (γ : Finset (Fin M) → ℂ) (s : ℝ) (q : ℕ) (z : ℂ) :
    rootSubsetSum S a γ s q z =
      ((-1 : ℂ) ^ q * ∑ I ∈ S.powersetCard q, γ I / ∏ i ∈ I, (z - a i)) / (s : ℂ) ^ q := by
  unfold rootSubsetSum
  rw [mul_div_assoc, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [prod_scaledReciprocalRoot, (Finset.mem_powersetCard.mp hI).2]
  ring

theorem powersetCard_disjoint_interior {M : ℕ} (a : Fin M → ℂ) (q : ℕ) :
    ((Finset.univ : Finset (Fin M)).powersetCard q).filter
      (fun I => Disjoint I (interiorRootIndices a)) = (exteriorRootIndices a).powersetCard q := by
  ext I
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, hd⟩
    refine ⟨?_, hcard⟩
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra h
    have hin : i ∈ interiorRootIndices a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩
    exact Finset.disjoint_left.mp hd hi hin
  · rintro ⟨hsub, hcard⟩
    refine ⟨⟨fun i _ => Finset.mem_univ i, hcard⟩, Finset.disjoint_left.mpr ?_⟩
    intro i hi hin
    have ho : 8 < ‖a i‖ := (Finset.mem_filter.mp (hsub hi)).2
    have hi' : ‖a i‖ ≤ 8 := (Finset.mem_filter.mp hin).2
    linarith

/-- Exact finite algebraic split underlying manuscript `eq:splitcoeff`. -/
theorem rootSubsetSum_split {M : ℕ} (a : Fin M → ℂ) (γ : Finset (Fin M) → ℂ)
    (s : ℝ) (q : ℕ) (z : ℂ) :
    rootSubsetSum Finset.univ a γ s q z =
      rootSubsetSum (exteriorRootIndices a) a γ s q z + interiorRootSubsetSum a γ s q z := by
  unfold rootSubsetSum interiorRootSubsetSum
  rw [← mul_add, ← powersetCard_disjoint_interior]
  rw [Finset.sum_filter_add_sum_filter_not]

theorem norm_scaledReciprocalRoot (a : ℂ) {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    ‖scaledReciprocalRoot a s z‖ = ‖z - a‖⁻¹ / s := by
  rw [scaledReciprocalRoot, norm_div, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs]

theorem sum_norm_scaledReciprocalRoot {M : ℕ} (S : Finset (Fin M)) (a : Fin M → ℂ)
    {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    (∑ i ∈ S, ‖scaledReciprocalRoot (a i) s z‖) = reciprocalDistanceSum S a z / s := by
  simp_rw [norm_scaledReciprocalRoot _ hs]
  rw [← Finset.sum_div]
  rfl

theorem norm_rootSubsetSum_le {M : ℕ} (S : Finset (Fin M)) (a : Fin M → ℂ)
    (γ : Finset (Fin M) → ℂ) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hγ : ∀ I, ‖γ I‖ ≤ C) (q : ℕ) (z : ℂ) :
    ‖rootSubsetSum S a γ s q z‖ ≤
      C * Real.exp 1 * (1 + reciprocalDistanceSum S a z / s) ^ q := by
  unfold rootSubsetSum
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hb := norm_powersetCard_product_sum_le S (fun i => scaledReciprocalRoot (a i) s z) γ q hC hγ
  rwa [sum_norm_scaledReciprocalRoot S a hs z] at hb

theorem norm_marked_univ_product_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (v : ι → ℂ) (γ : Finset ι → ℂ) (q : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hγ : ∀ I, ‖γ I‖ ≤ C) :
    ‖∑ I ∈ ((Finset.univ : Finset ι).powersetCard q).filter (fun I => ¬Disjoint I A),
      γ I * ∏ i ∈ I, v i‖ ≤ C * (∑ i ∈ A, ‖v i‖) * Real.exp 1 *
        (1 + ∑ i, ‖v i‖) ^ q := by
  have hb := norm_marked_powersetCard_product_sum_le Finset.univ A v γ q hC hγ
  simp only [Finset.sum_filter] at hb ⊢
  convert! hb using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro I _
    by_cases h : Disjoint I A <;> simp [h]
  · congr 3
    symm
    exact @Finset.sum_ite_mem_eq ι ℝ _ _ A (fun i => ‖v i‖)
      (fun i => @Finset.decidableMem ι (Classical.decEq ι) i A)

theorem norm_interiorRootSubsetSum_le {M : ℕ} (a : Fin M → ℂ)
    (γ : Finset (Fin M) → ℂ) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hγ : ∀ I, ‖γ I‖ ≤ C) (q : ℕ) (z : ℂ) :
    ‖interiorRootSubsetSum a γ s q z‖ ≤
      C * (reciprocalDistanceSum (interiorRootIndices a) a z / s) * Real.exp 1 *
        (1 + reciprocalDistanceSum Finset.univ a z / s) ^ q := by
  unfold interiorRootSubsetSum
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hb := norm_marked_univ_product_sum_le
    (interiorRootIndices a) (fun i => scaledReciprocalRoot (a i) s z) γ q hC hγ
  simpa only [sum_norm_scaledReciprocalRoot _ a hs z] using hb

theorem exteriorRootSubsetSum_analytic {M : ℕ} (a : Fin M → ℂ)
    (γ : Finset (Fin M) → ℂ) (s : ℝ) (q : ℕ) :
    AnalyticOnNhd ℂ (rootSubsetSum (exteriorRootIndices a) a γ s q) (ball 0 8) := by
  intro z hz
  have hz' : ‖z‖ < 8 := by simpa only [mem_ball, dist_zero_right] using hz
  unfold rootSubsetSum
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro I hI
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro i hi
  have hout : 8 < ‖a i‖ := (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hI).1 hi)).2
  have hza : z - a i ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    rw [he] at hz'
    linarith
  convert! ((show AnalyticAt ℂ (fun w => w - a i) z by fun_prop).inv hza).mul
    (show AnalyticAt ℂ (fun _ : ℂ => (s : ℂ)⁻¹) z from analyticAt_const) using 1

theorem rootSubsetSum_measurable {M : ℕ} (S : Finset (Fin M)) (a : Fin M → ℂ)
    (γ : Finset (Fin M) → ℂ) (s : ℝ) (q : ℕ) :
    Measurable (rootSubsetSum S a γ s q) := by
  unfold rootSubsetSum scaledReciprocalRoot
  fun_prop

theorem norm_exteriorRootSubsetSum_le {M : ℕ} (a : Fin M → ℂ)
    (γ : Finset (Fin M) → ℂ) {s C D : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hγ : ∀ I, ‖γ I‖ ≤ C) (q : ℕ) (z : ℂ)
    (houter : reciprocalDistanceSum (exteriorRootIndices a) a z / s ≤ D) :
    ‖rootSubsetSum (exteriorRootIndices a) a γ s q z‖ ≤ C * Real.exp 1 * (1 + D) ^ q := by
  apply (norm_rootSubsetSum_le (exteriorRootIndices a) a γ hs hC hγ q z).trans
  have ho : 0 ≤ reciprocalDistanceSum (exteriorRootIndices a) a z / s :=
    div_nonneg (reciprocalDistanceSum_nonneg _ _ _) hs
  gcongr

theorem linear_root_product_ne_zero_ae {M : ℕ} (a : Fin M → ℂ) :
    ∀ᵐ z : ℂ, (∏ i, (z - a i)) ≠ 0 := by
  have hnot : ∀ᵐ z : ℂ, z ∉ Set.range a := by
    rw [ae_iff]
    simp only [not_not]
    change volume (Set.range a) = 0
    exact (Set.finite_range a).measure_zero (volume : Measure ℂ)
  filter_upwards [hnot] with z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ hi
  exact hz ⟨i, (sub_eq_zero.mp hi).symm⟩

/-- The actual normalized polynomial differential coefficients split almost
everywhere into the exterior-root and interior-root expressions. Auxiliary
to LaTeX `eq:splitcoeff`; no product-form expansion is assumed. -/
theorem polynomialFamily_normalized_coefficient_split_ae {M n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (hp : FewInflection.polynomialWronskian p ≠ 0)
    (a : Fin M → ℂ)
    (hW : normalize (FewInflection.polynomialWronskian p) =
      ∏ i, (Polynomial.X - Polynomial.C (a i))) :
    ∃ γ : ℕ → Finset (Fin M) → ℂ,
      (∀ q I, ‖γ q I‖ ≤ (q.factorial : ℝ)) ∧
      ∀ (q : ℕ) (hq0 : 1 ≤ q) (hqn : q ≤ n + 1) (s : ℝ),
        (fun z => FewInflection.fundamentalCoefficients n (fun j w => (p j).eval w) z
          ⟨n + 1 - q, by omega⟩ / (s : ℂ) ^ q) =ᵐ[volume]
        (fun z => rootSubsetSum (exteriorRootIndices a) a (γ q) s q z +
          interiorRootSubsetSum a (γ q) s q z) := by
  obtain ⟨γ, hb, he⟩ := polynomialFamily_product_expansion p hp a hW
  refine ⟨γ, hb, ?_⟩
  intro q hq0 hqn s
  filter_upwards [linear_root_product_ne_zero_ae a] with z hz
  rw [← rootSubsetSum_split, rootSubsetSum_eq_quotient, he q hq0 hqn z hz]

theorem interiorRootSubsetSum_measurable {M : ℕ} (a : Fin M → ℂ)
    (γ : Finset (Fin M) → ℂ) (s : ℝ) (q : ℕ) :
    Measurable (interiorRootSubsetSum a γ s q) := by
  unfold interiorRootSubsetSum scaledReciprocalRoot
  fun_prop

theorem norm_interiorRootSubsetSum_le_outer_bound {M : ℕ} (a : Fin M → ℂ)
    (γ : Finset (Fin M) → ℂ) {s C D : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hγ : ∀ I, ‖γ I‖ ≤ C) (q : ℕ) (z : ℂ)
    (houter : reciprocalDistanceSum (exteriorRootIndices a) a z / s ≤ D) :
    ‖interiorRootSubsetSum a γ s q z‖ ≤
      C * (reciprocalDistanceSum (interiorRootIndices a) a z / s) * Real.exp 1 *
        (1 + reciprocalDistanceSum (interiorRootIndices a) a z / s + D) ^ q := by
  apply (norm_interiorRootSubsetSum_le a γ hs hC hγ q z).trans
  have hi : 0 ≤ reciprocalDistanceSum (interiorRootIndices a) a z / s :=
    div_nonneg (reciprocalDistanceSum_nonneg _ _ _) hs
  have ho : 0 ≤ reciprocalDistanceSum (exteriorRootIndices a) a z / s :=
    div_nonneg (reciprocalDistanceSum_nonneg _ _ _) hs
  rw [← reciprocalDistanceSum_split a z, add_div]
  have hb : 1 + (reciprocalDistanceSum (interiorRootIndices a) a z / s +
      reciprocalDistanceSum (exteriorRootIndices a) a z / s) ≤
      1 + reciprocalDistanceSum (interiorRootIndices a) a z / s + D := by linarith
  gcongr

theorem tendstoInMeasure_zero_of_norm_le {α E : Type*} [MeasurableSpace α]
    [SeminormedAddCommGroup E] {μ : Measure α} {f : ℕ → α → E} {g : ℕ → α → ℝ}
    (hg : TendstoInMeasure μ g atTop (fun _ => 0))
    (hbound : ∀ᶠ ν in atTop, ∀ᵐ x ∂μ, ‖f ν x‖ ≤ g ν x) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hg ⊢
  intro ε hε
  have hlim := hg ε hε
  simp only [sub_zero] at hlim ⊢
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hbound] with ν hν
  apply measure_mono_ae
  filter_upwards [hν] with x hx
  intro hεx
  exact hεx.trans (hx.trans (le_abs_self _))

/-- Vanishing of the interior-root coefficient error in Step 4 of
`prop:localcompact`. Uses a coarser generating-product bound than `eq:F-bound`,
with the same local convergence conclusion and no root-number-dependent constant. -/
theorem interiorRootSubsetSum_localMeasure_zero {M : ℕ → ℕ}
    (a : (ν : ℕ) → Fin (M ν) → ℂ) (γ : (ν : ℕ) → Finset (Fin (M ν)) → ℂ)
    {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hm : Tendsto (fun ν => ((interiorRootIndices (a ν)).card : ℝ) / s ν) atTop (𝓝 0))
    {C D : ℝ} (hC : 0 ≤ C) (hγ : ∀ ν I, ‖γ ν I‖ ≤ C)
    (houter : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 6,
      reciprocalDistanceSum (exteriorRootIndices (a ν)) (a ν) z / s ν ≤ D) (q : ℕ) :
    LocalMeasureConvergence (ball (0 : ℂ) 6)
      (fun ν => interiorRootSubsetSum (a ν) (γ ν) (s ν) q) (fun _ => 0) := by
  let u := fun ν z => reciprocalDistanceSum (interiorRootIndices (a ν)) (a ν) z / s ν
  have hu : LocalMeasureConvergence (ball (0 : ℂ) 6) u (fun _ => (0 : ℝ)) :=
    inner_root_sum_localMeasure_zero (fun ν => interiorRootIndices (a ν)) a
      (fun ν i hi => (Finset.mem_filter.mp hi).2) hs hm
  let Φ := fun x : ℝ => C * x * Real.exp 1 * (1 + x + D) ^ q
  have hΦ : Continuous Φ := by fun_prop
  have hzero : Φ 0 = 0 := by simp [Φ]
  have hb := hu.continuous_map
    (fun K _ _ ν => by dsimp [u, reciprocalDistanceSum]; fun_prop) hΦ
  simp only [hzero] at hb
  intro K hK hKU
  apply tendstoInMeasure_zero_of_norm_le (hb K hK hKU)
  filter_upwards [houter, hs.eventually_gt_atTop 0] with ν hν hsν
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact norm_interiorRootSubsetSum_le_outer_bound (a ν) (γ ν) hsν.le hC (hγ ν) q z
    (hν z (hKU hz))

end
end ModifiedCartan
#print axioms ModifiedCartan.rootSubsetSum_split
#print axioms ModifiedCartan.norm_interiorRootSubsetSum_le
#print axioms ModifiedCartan.exteriorRootSubsetSum_analytic
#print axioms ModifiedCartan.interiorRootSubsetSum_localMeasure_zero
