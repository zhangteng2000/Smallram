import ModifiedCartan.LocalJetDeterminantBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

open scoped BigOperators Classical
set_option autoImplicit false
namespace ModifiedCartan

/-- A product perturbation estimate with a sum of individual errors and no
factor depending on the number of factors. Used for `eq:F-bound`. -/
theorem prod_one_add_difference_le {ι : Type*} (S : Finset ι) (x y : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hxy : ∀ i, y i ≤ x i) :
    (∏ i ∈ S, (1 + x i)) - (∏ i ∈ S, (1 + y i)) ≤
      (∑ i ∈ S, (x i - y i)) * ∏ i ∈ S, (1 + x i) := by
  classical
  have hx (i : ι) : 0 ≤ x i := (hy i).trans (hxy i)
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hprod : (∏ j ∈ S, (1 + y j)) ≤ ∏ j ∈ S, (1 + x j) := by
      apply Finset.prod_le_prod (fun j _ => by linarith [hy j])
      intro j _
      linarith [hxy j]
    have hpx : 0 ≤ ∏ j ∈ S, (1 + x j) := Finset.prod_nonneg (fun j _ => by linarith [hx j])
    have hdiff : 0 ≤ x i - y i := sub_nonneg.mpr (hxy i)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      _ = (1 + x i) * ((∏ j ∈ S, (1 + x j)) - ∏ j ∈ S, (1 + y j)) +
          (x i - y i) * ∏ j ∈ S, (1 + y j) := by ring
      _ ≤ (1 + x i) * ((∑ j ∈ S, (x j - y j)) * ∏ j ∈ S, (1 + x j)) +
          (x i - y i) * ∏ j ∈ S, (1 + x j) := by
        gcongr
        · linarith [hx i]
      _ ≤ (1 + x i) * ((∑ j ∈ S, (x j - y j)) * ∏ j ∈ S, (1 + x j)) +
          (1 + x i) * ((x i - y i) * ∏ j ∈ S, (1 + x j)) := by
        have hnon := mul_nonneg (hx i) (mul_nonneg hdiff hpx)
        nlinarith
      _ = _ := by ring

 theorem powersetCard_product_sum_le_exp_one {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hSum : ∑ i ∈ S, x i ≤ 1) (q : ℕ) :
    (∑ I ∈ S.powersetCard q, ∏ i ∈ I, x i) ≤ Real.exp 1 := by
  calc
    _ ≤ ∑ I ∈ S.powerset, ∏ i ∈ I, x i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro I hI
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hI).1
      · intro I _ _
        exact Finset.prod_nonneg (fun i _ => hx i)
    _ = ∏ i ∈ S, (1 + x i) := (Finset.prod_one_add S).symm
    _ ≤ Real.exp (∑ i ∈ S, x i) := Real.prod_one_add_le_exp_sum S hx
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hSum

 theorem powersetCard_product_difference_le_exp_one {ι : Type*} (S : Finset ι)
    (x y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) (hxy : ∀ i, y i ≤ x i)
    (hSum : ∑ i ∈ S, x i ≤ 1) (q : ℕ) :
    (∑ I ∈ S.powersetCard q, ((∏ i ∈ I, x i) - ∏ i ∈ I, y i)) ≤
      (∑ i ∈ S, (x i - y i)) * Real.exp 1 := by
  have hx (i : ι) : 0 ≤ x i := (hy i).trans (hxy i)
  have hd : 0 ≤ ∑ i ∈ S, (x i - y i) := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hxy i))
  calc
    _ ≤ ∑ I ∈ S.powerset, ((∏ i ∈ I, x i) - ∏ i ∈ I, y i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro I hI
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hI).1
      · intro I _ _
        exact sub_nonneg.mpr (Finset.prod_le_prod (fun i _ => hy i) (fun i _ => hxy i))
    _ = (∏ i ∈ S, (1 + x i)) - ∏ i ∈ S, (1 + y i) := by
      rw [Finset.sum_sub_distrib, ← Finset.prod_one_add, ← Finset.prod_one_add]
    _ ≤ (∑ i ∈ S, (x i - y i)) * ∏ i ∈ S, (1 + x i) := prod_one_add_difference_le S x y hy hxy
    _ ≤ (∑ i ∈ S, (x i - y i)) * Real.exp 1 := by
      apply mul_le_mul_of_nonneg_left _ hd
      exact (Real.prod_one_add_le_exp_sum S hx).trans (Real.exp_le_exp.mpr hSum)

theorem powersetCard_product_sum_div {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (T : ℝ) (q : ℕ) :
    (∑ I ∈ S.powersetCard q, ∏ i ∈ I, (x i / T)) =
      (∑ I ∈ S.powersetCard q, ∏ i ∈ I, x i) / T ^ q := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hI).2]

/-- A degree-dependent bound independent of the number of roots. The added
one makes the normalizing denominator positive even for the empty list. -/
theorem powersetCard_product_sum_le {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (q : ℕ) :
    (∑ I ∈ S.powersetCard q, ∏ i ∈ I, x i) ≤
      Real.exp 1 * (1 + ∑ i ∈ S, x i) ^ q := by
  let T := 1 + ∑ i ∈ S, x i
  have hS : 0 ≤ ∑ i ∈ S, x i := Finset.sum_nonneg (fun i _ => hx i)
  have hT : 0 < T := by dsimp [T]; linarith
  have hsum : ∑ i ∈ S, x i / T ≤ 1 := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hT).mpr
    dsimp [T]
    linarith
  have hb := powersetCard_product_sum_le_exp_one S (fun i => x i / T)
    (fun i => div_nonneg (hx i) hT.le) hsum q
  rw [powersetCard_product_sum_div] at hb
  exact (div_le_iff₀ (pow_pos hT q)).mp hb

theorem powersetCard_product_difference_le {ι : Type*} (S : Finset ι)
    (x y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) (hxy : ∀ i, y i ≤ x i) (q : ℕ) :
    (∑ I ∈ S.powersetCard q, ((∏ i ∈ I, x i) - ∏ i ∈ I, y i)) ≤
      (∑ i ∈ S, (x i - y i)) * Real.exp 1 * (1 + ∑ i ∈ S, x i) ^ q := by
  have hx (i : ι) : 0 ≤ x i := (hy i).trans (hxy i)
  let T := 1 + ∑ i ∈ S, x i
  have hS : 0 ≤ ∑ i ∈ S, x i := Finset.sum_nonneg (fun i _ => hx i)
  have hT : 0 < T := by dsimp [T]; linarith
  have hsum : ∑ i ∈ S, x i / T ≤ 1 := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hT).mpr
    dsimp [T]
    linarith
  have hb := powersetCard_product_difference_le_exp_one S (fun i => x i / T)
    (fun i => y i / T) (fun i => div_nonneg (hy i) hT.le)
    (fun i => div_le_div_of_nonneg_right (hxy i) hT.le) hsum q
  have hd : 0 ≤ ∑ i ∈ S, (x i - y i) := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hxy i))
  have hratio : ∑ i ∈ S, (x i / T - y i / T) ≤ ∑ i ∈ S, (x i - y i) := by
    simp_rw [← sub_div]
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hT).mpr
    dsimp [T]
    nlinarith
  have hscaled : (∑ I ∈ S.powersetCard q, ((∏ i ∈ I, x i) - ∏ i ∈ I, y i)) / T ^ q ≤
      (∑ i ∈ S, (x i - y i)) * Real.exp 1 := by
    have he : (∑ I ∈ S.powersetCard q,
        ((∏ i ∈ I, x i / T) - ∏ i ∈ I, y i / T)) =
        (∑ I ∈ S.powersetCard q, ((∏ i ∈ I, x i) - ∏ i ∈ I, y i)) / T ^ q := by
      rw [Finset.sum_sub_distrib, powersetCard_product_sum_div, powersetCard_product_sum_div,
        ← sub_div, ← Finset.sum_sub_distrib]
    rw [he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hratio (Real.exp_pos 1).le)
  exact (div_le_iff₀ (pow_pos hT q)).mp hscaled

theorem prod_zeroed_eq {ι : Type*} (I A : Finset ι) (x : ι → ℝ) :
    (∏ i ∈ I, if i ∈ A then 0 else x i) = if Disjoint I A then ∏ i ∈ I, x i else 0 := by
  classical
  by_cases h : Disjoint I A
  · simp only [h, ↓reduceIte]
    apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ A := fun hA => Finset.disjoint_left.mp h hi hA
    simp only [hn, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    obtain ⟨i, hi, hA⟩ := Finset.not_disjoint_iff.mp h
    exact Finset.prod_eq_zero hi (by simp only [hA, ↓reduceIte])

theorem marked_powersetCard_product_sum_le {ι : Type*} (S A : Finset ι)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (q : ℕ) :
    (∑ I ∈ (S.powersetCard q).filter (fun I => ¬Disjoint I A), ∏ i ∈ I, x i) ≤
      (∑ i ∈ S.filter (fun i => i ∈ A), x i) * Real.exp 1 *
        (1 + ∑ i ∈ S, x i) ^ q := by
  let y := fun i => if i ∈ A then (0 : ℝ) else x i
  have hy (i : ι) : 0 ≤ y i := by
    dsimp [y]
    split_ifs
    · exact le_rfl
    · exact hx i
  have hxy (i : ι) : y i ≤ x i := by dsimp [y]; split_ifs <;> simp_all
  have hb := powersetCard_product_difference_le S x y hy hxy q
  have he : (∑ I ∈ S.powersetCard q, ((∏ i ∈ I, x i) - ∏ i ∈ I, y i)) =
      ∑ I ∈ (S.powersetCard q).filter (fun I => ¬Disjoint I A), ∏ i ∈ I, x i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I _
    change (∏ i ∈ I, x i) - (∏ i ∈ I, if i ∈ A then 0 else x i) = _
    rw [prod_zeroed_eq]
    by_cases h : Disjoint I A <;> simp [h]
  have hd : (∑ i ∈ S, (x i - y i)) = ∑ i ∈ S.filter (fun i => i ∈ A), x i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [y]
    split_ifs <;> simp
  rwa [he, hd] at hb

theorem norm_powersetCard_product_sum_le {ι : Type*} (S : Finset ι)
    (v : ι → ℂ) (γ : Finset ι → ℂ) (q : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hγ : ∀ I, ‖γ I‖ ≤ C) :
    ‖∑ I ∈ S.powersetCard q, γ I * ∏ i ∈ I, v i‖ ≤
      C * Real.exp 1 * (1 + ∑ i ∈ S, ‖v i‖) ^ q := by
  calc
    _ ≤ ∑ I ∈ S.powersetCard q, ‖γ I * ∏ i ∈ I, v i‖ := norm_sum_le _ _
    _ ≤ ∑ I ∈ S.powersetCard q, C * ∏ i ∈ I, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro I _
      rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_right (hγ I) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
    _ = C * ∑ I ∈ S.powersetCard q, ∏ i ∈ I, ‖v i‖ := (Finset.mul_sum ..).symm
    _ ≤ C * (Real.exp 1 * (1 + ∑ i ∈ S, ‖v i‖) ^ q) :=
      mul_le_mul_of_nonneg_left (powersetCard_product_sum_le S (fun i => ‖v i‖)
        (fun i => norm_nonneg _) q) hC
    _ = _ := by ring

theorem norm_marked_powersetCard_product_sum_le {ι : Type*} (S A : Finset ι)
    (v : ι → ℂ) (γ : Finset ι → ℂ) (q : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hγ : ∀ I, ‖γ I‖ ≤ C) :
    ‖∑ I ∈ (S.powersetCard q).filter (fun I => ¬Disjoint I A), γ I * ∏ i ∈ I, v i‖ ≤
      C * (∑ i ∈ S.filter (fun i => i ∈ A), ‖v i‖) * Real.exp 1 *
        (1 + ∑ i ∈ S, ‖v i‖) ^ q := by
  calc
    _ ≤ ∑ I ∈ (S.powersetCard q).filter (fun I => ¬Disjoint I A),
        ‖γ I * ∏ i ∈ I, v i‖ := norm_sum_le _ _
    _ ≤ ∑ I ∈ (S.powersetCard q).filter (fun I => ¬Disjoint I A),
        C * ∏ i ∈ I, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro I _
      rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_right (hγ I) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
    _ = C * ∑ I ∈ (S.powersetCard q).filter (fun I => ¬Disjoint I A), ∏ i ∈ I, ‖v i‖ :=
      (Finset.mul_sum ..).symm
    _ ≤ C * ((∑ i ∈ S.filter (fun i => i ∈ A), ‖v i‖) * Real.exp 1 *
        (1 + ∑ i ∈ S, ‖v i‖) ^ q) :=
      mul_le_mul_of_nonneg_left (marked_powersetCard_product_sum_le S A (fun i => ‖v i‖)
        (fun i => norm_nonneg _) q) hC
    _ = _ := by ring

end ModifiedCartan
#print axioms ModifiedCartan.powersetCard_product_difference_le_exp_one
#print axioms ModifiedCartan.norm_marked_powersetCard_product_sum_le
