import FewInflection.Results

/-!
# Elementary symmetric bounds for universal minor expansions

The representation-theoretic part of the paper supplies coefficients bounded by
`s!` in a finite sum of products of reciprocal root distances.  This file
proves the analytic estimate for that finite sum independently of the source
of the coefficients.  It is therefore a genuine reusable step without
assuming the external representation theorem.
-/

open scoped BigOperators

namespace FewInflection

noncomputable section

def elementarySymmetric {R : Type*} [CommSemiring R] {M : ℕ}
    (x : Fin M → R) (s : ℕ) : R :=
  ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard s, ∏ i ∈ I, x i

@[simp] theorem elementarySymmetric_zero {R : Type*} [CommSemiring R]
    {M : ℕ} (x : Fin M → R) :
    elementarySymmetric x 0 = 1 := by
  simp [elementarySymmetric]

@[simp] theorem elementarySymmetric_of_gt_card {R : Type*} [CommSemiring R]
    {M s : ℕ} (x : Fin M → R)
    (hs : M < s) : elementarySymmetric x s = 0 := by
  have hP : (Finset.univ : Finset (Fin M)).powersetCard s = ∅ := by
    apply Finset.powersetCard_eq_empty.2
    simpa using hs
  simp [elementarySymmetric, hP]

theorem coeff_finset_prod_X_add_C_eq_elementarySymmetric
    {R : Type*} [CommSemiring R] {M s : ℕ} (a : Fin M → R)
    (hs : s ≤ M) :
    (∏ i : Fin M, (Polynomial.X + Polynomial.C (a i))).coeff (M - s) =
      elementarySymmetric a s := by
  rw [Finset.prod_X_add_C_coeff (s := (Finset.univ : Finset (Fin M))) a]
  · simp [elementarySymmetric]
    rw [Nat.sub_sub_self hs]
  · simpa using Nat.sub_le _ _

/-- The finite generating identity used to sum the initial-basis Taylor
majorant. Subsets are grouped by cardinality before the scalar power is
factored out. -/
theorem elementarySymmetric_generating_identity
    {M : ℕ} (x : Fin M → ℝ) (t : ℝ) :
    ∑ s ∈ Finset.range (M + 1), elementarySymmetric x s * t ^ s =
      ∏ i : Fin M, (1 + t * x i) := by
  rw [Finset.prod_one_add, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro s hs
  rw [elementarySymmetric, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  have hcard := (Finset.mem_powersetCard.mp hI).2
  rw [show (∏ i ∈ I, (t * x i)) =
      t ^ I.card * (∏ i ∈ I, x i) by
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_const]]
  rw [hcard]
  ring

theorem norm_sum_coeff_mul_inv_product_le_factorial_mul_elementarySymmetric
    {M s : ℕ} (coeff : Finset (Fin M) → ℂ) (a : Fin M → ℂ)
    (hcoeff : ∀ I ∈ (Finset.univ : Finset (Fin M)).powersetCard s,
      ‖coeff I‖ ≤ (Nat.factorial s : ℝ)) :
    ‖∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard s,
        coeff I * ∏ i ∈ I, (a i)⁻¹‖ ≤
      (Nat.factorial s : ℝ) *
        elementarySymmetric (fun i => ‖(a i)⁻¹‖) s := by
  let P : Finset (Finset (Fin M)) :=
    (Finset.univ : Finset (Fin M)).powersetCard s
  calc
    ‖∑ I ∈ P, coeff I * ∏ i ∈ I, (a i)⁻¹‖ ≤
        ∑ I ∈ P, ‖coeff I * ∏ i ∈ I, (a i)⁻¹‖ := by
      exact norm_sum_le P _
    _ = ∑ I ∈ P,
        ‖coeff I‖ * ∏ i ∈ I, ‖(a i)⁻¹‖ := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [norm_mul, norm_prod]
    _ ≤ ∑ I ∈ P,
        (Nat.factorial s : ℝ) * ∏ i ∈ I, ‖(a i)⁻¹‖ := by
      apply Finset.sum_le_sum
      intro I hI
      exact mul_le_mul_of_nonneg_right
        (hcoeff I hI) (Finset.prod_nonneg fun i hi => norm_nonneg _)
    _ = (Nat.factorial s : ℝ) *
        elementarySymmetric (fun i => ‖(a i)⁻¹‖) s := by
      simp only [P, elementarySymmetric]
      rw [Finset.mul_sum]

/-! Complementing a subset of a finite index set turns an elementary
 symmetric sum into the reciprocal-root sum that occurs in logarithmic
 derivative estimates.  The nonvanishing hypothesis is kept explicit so the
 division is a genuine algebraic identity. -/
theorem elementarySymmetric_complement_div_prod
    {M s : ℕ} (d : Fin M → ℂ) (hd : ∀ i, d i ≠ 0) (hs : s ≤ M) :
    elementarySymmetric d (M - s) / (∏ i : Fin M, d i) =
      elementarySymmetric (fun i => (d i)⁻¹) s := by
  classical
  let U : Finset (Fin M) := Finset.univ
  let P : Finset (Finset (Fin M)) := U.powersetCard (M - s)
  let Q : Finset (Finset (Fin M)) := U.powersetCard s
  have hPmem : ∀ I ∈ P, Iᶜ ∈ Q := by
    intro I hI
    have hI' := Finset.mem_powersetCard.mp hI
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      exact Finset.mem_univ _
    · rw [Finset.card_compl, hI'.2]
      simp only [Fintype.card_fin]
      exact Nat.sub_sub_self hs
  have hQmem : ∀ J ∈ Q, Jᶜ ∈ P := by
    intro J hJ
    have hJ' := Finset.mem_powersetCard.mp hJ
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      exact Finset.mem_univ _
    · rw [Finset.card_compl, hJ'.2]
      simp only [Fintype.card_fin]
  have hcomp_inj : ∀ I₁ ∈ P, ∀ I₂ ∈ P, I₁ᶜ = I₂ᶜ → I₁ = I₂ := by
    intro I₁ hI₁ I₂ hI₂ hab
    apply Finset.ext
    intro x
    have hx := congrArg (fun T : Finset (Fin M) => x ∈ T) hab
    have hxiff : x ∈ I₁ᶜ ↔ x ∈ I₂ᶜ := iff_of_eq hx
    have hn : x ∉ I₁ ↔ x ∉ I₂ := by
      simpa only [Finset.mem_compl] using hxiff
    simpa only [not_not] using (not_congr hn)
  have hcomp_surj : ∀ J ∈ Q, ∃ I, ∃ hI : I ∈ P, Iᶜ = J := by
    intro J hJ
    refine ⟨Jᶜ, hQmem J hJ, ?_⟩
    simp
  have hterm : ∀ I ∈ P,
      (∏ i ∈ I, d i) / (∏ i : Fin M, d i) =
        ∏ i ∈ Iᶜ, (d i)⁻¹ := by
    intro I hI
    have hprod : (∏ i : Fin M, d i) =
        (∏ i ∈ I, d i) * (∏ i ∈ Iᶜ, d i) := by
      rw [← Finset.prod_union]
      · simp
      · apply Finset.disjoint_left.2
        intro x hxI hxC
        exact (Finset.mem_compl.mp hxC) hxI
    have hIprod : (∏ i ∈ I, d i) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      exact hd i
    rw [Finset.prod_inv_distrib, hprod]
    field_simp [hIprod]
  dsimp [elementarySymmetric, P, Q, U]
  rw [Finset.sum_div]
  apply Finset.sum_bij (fun I _ => Iᶜ)
  · intro I hI
    exact hPmem I hI
  · intro I₁ hI₁ I₂ hI₂ hab
    exact hcomp_inj I₁ hI₁ I₂ hI₂ hab
  · intro J hJ
    exact hcomp_surj J hJ
  · intro I hI
    simpa [Finset.prod_inv_distrib] using hterm I hI

end

end FewInflection

