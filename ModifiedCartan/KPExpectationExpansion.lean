import ModifiedCartan.KPAlphaExpectation

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

theorem complement_product_weight_div {A : Type*} [Fintype A] [DecidableEq A]
    (d : A → ℂ) (hd : ∀ i, d i ≠ 0) (I : Finset A) (c : ℂ) :
    ((∏ i ∈ Finset.univ \ I, d i) * c) / (∏ i, d i) = c / (∏ i ∈ I, d i) := by
  have hI : (∏ i ∈ I, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  have hC : (∏ i ∈ Finset.univ \ I, d i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  rw [← Finset.prod_sdiff (Finset.subset_univ I) (f := d)]
  field_simp

theorem kpBeta_expectation_eq_sum {A W : Type*} [Fintype A] [DecidableEq A]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Representation ℂ (Equiv.Perm A) W) (μ : YoungDiagram)
    (z : A → ℂ) (a : ℂ) (v : W) :
    inner ℂ v (ρ.asAlgebraHom (kpBeta μ z a) v) =
      ∑ I ∈ (Finset.univ : Finset A).powersetCard (partitionSize μ),
        (∏ i ∈ Finset.univ \ I, (a + z i)) * inner ℂ v (ρ.asAlgebraHom (kpAlpha μ I) v) := by
  simp only [kpBeta, map_sum, LinearMap.sum_apply, inner_sum, map_smul,
    LinearMap.smul_apply, inner_smul_right]

/-- The group-algebra identity giving the reciprocal-root products in
    manuscript `eq:universal-minors`; no distinctness of roots is used. -/
theorem kpBeta_expectation_div_product {A W : Type*} [Fintype A] [DecidableEq A]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Representation ℂ (Equiv.Perm A) W) (μ : YoungDiagram)
    (z : A → ℂ) (a : ℂ) (hroot : ∀ i, a + z i ≠ 0) (v : W) :
    inner ℂ v (ρ.asAlgebraHom (kpBeta μ z a) v) / (∏ i, (a + z i)) =
      ∑ I ∈ (Finset.univ : Finset A).powersetCard (partitionSize μ),
        inner ℂ v (ρ.asAlgebraHom (kpAlpha μ I) v) / (∏ i ∈ I, (a + z i)) := by
  rw [kpBeta_expectation_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro I _
  exact complement_product_weight_div (fun i => a + z i) hroot I _

end
end ModifiedCartan

#print axioms ModifiedCartan.kpBeta_expectation_div_product