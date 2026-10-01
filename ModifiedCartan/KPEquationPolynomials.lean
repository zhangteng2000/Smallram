import ModifiedCartan.FiniteKPJointEquation
import ModifiedCartan.StandardPolytabloidBasis

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

theorem linearMap_pi_eq_sum_single {ι V W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (g : (ι → V) →ₗ[ℂ] W) (v : ι → V) :
    g v = ∑ i, g ((LinearMap.single ℂ (fun _ : ι => V) i) (v i)) := by
  have hv : v = ∑ i, (LinearMap.single ℂ (fun _ : ι => V) i) (v i) :=
    (LinearMap.sum_single_apply (fun _ : ι => V) v).symm
  calc
    g v = g (∑ i, (LinearMap.single ℂ (fun _ : ι => V) i) (v i)) := congrArg g hv
    _ = _ := map_sum _ _ _

theorem kpBeta_linearFunctional_action {A : Type*} [Fintype A]
    (τ μ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (L : YoungSpechtModule τ →ₗ[ℂ] ℂ) (v : YoungSpechtModule τ) :
    L ((spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ z 0) v) =
      ∑ I : Finset A, kpWeight z 0 I *
        L ((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ I) v) := by
  simp only [kpBeta_eq_sum_all_subsets, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

def kpEquationEntryFunctional (τ : YoungDiagram)
    (g : (Subpartition τ → YoungSpechtModule τ) →ₗ[ℂ] YoungSpechtModule τ)
    (i : StandardYoungTableau τ) (μ : Subpartition τ) : YoungSpechtModule τ →ₗ[ℂ] ℂ :=
  ((youngStandardPolytabloidBasis τ).coord i).comp
    (g.comp (LinearMap.single ℂ (fun _ : Subpartition τ => YoungSpechtModule τ) μ))

theorem finiteKPJointEquation_matrix_entry {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (z : A → ℂ) (χ : YoungDiagram → ℂ)
    (g : (Subpartition τ → YoungSpechtModule τ) →ₗ[ℂ] YoungSpechtModule τ)
    (i j : StandardYoungTableau τ) :
    LinearMap.toMatrix (youngStandardPolytabloidBasis τ) (youngStandardPolytabloidBasis τ)
      (g.comp (finiteKPJointEquation τ hτ z χ)) i j =
      ∑ μ : Subpartition τ,
        ((∑ I : Finset A, kpWeight z 0 I * kpEquationEntryFunctional τ g i μ
          ((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ.val I)
            (youngStandardPolytabloidBasis τ j))) -
          χ μ.val * kpEquationEntryFunctional τ g i μ (youngStandardPolytabloidBasis τ j)) := by
  rw [LinearMap.toMatrix_apply]
  change (((youngStandardPolytabloidBasis τ).coord i).comp g)
    (finiteKPJointEquation τ hτ z χ (youngStandardPolytabloidBasis τ j)) = _
  rw [linearMap_pi_eq_sum_single]
  apply Finset.sum_congr rfl
  intro μ hμ
  change kpEquationEntryFunctional τ g i μ
    ((spechtRepresentationOn τ hτ).asAlgebraHom (kpBeta μ.val z 0)
      (youngStandardPolytabloidBasis τ j) - χ μ.val • (youngStandardPolytabloidBasis τ j)) = _
  rw [map_sub, map_smul, kpBeta_linearFunctional_action, smul_eq_mul]

def kpZeroWeightPolynomial {A R : Type*} [Fintype A] [CommRing R] (I : Finset A) :
    MvPolynomial A R := ∏ i ∈ Finset.univ \ I, MvPolynomial.X i

theorem kpZeroWeightPolynomial_eval₂ {A B : Type*} [Fintype A]
    (x : B → ℂ) (z : A → ℂ) (I : Finset A) :
    MvPolynomial.eval₂ (MvPolynomial.eval x) z
      (kpZeroWeightPolynomial (R := MvPolynomial B ℂ) I) = kpWeight z 0 I := by
  simp only [kpZeroWeightPolynomial, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X,
    kpWeight, zero_add]

def kpEquationEntryPolynomial {n : ℕ} {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (g : (Subpartition τ → YoungSpechtModule τ) →ₗ[ℂ] YoungSpechtModule τ)
    (i j : StandardYoungTableau τ) : MvPolynomial A (MvPolynomial (SchubertChartSlot n τ) ℂ) :=
  ∑ μ : Subpartition τ,
    ((∑ I : Finset A, kpZeroWeightPolynomial I * MvPolynomial.C (MvPolynomial.C
      (kpEquationEntryFunctional τ g i μ
        ((spechtRepresentationOn τ hτ).asAlgebraHom (kpAlpha μ.val I)
          (youngStandardPolytabloidBasis τ j))))) -
      MvPolynomial.C (schubertCoordinatePolynomial τ μ.val) * MvPolynomial.C (MvPolynomial.C
        (kpEquationEntryFunctional τ g i μ (youngStandardPolytabloidBasis τ j))))

theorem kpEquationEntryPolynomial_eval₂ {n : ℕ} {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (g : (Subpartition τ → YoungSpechtModule τ) →ₗ[ℂ] YoungSpechtModule τ)
    (x : SchubertChartSlot n τ → ℂ) (z : A → ℂ) (i j : StandardYoungTableau τ) :
    MvPolynomial.eval₂ (MvPolynomial.eval x) z (kpEquationEntryPolynomial τ hτ g i j) =
      LinearMap.toMatrix (youngStandardPolytabloidBasis τ) (youngStandardPolytabloidBasis τ)
        (g.comp (finiteKPJointEquation τ hτ z
          (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial τ μ)))) i j := by
  rw [finiteKPJointEquation_matrix_entry]
  change (MvPolynomial.eval₂Hom (MvPolynomial.eval x) z) (kpEquationEntryPolynomial τ hτ g i j) = _
  simp only [kpEquationEntryPolynomial, map_sum, map_sub, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C, MvPolynomial.coe_eval₂Hom,
    kpZeroWeightPolynomial_eval₂]

/-- The actual square-composite determinant is a polynomial in the roots and
    Schubert chart coordinates. Auxiliary to manuscript `lem:KP-correspondence`. -/
def kpEquationDeterminantPolynomial {n : ℕ} {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (g : (Subpartition τ → YoungSpechtModule τ) →ₗ[ℂ] YoungSpechtModule τ) :
    MvPolynomial A (MvPolynomial (SchubertChartSlot n τ) ℂ) :=
  Matrix.det (fun i j : StandardYoungTableau τ => kpEquationEntryPolynomial τ hτ g i j)

theorem kpEquationDeterminantPolynomial_eval₂ {n : ℕ} {A : Type*} [Fintype A]
    (τ : YoungDiagram) (hτ : Fintype.card A = partitionSize τ)
    (g : (Subpartition τ → YoungSpechtModule τ) →ₗ[ℂ] YoungSpechtModule τ)
    (x : SchubertChartSlot n τ → ℂ) (z : A → ℂ) :
    MvPolynomial.eval₂ (MvPolynomial.eval x) z (kpEquationDeterminantPolynomial τ hτ g) =
      LinearMap.det (g.comp (finiteKPJointEquation τ hτ z
        (fun μ => MvPolynomial.eval x (schubertCoordinatePolynomial τ μ)))) := by
  change (MvPolynomial.eval₂Hom (MvPolynomial.eval x) z)
    (Matrix.det (fun i j : StandardYoungTableau τ => kpEquationEntryPolynomial τ hτ g i j)) = _
  erw [RingHom.map_det]
  rw [← LinearMap.det_toMatrix (youngStandardPolytabloidBasis τ)]
  congr 1
  funext i j
  exact kpEquationEntryPolynomial_eval₂ τ hτ g x z i j

end
end ModifiedCartan

#print axioms ModifiedCartan.kpEquationDeterminantPolynomial_eval₂
