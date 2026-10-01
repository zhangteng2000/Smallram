import ModifiedCartan.PolynomialAlternantSeparation
import ModifiedCartan.SchubertCoordinates

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem polynomialAlternant_reverse_partition_coeff {n : ℕ}
    (p : Fin (n + 1) → Polynomial ℂ) (μ : YoungDiagram) (hμ : PartitionFits n μ) :
    MvPolynomial.coeff (finiteExponent (partitionAlternantExponent (n + 1) μ))
      (polynomialAlternant (fun j => p j.rev)) =
        multiDegreeInverseFactorial (finiteExponent (partitionAlternantExponent (n + 1) μ)) *
          (partitionPolynomialMinor μ p).eval 0 := by
  have h := polynomialAlternant_translate_partition_coeff (fun j => p j.rev) μ hμ 0
  simpa only [mvPolynomialTranslate_zero, Fin.rev_rev] using h

theorem partitionMinor_proportional_of_normalized_eq {n : ℕ}
    (τ : YoungDiagram) (hτ : PartitionFits n τ) (p q : Fin (n + 1) → Polynomial ℂ)
    (hp : (partitionPolynomialMinor τ p).eval 0 ≠ 0)
    (hq : (partitionPolynomialMinor τ q).eval 0 ≠ 0)
    (he : ∀ μ, normalizedPartitionMinor τ p μ 0 = normalizedPartitionMinor τ q μ 0)
    (μ : YoungDiagram) :
    (partitionPolynomialMinor μ p).eval 0 =
      ((partitionPolynomialMinor τ p).eval 0 / (partitionPolynomialMinor τ q).eval 0) *
        (partitionPolynomialMinor μ q).eval 0 := by
  have hf : ((partitionSize τ).factorial : ℂ) / (standardSkewTableauCount τ ⊥ : ℂ) ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero (partitionSize τ)
    · exact_mod_cast (standardSkewTableauCount_pos bot_le hτ).ne'
  have hr : (partitionPolynomialMinor μ p).eval 0 / (partitionPolynomialMinor τ p).eval 0 =
      (partitionPolynomialMinor μ q).eval 0 / (partitionPolynomialMinor τ q).eval 0 := by
    apply mul_left_cancel₀ hf
    simpa only [normalizedPartitionMinor, mul_div_assoc] using he μ
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hq).mpr
  exact ((div_eq_div_iff hp hq).mp hr).trans (mul_comm _ _)

/-- The exact normalized Plucker coordinates at zero separate actual polynomial
    subspaces in the stated Schubert cell. No embedding theorem is assumed.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialSchubertSpace_eq_of_coordinates {n D E : ℕ} {τ : YoungDiagram}
    {V W : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n D τ) (hW : W ∈ polynomialSchubertCell n E τ)
    (he : ∀ μ, normalizedSchubertCoordinate hV μ 0 = normalizedSchubertCoordinate hW μ 0) :
    V = W := by
  let F := schubertFrame hV
  let G := schubertFrame hW
  have hp := partitionPolynomialMinor_top_eval_ne_zero hV.1 F.polynomials
    F.polynomials_ne_zero F.degree_eq 0
  have hq := partitionPolynomialMinor_top_eval_ne_zero hW.1 G.polynomials
    G.polynomials_ne_zero G.degree_eq 0
  let c := (partitionPolynomialMinor τ F.polynomials).eval 0 /
    (partitionPolynomialMinor τ G.polynomials).eval 0
  have hc : c ≠ 0 := div_ne_zero hp hq
  have hm (μ : YoungDiagram) : (partitionPolynomialMinor μ F.polynomials).eval 0 =
      c * (partitionPolynomialMinor μ G.polynomials).eval 0 :=
    partitionMinor_proportional_of_normalized_eq τ hV.1 F.polynomials G.polynomials hp hq he μ
  have ha : polynomialAlternant (fun j => F.polynomials j.rev) =
      MvPolynomial.C c * polynomialAlternant (fun j => G.polynomials j.rev) := by
    apply alternatingPolynomial_ext (polynomialAlternant_hasAlternatingCoefficients _)
      ((polynomialAlternant_hasAlternatingCoefficients _).C_mul c)
    intro μ hμ
    have hf := (partitionFits_iff_height_le μ).mpr hμ
    rw [polynomialAlternant_reverse_partition_coeff F.polynomials μ hf,
      MvPolynomial.coeff_C_mul, polynomialAlternant_reverse_partition_coeff G.polynomials μ hf,
      hm]
    ring
  apply polynomialBasis_subspace_eq_of_alternant_eq V W
    (F.basis.reindex (Fin.revPerm : Equiv.Perm (Fin (n + 1))))
    (G.basis.reindex (Fin.revPerm : Equiv.Perm (Fin (n + 1)))) c hc
  have hrF (j : Fin (n + 1)) :
      ((F.basis.reindex (Fin.revPerm : Equiv.Perm (Fin (n + 1)))) j).val = F.polynomials j.rev := by
    rw [Module.Basis.reindex_apply]
    rfl
  have hrG (j : Fin (n + 1)) :
      ((G.basis.reindex (Fin.revPerm : Equiv.Perm (Fin (n + 1)))) j).val = G.polynomials j.rev := by
    rw [Module.Basis.reindex_apply]
    rfl
  simpa only [hrF, hrG] using ha

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialSchubertSpace_eq_of_coordinates