import ModifiedCartan.PluckerTranslation
import ModifiedCartan.PolynomialODEKernelBound
import Mathlib.Algebra.Polynomial.FieldDivision

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- The empty normalized coordinate is the value of the monic Wronskian.
    This verifies the scalar in `eq:normalized-Plucker-coordinates`. -/
theorem normalizedPartitionMinor_bot_eq_normalize_wronskian {n : ℕ}
    (τ : YoungDiagram) (hτ : PartitionFits n τ) (p : Fin (n + 1) → Polynomial ℂ)
    (hp0 : ∀ j, p j ≠ 0) (hp : ∀ j, (p j).natDegree = partitionMinorOrders n τ j) (a : ℂ) :
    normalizedPartitionMinor τ p ⊥ a =
      (normalize (FewInflection.polynomialWronskian p)).eval a := by
  let W := FewInflection.polynomialWronskian p
  have hdeg : W.natDegree = partitionSize τ :=
    polynomialWronskian_natDegree_eq_partitionSize p hτ hp0 hp
  have ht : (partitionPolynomialMinor τ p).eval 0 ≠ 0 :=
    partitionPolynomialMinor_top_eval_ne_zero hτ p hp0 hp 0
  have hf : (standardSkewTableauCount τ ⊥ : ℂ) ≠ 0 := by
    exact_mod_cast (standardSkewTableauCount_pos bot_le hτ).ne'
  have hfac : ((partitionSize τ).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (partitionSize τ)
  have he := factorial_mul_wronskian_top_coeff p hτ (fun j => (hp j).le)
  have he' : ((partitionSize τ).factorial : ℂ) * W.leadingCoeff =
      (standardSkewTableauCount τ ⊥ : ℂ) * (partitionPolynomialMinor τ p).eval 0 := by
    simpa only [Polynomial.leadingCoeff, hdeg] using he
  have hl : W.leadingCoeff ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he'
    exact mul_ne_zero hf ht he'.symm
  have hc : ((partitionSize τ).factorial : ℂ) /
      (standardSkewTableauCount τ ⊥ : ℂ) / (partitionPolynomialMinor τ p).eval 0 =
        W.leadingCoeff⁻¹ := by
    field_simp
    exact he'
  rw [normalizedPartitionMinor, partitionPolynomialMinor_bot,
    partitionPolynomialMinor_top_eval_eq p hτ (fun j => (hp j).le) a 0]
  change _ = (normalize W).eval a
  rw [normalize_apply, Polynomial.coe_normUnit, CommGroupWithZero.coe_normUnit ℂ hl,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [← hc]
  ring

/-- The monic Wronskian of a Schubert space, using its chosen actual frame. -/
def schubertMonicWronskian {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ) : Polynomial ℂ :=
  normalize (FewInflection.polynomialWronskian (schubertFrame hV).polynomials)

theorem normalizedSchubertCoordinate_bot {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ) (a : ℂ) :
    normalizedSchubertCoordinate hV ⊥ a = (schubertMonicWronskian hV).eval a :=
  normalizedPartitionMinor_bot_eq_normalize_wronskian τ hV.1
    (schubertFrame hV).polynomials (schubertFrame hV).polynomials_ne_zero
    (schubertFrame hV).degree_eq a

theorem schubertMonicWronskian_monic {n D : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ) :
    (schubertMonicWronskian hV).Monic := by
  apply Polynomial.monic_normalize
  apply polynomialWronskian_ne_zero_of_linearIndependent
  exact (schubertFrame hV).basis.linearIndependent.map' V.subtype V.ker_subtype

end
end ModifiedCartan

#print axioms ModifiedCartan.normalizedSchubertCoordinate_bot
#print axioms ModifiedCartan.schubertMonicWronskian_monic