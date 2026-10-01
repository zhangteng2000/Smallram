import ModifiedCartan.SchubertColumnDifferentialEquation
import ModifiedCartan.SchubertDegreeInitialCoefficients
import ModifiedCartan.PolynomialCoefficientMinors
import ModifiedCartan.PolynomialODEAdjugateMap
import ModifiedCartan.InitialPolynomialJetBounds

namespace ModifiedCartan
noncomputable section
open scoped Classical BigOperators

def partitionColumnDifferentialCoefficients {R : Type*} [CommRing R]
    (N : ℕ) (f : YoungDiagram → Polynomial R) (i : Fin (N + 1)) : Polynomial R :=
  Polynomial.C ((-1 : R) ^ (N - i.val)) * f (columnPartition (N - i.val))

/-- Actual normalized coordinate polynomials reconstruct an identity-jet
    Schubert basis by the finite adjugate. Auxiliary to `lem:KP-correspondence`. -/
theorem schubert_columnValues_adjugate_solution {n D L : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (b : Module.Basis (Fin (n + 1)) ℂ V)
    (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval 0 = if i = j then 1 else 0)
    (f : YoungDiagram → Polynomial ℂ)
    (hf : ∀ μ a, (f μ).eval a = normalizedSchubertCoordinate hV μ a)
    (hL : n + partitionSize τ < L) (j : Fin (n + 1)) :
    polynomialODEAdjugatePolynomial (n + 1) L
      (partitionColumnDifferentialCoefficients (n + 1) f)
      (fun r : Fin L => if r.val = j.val then ((j.val.factorial : ℂ)⁻¹) else 0) =
      (polynomialODEJetMatrix (n + 1) L
        (partitionColumnDifferentialCoefficients (n + 1) f)).det • (b j).val := by
  apply polynomialODE_identityJets_adjugate_solution _ _ hb
  · intro l
    exact (polynomialSchubertCell_natDegree_le hV (b l)).trans_lt hL
  · intro l
    exact schubert_columnValues_differential_identity hV b f hf l

theorem normalizedSchubertCoordinate_eq_bot_mul_of_identityJets {n D : ℕ}
    {τ : YoungDiagram} {V : Submodule ℂ (Polynomial ℂ)}
    (hV : V ∈ polynomialSchubertCell n D τ) (b : Module.Basis (Fin (n + 1)) ℂ V)
    (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval 0 = if i = j then 1 else 0)
    (μ : YoungDiagram) :
    normalizedSchubertCoordinate hV μ 0 =
      normalizedSchubertCoordinate hV ⊥ 0 *
        (partitionPolynomialMinor μ (fun j => (b j).val)).eval 0 := by
  rw [normalizedSchubertCoordinate_eq_basis hV b μ,
    normalizedSchubertCoordinate_eq_basis hV b ⊥]
  simp only [normalizedPartitionMinor, partitionPolynomialMinor_bot,
    identityJet_polynomialWronskian_eval _ 0 hb, mul_one]
  ring

/-- The denominator-cleared coordinate identity underlying the universal
    Bethe-algebra reconstruction. It holds without dividing by a determinant. -/
theorem schubert_columnValues_adjugate_minor {n D L : ℕ} {τ : YoungDiagram}
    {V : Submodule ℂ (Polynomial ℂ)} (hV : V ∈ polynomialSchubertCell n D τ)
    (b : Module.Basis (Fin (n + 1)) ℂ V)
    (hb : ∀ i j : Fin (n + 1),
      (Polynomial.derivative^[i.val] (b j).val).eval 0 = if i = j then 1 else 0)
    (f : YoungDiagram → Polynomial ℂ)
    (hf : ∀ μ a, (f μ).eval a = normalizedSchubertCoordinate hV μ a)
    (hL : n + partitionSize τ < L) (μ : YoungDiagram) :
    (polynomialODEJetMatrix (n + 1) L
      (partitionColumnDifferentialCoefficients (n + 1) f)).det ^ (n + 1) * (f μ).eval 0 =
      (f ⊥).eval 0 * partitionCoefficientMinor μ (fun j : Fin (n + 1) =>
        polynomialODEAdjugatePolynomial (n + 1) L
          (partitionColumnDifferentialCoefficients (n + 1) f)
          (fun r : Fin L => if r.val = j.val then ((j.val.factorial : ℂ)⁻¹) else 0)) := by
  have he := schubert_columnValues_adjugate_solution hV b hb f hf hL
  simp_rw [he]
  rw [partitionCoefficientMinor_smul, partitionCoefficientMinor_eq_eval, hf, hf,
    normalizedSchubertCoordinate_eq_bot_mul_of_identityJets hV b hb μ]
  ring

end
end ModifiedCartan

#print axioms ModifiedCartan.schubert_columnValues_adjugate_solution
#print axioms ModifiedCartan.schubert_columnValues_adjugate_minor
