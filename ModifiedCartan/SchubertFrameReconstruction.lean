import ModifiedCartan.PolynomialJetDegreeProfile
import ModifiedCartan.PolynomialJetMatrixGauge
import ModifiedCartan.SchubertCoordinates

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem normalizedPartitionMinor_matrixGauge {n : ℕ} (τ μ : YoungDiagram)
    (p : Fin (n + 1) → Polynomial ℂ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hB : B.det ≠ 0) (a : ℂ) :
    normalizedPartitionMinor τ (polynomialMatrixGauge p B) μ a =
      normalizedPartitionMinor τ p μ a := by
  rw [normalizedPartitionMinor, partitionPolynomialMinor_matrixGauge,
    partitionPolynomialMinor_matrixGauge]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [← mul_assoc, mul_div_mul_right _ _ hB]
  rfl

/-- A nonzero top coordinate and the exact vanishing support produce an actual
    Schubert frame. The degree profile is proved by finite jet elimination.
    Auxiliary to manuscript `lem:KP-correspondence`. -/
theorem polynomialSchubertFrame_exists_of_minor_support {n : ℕ}
    (τ : YoungDiagram) (hτ : PartitionFits n τ) (p : Fin (n + 1) → Polynomial ℂ)
    (ht : (partitionPolynomialMinor τ p).eval 0 ≠ 0)
    (hs : ∀ μ : YoungDiagram, ¬ μ ≤ τ → (partitionPolynomialMinor μ p).eval 0 = 0) :
    ∃ (V : Submodule ℂ (Polynomial ℂ)) (F : PolynomialSchubertFrame n τ V),
      ∀ μ a, normalizedPartitionMinor τ F.polynomials μ a =
        normalizedPartitionMinor τ p μ a := by
  have hd : Matrix.det (fun i j : Fin (n + 1) =>
      (Polynomial.derivative^[partitionMinorOrders n τ i] (p j)).eval 0) ≠ 0 := by
    rw [partitionPolynomialMinor_of_fits hτ, polynomialDerivativeMinor_eval] at ht
    exact ht
  obtain ⟨B, hB, hj⟩ := polynomialMatrixGauge_exists_identity_jets
    (partitionMinorOrders n τ) p 0 hd
  let q := polynomialMatrixGauge p B
  have hq : ∀ μ : YoungDiagram, ¬ μ ≤ τ → (partitionPolynomialMinor μ q).eval 0 = 0 := by
    intro μ hμ
    rw [partitionPolynomialMinor_matrixGauge, Polynomial.eval_mul, hs μ hμ, zero_mul]
  have hlin : LinearIndependent ℂ q :=
    polynomialTuple_linearIndependent_of_identity_jets _ q 0 hj
  let V := Submodule.span ℂ (Set.range q)
  let b : Module.Basis (Fin (n + 1)) ℂ V := Module.Basis.span hlin
  have hb (j : Fin (n + 1)) : (b j).val = q j := Module.Basis.coe_span_apply hlin j
  let F : PolynomialSchubertFrame n τ V :=
    { basis := b
      degree_eq := fun j => by
        rw [hb]
        exact polynomial_natDegree_eq_of_identity_jets_support τ q hj hq j }
  refine ⟨V, F, ?_⟩
  intro μ a
  have he : F.polynomials = q := funext hb
  rw [he]
  exact normalizedPartitionMinor_matrixGauge τ μ p B hB a

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomialSchubertFrame_exists_of_minor_support