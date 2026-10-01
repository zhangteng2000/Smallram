import ModifiedCartan.FittingFrobeniusOrthogonality

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- KP (2.15), finite alphabet form: the actual Specht character transform
    times the staircase alternant is the partition alternant.
    Auxiliary to the manuscript's `lem:KP-correspondence`. -/
theorem finiteFrobeniusPolynomial_mul_alternant {m : ℕ} (μ : YoungDiagram)
    (hm : μ.colLen 0 ≤ m) :
    finiteVandermondeAlternant m * finiteFrobeniusPolynomial (Fin m) μ =
      finiteAlternant (partitionAlternantExponent m μ) := by
  have hd := partitionAlternantExponent_degree μ hm
  have h := finiteAlternant_frobenius_expansion (partitionSize μ)
    (partitionFiniteDegree m μ + finiteStaircaseDegree m) hd
  change finiteAlternant (partitionAlternantExponent m μ) = finiteVandermondeAlternant m *
    ∑ ν : SizedYoungDiagram (partitionSize μ), finiteFrobeniusPolynomial (Fin m) ν.val *
      MvPolynomial.C (frobeniusAlternantCoefficient m μ ν.val) at h
  have hc (ν : SizedYoungDiagram (partitionSize μ)) :
      frobeniusAlternantCoefficient m μ ν.val =
        if (⟨μ, rfl⟩ : SizedYoungDiagram (partitionSize μ)) = ν then 1 else 0 :=
    frobeniusAlternantCoefficient_identity ⟨μ, rfl⟩ ν hm
  simpa [hc, apply_ite] using h.symm

theorem finiteFrobeniusPolynomial_schur_determinant_rev {m : ℕ} (μ : YoungDiagram)
    (hm : μ.colLen 0 ≤ m) :
    finiteFrobeniusPolynomial (Fin m) μ *
      Matrix.det (fun i j : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) ℂ) ^ j.rev.val) =
        Matrix.det (fun i j : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) ℂ) ^
          (μ.rowLen j.val + j.rev.val)) := by
  have h := finiteFrobeniusPolynomial_mul_alternant μ hm
  rw [finiteVandermondeAlternant, finiteAlternant_eq_det_columns,
    finiteAlternant_eq_det_columns] at h
  simpa only [partitionAlternantExponent, mul_comm] using h

/-- KP (2.15), with the exact determinantal Schur exponents. This proves the
    character/Schur bridge used by manuscript `lem:KP-correspondence`. -/
theorem finiteFrobeniusPolynomial_schur_determinant {m : ℕ} (μ : YoungDiagram)
    (hm : μ.colLen 0 ≤ m) :
    finiteFrobeniusPolynomial (Fin m) μ *
      Matrix.det (fun i j : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) ℂ) ^ (m - 1 - j.val)) =
        Matrix.det (fun i j : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) ℂ) ^
          (μ.rowLen j.val + (m - 1 - j.val))) := by
  simpa only [Fin.val_rev, Nat.sub_sub, Nat.add_comm] using
    finiteFrobeniusPolynomial_schur_determinant_rev μ hm

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteFrobeniusPolynomial_mul_alternant
#print axioms ModifiedCartan.finiteFrobeniusPolynomial_schur_determinant
