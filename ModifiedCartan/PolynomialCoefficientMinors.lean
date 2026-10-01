import ModifiedCartan.PartitionMinorDerivative
import FewInflection.PolynomialJets

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- The derivative minor at zero, expressed over an arbitrary commutative
    coefficient ring. Auxiliary to manuscript `lem:KP-correspondence`. -/
def polynomialCoefficientMinor {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (orders : ι → ℕ) (p : ι → Polynomial R) : R :=
  (Matrix.of fun i j => ((orders i).factorial : R) * (p j).coeff (orders i)).det

theorem polynomialCoefficientMinor_map {R S ι : Type*} [CommRing R] [CommRing S]
    [Fintype ι] [DecidableEq ι] (f : R →+* S) (orders : ι → ℕ)
    (p : ι → Polynomial R) :
    f (polynomialCoefficientMinor orders p) =
      polynomialCoefficientMinor orders (fun j => (p j).map f) := by
  unfold polynomialCoefficientMinor
  rw [f.map_det]
  apply congrArg Matrix.det
  funext i j
  change f (((orders i).factorial : R) * (p j).coeff (orders i)) =
    ((orders i).factorial : S) * ((p j).map f).coeff (orders i)
  rw [map_mul, map_natCast, Polynomial.coeff_map]

theorem polynomialCoefficientMinor_smul {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (orders : ι → ℕ) (p : ι → Polynomial R) (s : R) :
    polynomialCoefficientMinor orders (fun j => s • p j) =
      s ^ Fintype.card ι * polynomialCoefficientMinor orders p := by
  have he : (Matrix.of fun i j => ((orders i).factorial : R) *
      (s • p j).coeff (orders i)) =
      s • (Matrix.of fun i j => ((orders i).factorial : R) *
        (p j).coeff (orders i)) := by
    funext i j
    change ((orders i).factorial : R) * (s • p j).coeff (orders i) =
      s * (((orders i).factorial : R) * (p j).coeff (orders i))
    rw [Polynomial.coeff_smul, smul_eq_mul]
    ring
  unfold polynomialCoefficientMinor
  rw [he, Matrix.det_smul]

theorem polynomialCoefficientMinor_eq_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (orders : ι → ℕ) (p : ι → Polynomial ℂ) :
    polynomialCoefficientMinor orders p = (polynomialDerivativeMinor orders p).eval 0 := by
  rw [polynomialDerivativeMinor_eval]
  unfold polynomialCoefficientMinor
  apply congrArg Matrix.det
  funext i j
  change ((orders i).factorial : ℂ) * (p j).coeff (orders i) =
    (Polynomial.derivative^[orders i] (p j)).eval 0
  rw [← FewInflection.iteratedDeriv_polynomial_eval,
    FewInflection.iteratedDeriv_polynomial_eval_zero]

/-- Arbitrary-partition minors, with the manuscript's zero convention for
    partitions having too many rows. -/
def partitionCoefficientMinor {R : Type*} [CommRing R] {n : ℕ}
    (μ : YoungDiagram) (p : Fin (n + 1) → Polynomial R) : R :=
  if PartitionFits n μ then polynomialCoefficientMinor (partitionMinorOrders n μ) p else 0

theorem partitionCoefficientMinor_map {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} (f : R →+* S) (μ : YoungDiagram) (p : Fin (n + 1) → Polynomial R) :
    f (partitionCoefficientMinor μ p) =
      partitionCoefficientMinor μ (fun j => (p j).map f) := by
  by_cases h : PartitionFits n μ
  · simp only [partitionCoefficientMinor, h, ite_true, polynomialCoefficientMinor_map]
  · simp only [partitionCoefficientMinor, h, ite_false, map_zero]

theorem partitionCoefficientMinor_smul {R : Type*} [CommRing R] {n : ℕ}
    (μ : YoungDiagram) (p : Fin (n + 1) → Polynomial R) (s : R) :
    partitionCoefficientMinor μ (fun j => s • p j) =
      s ^ (n + 1) * partitionCoefficientMinor μ p := by
  by_cases h : PartitionFits n μ
  · simp only [partitionCoefficientMinor, h, ite_true, polynomialCoefficientMinor_smul,
      Fintype.card_fin]
  · simp only [partitionCoefficientMinor, h, ite_false, mul_zero]

theorem partitionCoefficientMinor_eq_eval {n : ℕ}
    (μ : YoungDiagram) (p : Fin (n + 1) → Polynomial ℂ) :
    partitionCoefficientMinor μ p = (partitionPolynomialMinor μ p).eval 0 := by
  by_cases h : PartitionFits n μ
  · simp only [partitionCoefficientMinor, partitionPolynomialMinor, h, ite_true,
      polynomialCoefficientMinor_eq_eval]
  · simp only [partitionCoefficientMinor, partitionPolynomialMinor, h, ite_false,
      Polynomial.eval_zero]

end
end ModifiedCartan

#print axioms ModifiedCartan.partitionCoefficientMinor_map
#print axioms ModifiedCartan.partitionCoefficientMinor_smul
#print axioms ModifiedCartan.partitionCoefficientMinor_eq_eval
