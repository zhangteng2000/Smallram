import ModifiedCartan.FiniteAlternants
import ModifiedCartan.FiniteCauchyDeterminant
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.Ring.Int.Units

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteVandermondeAlternant_map {R : Type*} [CommRing R] {m : ℕ}
    (φ : MvPolynomial (Fin m) ℂ →+* R) :
    φ (finiteVandermondeAlternant m) =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) : ℤ) : R) *
        finiteVandermondeProduct (fun i => φ (MvPolynomial.X i)) := by
  erw [finiteVandermondeAlternant, finiteAlternant_eq_det, RingHom.map_det]
  have hm : φ.mapMatrix (fun i j : Fin m =>
      (MvPolynomial.X j : MvPolynomial (Fin m) ℂ) ^ i.rev.val) =
      (Matrix.vandermonde (fun i => φ (MvPolynomial.X i))).transpose.submatrix Fin.revPerm id := by
    ext i j
    change φ ((MvPolynomial.X j) ^ i.rev.val) = (φ (MvPolynomial.X j)) ^ (Fin.revPerm i).val
    simp
  rw [hm, Matrix.det_permute, Matrix.det_transpose, Matrix.det_vandermonde]
  rfl

/-- The two reversal signs cancel in the product of two alternants.
    Auxiliary to paper `lem:KP-correspondence`. -/
theorem finiteVandermondeAlternant_map_mul {R : Type*} [CommRing R] {m : ℕ}
    (φ ψ : MvPolynomial (Fin m) ℂ →+* R) :
    φ (finiteVandermondeAlternant m) * ψ (finiteVandermondeAlternant m) =
      finiteVandermondeProduct (fun i => φ (MvPolynomial.X i)) *
        finiteVandermondeProduct (fun i => ψ (MvPolynomial.X i)) := by
  rw [finiteVandermondeAlternant_map, finiteVandermondeAlternant_map]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with hs | hs <;>
    simp [hs]

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteVandermondeAlternant_map_mul
