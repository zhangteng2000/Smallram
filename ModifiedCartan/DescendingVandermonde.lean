import ModifiedCartan.VandermondeAlternantMaps

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteVandermondeAlternant_map_product {R : Type*} [CommRing R] {m : ℕ}
    (φ : MvPolynomial (Fin m) ℂ →+* R) :
    φ (finiteVandermondeAlternant m) =
      ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (φ (MvPolynomial.X i) - φ (MvPolynomial.X j)) := by
  erw [finiteVandermondeAlternant, finiteAlternant_eq_det, RingHom.map_det]
  have hm : φ.mapMatrix (fun i j : Fin m =>
      (MvPolynomial.X j : MvPolynomial (Fin m) ℂ) ^ i.rev.val) =
      (Matrix.projVandermonde (fun _ : Fin m => (1 : R))
        (fun i => φ (MvPolynomial.X i))).transpose := by
    ext i j
    change φ ((MvPolynomial.X j) ^ i.rev.val) =
      (1 : R) ^ i.val * (φ (MvPolynomial.X j)) ^ i.rev.val
    simp
  rw [hm, Matrix.det_transpose, Matrix.det_projVandermonde]
  simp

/-- The first-variable factorization of the descending staircase determinant.
    Auxiliary to the finite Bernstein calculation for `lem:KP-correspondence`. -/
theorem finiteVandermondeAlternant_map_succ {R : Type*} [CommRing R] {m : ℕ}
    (φ : MvPolynomial (Fin (m + 1)) ℂ →+* R) :
    φ (finiteVandermondeAlternant (m + 1)) =
      (∏ i : Fin m, (φ (MvPolynomial.X 0) - φ (MvPolynomial.X i.succ))) *
        (φ.comp (MvPolynomial.rename Fin.succ).toRingHom) (finiteVandermondeAlternant m) := by
  rw [finiteVandermondeAlternant_map_product, finiteVandermondeAlternant_map_product]
  simp [Fin.prod_univ_succ, Fin.Ioi_zero_eq_map, Finset.prod_map, Fin.coe_succEmb,
    Fin.prod_Ioi_succ]

end
end ModifiedCartan
