import ModifiedCartan.FiniteFrobeniusCauchy
import ModifiedCartan.CauchyKernelCoefficients

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def separateAlphabetPolynomial (A B R : Type*) [CommSemiring R] :
    MvPolynomial (A ⊕ B) R →+* MvPolynomial B (MvPolynomial A R) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (Sum.elim (fun a => MvPolynomial.C (MvPolynomial.X a)) MvPolynomial.X)

theorem separateAlphabetPolynomial_rename_inl {A B R : Type*} [CommSemiring R]
    (F : MvPolynomial A R) :
    separateAlphabetPolynomial A B R (MvPolynomial.rename Sum.inl F) = MvPolynomial.C F := by
  have h : (separateAlphabetPolynomial A B R).comp
      (MvPolynomial.rename (R := R) (τ := A ⊕ B) Sum.inl).toRingHom = MvPolynomial.C := by
    ext r a <;> simp [separateAlphabetPolynomial]
  exact DFunLike.congr_fun h F

theorem separateAlphabetPolynomial_rename_inr {A B R : Type*} [CommSemiring R]
    (F : MvPolynomial B R) :
    separateAlphabetPolynomial A B R (MvPolynomial.rename Sum.inr F) =
      MvPolynomial.map MvPolynomial.C F := by
  have h : (separateAlphabetPolynomial A B R).comp
      (MvPolynomial.rename (R := R) (τ := A ⊕ B) Sum.inr).toRingHom =
        MvPolynomial.map MvPolynomial.C := by
    ext r b <;> simp [separateAlphabetPolynomial]
  exact DFunLike.congr_fun h F

/-- The proved Specht Cauchy identity with one alphabet placed in the
    coefficient ring. Auxiliary to paper `lem:KP-correspondence`. -/
theorem finiteFrobeniusPolynomial_cauchy_separated {A B : Type*} [Fintype A] [Fintype B]
    (n : ℕ) :
    (∑ μ : SizedYoungDiagram n,
      MvPolynomial.C (finiteFrobeniusPolynomial A μ.val) *
        MvPolynomial.map MvPolynomial.C (finiteFrobeniusPolynomial B μ.val)) =
      finiteCauchyCoefficientPolynomial (B := B)
        (fun a : A => (MvPolynomial.X a : MvPolynomial A ℂ)) n := by
  have h := congrArg (separateAlphabetPolynomial A B ℂ)
    (finiteFrobeniusPolynomial_cauchy (A := Fin n) (B := A) (C := B))
  rw [Fintype.card_fin] at h
  simp only [Fintype.card_fin, map_sum, map_mul,
    separateAlphabetPolynomial_rename_inl, separateAlphabetPolynomial_rename_inr] at h
  simpa only [
    map_multiset_prod, Multiset.map_map, Function.comp_def,
    map_mul, separateAlphabetPolynomial, MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr,
    finiteCauchyCoefficientPolynomial] using h

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteFrobeniusPolynomial_cauchy_separated
