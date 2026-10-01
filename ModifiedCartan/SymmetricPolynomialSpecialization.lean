import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Complex.Basic

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- A symmetric polynomial with polynomial coefficients specializes to a
    polynomial in the base variables once the elementary symmetric values
    are prescribed by base polynomials. Auxiliary to `lem:KP-correspondence`. -/
theorem symmetricPolynomial_exists_specialization {A B : Type*} [Fintype A]
    (p : MvPolynomial A (MvPolynomial B ℂ)) (hp : p.IsSymmetric)
    (w : Fin (Fintype.card A) → MvPolynomial B ℂ) :
    ∃ q : MvPolynomial B ℂ, ∀ (x : B → ℂ) (z : A → ℂ),
      (∀ i : Fin (Fintype.card A), MvPolynomial.eval x (w i) =
        MvPolynomial.eval₂ (MvPolynomial.eval x) z
          (MvPolynomial.esymm A (MvPolynomial B ℂ) (i.val + 1))) →
      MvPolynomial.eval x q = MvPolynomial.eval₂ (MvPolynomial.eval x) z p := by
  obtain ⟨q, hq⟩ := MvPolynomial.esymmAlgHom_surjective
    (MvPolynomial B ℂ) (σ := A) (n := Fintype.card A) le_rfl ⟨p, hp⟩
  have he : MvPolynomial.aeval
      (fun i : Fin (Fintype.card A) => MvPolynomial.esymm A (MvPolynomial B ℂ) (i.val + 1)) q = p := by
    have hv := congrArg Subtype.val hq
    rw [MvPolynomial.esymmAlgHom_apply] at hv
    exact hv
  refine ⟨MvPolynomial.aeval w q, ?_⟩
  intro x z hw
  rw [← he]
  clear hq he
  change (MvPolynomial.eval x) (MvPolynomial.aeval w q) =
    (MvPolynomial.eval₂Hom (MvPolynomial.eval x) z) (MvPolynomial.aeval _ q)
  induction q using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.aeval_C]
    change MvPolynomial.eval x c =
      MvPolynomial.eval₂ (MvPolynomial.eval x) z (MvPolynomial.C c)
    rw [MvPolynomial.eval₂_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, hp]
    rw [hw i]
    rfl

/-- Vieta's formula in the `X + z_i` parameter convention, with arbitrary
    polynomial coefficients evaluated at a base point. -/
theorem eval₂_esymm_eq_linearProduct_coeff {M : ℕ} {B : Type*}
    (x : B → ℂ) (z : Fin M → ℂ) (i : Fin M) :
    MvPolynomial.eval₂ (MvPolynomial.eval x) z
      (MvPolynomial.esymm (Fin M) (MvPolynomial B ℂ) (i.val + 1)) =
      (∏ j : Fin M, (Polynomial.X + Polynomial.C (z j))).coeff (M - (i.val + 1)) := by
  rw [Finset.prod_X_add_C_coeff _ z (by simp only [Finset.card_univ, Fintype.card_fin]; omega)]
  simp only [Finset.card_univ, Fintype.card_fin,
    Nat.sub_sub_self (Nat.succ_le_of_lt i.isLt)]
  simp only [MvPolynomial.esymm, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X]

end
end ModifiedCartan

#print axioms ModifiedCartan.symmetricPolynomial_exists_specialization
