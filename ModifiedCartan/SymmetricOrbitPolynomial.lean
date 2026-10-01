import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Perm

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- A symmetric equation recording all root relabelings of a polynomial
    certificate. Auxiliary to manuscript `lem:KP-correspondence`. -/
def symmetricOrbitPolynomial {A R : Type*} [Fintype A] [CommRing R]
    (p : MvPolynomial A R) (c : R) : MvPolynomial A R :=
  (∏ u : Equiv.Perm A, (MvPolynomial.C c - MvPolynomial.rename u p)) -
    MvPolynomial.C (c ^ Fintype.card (Equiv.Perm A))

theorem symmetricOrbitPolynomial_isSymmetric {A R : Type*} [Fintype A] [CommRing R]
    (p : MvPolynomial A R) (c : R) : (symmetricOrbitPolynomial p c).IsSymmetric := by
  intro v
  simp only [symmetricOrbitPolynomial, map_sub, map_prod, MvPolynomial.rename_C,
    MvPolynomial.rename_rename]
  congr 1
  exact Equiv.prod_comp (Equiv.mulLeft v)
    (fun u : Equiv.Perm A => MvPolynomial.C c - MvPolynomial.rename u p)

theorem symmetricOrbitPolynomial_eval₂ {A R S : Type*} [Fintype A]
    [CommRing R] [CommRing S] (f : R →+* S) (z : A → S) (p : MvPolynomial A R) (c : R) :
    MvPolynomial.eval₂ f z (symmetricOrbitPolynomial p c) =
      (∏ u : Equiv.Perm A, (f c - MvPolynomial.eval₂ f (z ∘ u) p)) -
        (f c) ^ Fintype.card (Equiv.Perm A) := by
  change (MvPolynomial.eval₂Hom f z) (symmetricOrbitPolynomial p c) = _
  simp only [symmetricOrbitPolynomial, map_sub, map_prod, MvPolynomial.eval₂Hom_C,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename, map_pow]

theorem symmetricOrbitPolynomial_eval₂_eq_zero {A R S : Type*} [Fintype A]
    [CommRing R] [CommRing S] (f : R →+* S) (z : A → S) (p : MvPolynomial A R) (c : R)
    (hp : ∀ u : Equiv.Perm A, MvPolynomial.eval₂ f (z ∘ u) p = 0) :
    MvPolynomial.eval₂ f z (symmetricOrbitPolynomial p c) = 0 := by
  rw [symmetricOrbitPolynomial_eval₂]
  simp only [hp, sub_zero, Finset.prod_const, Finset.card_univ, sub_self]

/-- Vanishing of the symmetric orbit equations for all constants forces the
    original certificate to vanish, over an integral domain. -/
theorem eval₂_eq_zero_of_symmetricOrbitPolynomial {A R S : Type*} [Fintype A]
    [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Surjective f)
    (z : A → S) (p : MvPolynomial A R)
    (h : ∀ c : R, MvPolynomial.eval₂ f z (symmetricOrbitPolynomial p c) = 0) :
    MvPolynomial.eval₂ f z p = 0 := by
  obtain ⟨c, hc⟩ := hf (MvPolynomial.eval₂ f z p)
  have he := h c
  rw [symmetricOrbitPolynomial_eval₂] at he
  have hprod : (∏ u : Equiv.Perm A, (f c - MvPolynomial.eval₂ f (z ∘ u) p)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : Equiv.Perm A))
    change f c - MvPolynomial.eval₂ f z p = 0
    exact sub_eq_zero.mpr hc
  rw [hprod, zero_sub, neg_eq_zero] at he
  by_contra hn
  exact (pow_ne_zero _ (hc ▸ hn)) he

end
end ModifiedCartan

#print axioms ModifiedCartan.eval₂_eq_zero_of_symmetricOrbitPolynomial
