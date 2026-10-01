import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Div

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem algebraic_nonzero_relation_constant {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain S] [Algebra R S] {x : S}
    (hx : IsAlgebraic R x) (hne : x ≠ 0) :
    ∃ p : Polynomial R, p.coeff 0 ≠ 0 ∧ Polynomial.aeval x p = 0 := by
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨q, he, hq⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  have hc : q.coeff 0 ≠ 0 := by
    simpa only [map_zero, sub_zero, Polynomial.X_dvd_iff] using hq
  refine ⟨q, hc, ?_⟩
  rw [he, map_mul, map_pow] at hpx
  simp only [Polynomial.aeval_X, map_zero, sub_zero] at hpx
  exact (mul_eq_zero.mp hpx).resolve_left (pow_ne_zero _ hne)

theorem algebraicIndependent_of_surjective_polynomialMap {K ι : Type*}
    [Field K] [Infinite K] (w : ι → MvPolynomial ι K)
    (hw : Function.Surjective (fun x : ι → K => fun i => MvPolynomial.eval x (w i))) :
    AlgebraicIndependent K w := by
  apply algebraicIndependent_iff.mpr
  intro p hp
  apply MvPolynomial.funext
  intro y
  obtain ⟨x, hx⟩ := hw y
  change (fun i => MvPolynomial.eval x (w i)) = y at hx
  have he := MvPolynomial.comp_aeval_apply (MvPolynomial.aeval x) (f := w) p
  rw [hp, map_zero] at he
  change 0 = MvPolynomial.eval (fun i => MvPolynomial.eval x (w i)) p at he
  rw [hx] at he
  simpa only [map_zero] using he.symm

/-- A subset meeting every fibre of a polynomial self-map of affine space
    is Zariski dense. This avoids a fibre-degree assumption in the proposed
    alternative proof of manuscript `lem:KP-correspondence`. -/
theorem polynomial_eq_zero_of_zero_on_every_fibre {K ι : Type*}
    [Field K] [Infinite K] [Finite ι]
    (w : ι → MvPolynomial ι K) (p : MvPolynomial ι K)
    (h : ∀ y : ι → K, ∃ x : ι → K,
      (fun i => MvPolynomial.eval x (w i)) = y ∧ MvPolynomial.eval x p = 0) : p = 0 := by
  have hw : AlgebraicIndependent K w :=
    algebraicIndependent_of_surjective_polynomialMap w (fun y => by
      obtain ⟨x, hx, hp⟩ := h y
      exact ⟨x, hx⟩)
  have hb : IsTranscendenceBasis K w :=
    hw.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simp)
  have halg := hb.isAlgebraic
  by_contra hp
  obtain ⟨q, hq0, hq⟩ := algebraic_nonzero_relation_constant
    (halg.isAlgebraic p) hp
  let r : MvPolynomial ι K := hw.repr (q.coeff 0)
  have hr : r ≠ 0 := by
    intro he
    have he' := congrArg (MvPolynomial.aeval w) he
    rw [show MvPolynomial.aeval w r = (q.coeff 0).val from hw.aeval_repr _, map_zero] at he'
    exact hq0 (Subtype.ext he')
  apply hr
  apply MvPolynomial.funext
  intro y
  obtain ⟨x, hx, hpx⟩ := h y
  have hc := congrArg (MvPolynomial.eval x) hq
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hpx,
    Polynomial.eval₂_at_zero, map_zero] at hc
  have he := MvPolynomial.comp_aeval_apply (MvPolynomial.aeval x) (f := w) r
  rw [show MvPolynomial.aeval w r = (q.coeff 0).val from hw.aeval_repr _] at he
  change MvPolynomial.eval x (q.coeff 0).val =
    MvPolynomial.eval (fun i => MvPolynomial.eval x (w i)) r at he
  rw [hx] at he
  simpa only [map_zero] using he.symm.trans hc

end
end ModifiedCartan

#print axioms ModifiedCartan.polynomial_eq_zero_of_zero_on_every_fibre
