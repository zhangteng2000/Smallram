import ModifiedCartan.SchubertMonicWronskian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- A monic complex polynomial admits the parameter convention `X + z_i`
    with repeated roots retained. Auxiliary to `lem:KP-correspondence`. -/
theorem complex_monic_eq_prod_linear {M : ℕ} (p : Polynomial ℂ)
    (hp : p.Monic) (hd : p.natDegree = M) :
    ∃ z : Fin M → ℂ, p = ∏ i : Fin M, (Polynomial.X + Polynomial.C (z i)) := by
  let l := p.roots.toList
  have hl : l.length = M := by
    rw [Multiset.length_toList, ← (IsAlgClosed.splits p).natDegree_eq_card_roots, hd]
  have hprod : (l.map (fun r => Polynomial.X - Polynomial.C r)).prod =
      ∏ i : Fin l.length, (Polynomial.X - Polynomial.C (l.get i)) := by
    rw [← Fin.prod_ofFn]
    congr 1
    simpa only [Function.comp_def, List.ofFn_get] using
      (List.map_ofFn (f := l.get) (g := fun r : ℂ => Polynomial.X - Polynomial.C r))
  have he : ∃ z : Fin l.length → ℂ,
      p = ∏ i : Fin l.length, (Polynomial.X + Polynomial.C (z i)) := by
    refine ⟨fun i => -(l.get i), ?_⟩
    rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp,
      ← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.prod_coe]
    rw [hprod]
    simp only [map_neg, sub_eq_add_neg]
  rw [hl] at he
  exact he

/-- A monic polynomial with arbitrary coefficients below its prescribed degree. -/
def monicPolynomialFromCoefficients {M : ℕ} (c : Fin M → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ M + ∑ i : Fin M, Polynomial.C (c i) * Polynomial.X ^ i.val

theorem monicPolynomialFromCoefficients_monic {M : ℕ} (c : Fin M → ℂ) :
    (monicPolynomialFromCoefficients c).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c)

theorem monicPolynomialFromCoefficients_natDegree {M : ℕ} (c : Fin M → ℂ) :
    (monicPolynomialFromCoefficients c).natDegree = M := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [monicPolynomialFromCoefficients, Polynomial.degree_add_eq_left_of_degree_lt,
    Polynomial.degree_X_pow]
  simpa only [Polynomial.degree_X_pow] using Polynomial.degree_sum_fin_lt c

theorem monicPolynomialFromCoefficients_coeff {M : ℕ} (c : Fin M → ℂ) (j : Fin M) :
    (monicPolynomialFromCoefficients c).coeff j.val = c j := by
  rw [monicPolynomialFromCoefficients, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    ite_eq_right (Nat.ne_of_lt j.isLt), zero_add, Polynomial.finsetSum_coeff]
  simp only [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
  simpa only [Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left] 

end
end ModifiedCartan

#print axioms ModifiedCartan.complex_monic_eq_prod_linear
