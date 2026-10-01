import ModifiedCartan.FiniteBernstein

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem toLaurent_coeff_eq_zero_of_neg {R : Type*} [Semiring R]
    (p : Polynomial R) (n : ℤ) (hn : n < 0) : p.toLaurent.coeff n = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [LaurentPolynomial.support_coeff_toLaurent]
  intro hmem
  obtain ⟨m, hm, he⟩ := Finset.mem_map.mp hmem
  have he' : (m : ℤ) = n := he
  omega

def finiteElementaryPolynomial (B : Type*) [Fintype B] : Polynomial (MvPolynomial B ℂ) :=
  ∏ b : B, (1 - Polynomial.C (MvPolynomial.X b) * Polynomial.X)

theorem finiteElementaryLaurent_eq_toLaurent (B : Type*) [Fintype B] :
    finiteElementaryLaurent B = (finiteElementaryPolynomial B).toLaurent := by
  simp only [finiteElementaryLaurent, finiteElementaryPolynomial, map_prod, map_sub, map_one,
    map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X]

theorem finiteElementaryLaurent_coeff_neg (B : Type*) [Fintype B] (n : ℤ) (hn : n < 0) :
    (finiteElementaryLaurent B).coeff n = 0 := by
  rw [finiteElementaryLaurent_eq_toLaurent]
  exact toLaurent_coeff_eq_zero_of_neg _ n hn

theorem finiteBernstein_one_residue (B : Type*) [Fintype B] :
    (finiteBernstein B 1).coeff (-1) = 0 := by
  rw [finiteBernstein, map_one, mul_one]
  exact finiteElementaryLaurent_coeff_neg B (-1) (by norm_num)

end
end ModifiedCartan

