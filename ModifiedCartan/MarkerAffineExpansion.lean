import ModifiedCartan.MarkerAssignmentDegree
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def markerAssignmentWeight {A B R : Type*} [Fintype B] [CommMonoid R]
    (h : B → R) (w : A → B → R) (c : B → Option A) : R :=
  ∏ b : B, (c b).elim (h b) (fun a => w a b)

def markerAffineProduct {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]
    (h : B → R) (w : A → B → R) : MvPolynomial A R :=
  ∏ b : B, (MvPolynomial.C (h b) + ∑ a : A, MvPolynomial.X a * MvPolynomial.C (w a b))

theorem markerAffineProduct_expansion {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (h : B → R) (w : A → B → R) :
    markerAffineProduct h w = ∑ c : B → Option A,
      MvPolynomial.monomial (markerAssignmentDegree c) (markerAssignmentWeight h w c) := by
  let f : B → Option A → MvPolynomial A R := fun b o =>
    MvPolynomial.monomial (o.elim 0 (fun a => Finsupp.single a 1))
      (o.elim (h b) (fun a => w a b))
  have hf (b : B) : (∑ o : Option A, f b o) =
      MvPolynomial.C (h b) + ∑ a : A, MvPolynomial.X a * MvPolynomial.C (w a b) := by
    rw [Fintype.sum_option]
    apply congrArg (fun q => MvPolynomial.C (h b) + q)
    apply Finset.sum_congr rfl
    intro a ha
    change MvPolynomial.monomial (Finsupp.single a 1) (w a b) =
      MvPolynomial.monomial (Finsupp.single a 1) 1 * MvPolynomial.C (w a b)
    rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]
  calc
    _ = ∏ b : B, ∑ o : Option A, f b o := by simp only [markerAffineProduct, hf]
    _ = ∑ c : B → Option A, ∏ b : B, f b (c b) := Fintype.prod_sum f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (MvPolynomial.monomial_sum_prod Finset.univ
        (fun b => (c b).elim 0 (fun a => Finsupp.single a 1))
        (fun b => (c b).elim (h b) (fun a => w a b))).symm

theorem markerAffineProduct_coeff {A B R : Type*} [Fintype A] [Fintype B]
    [CommSemiring R] (h : B → R) (w : A → B → R) (d : A →₀ ℕ) :
    MvPolynomial.coeff d (markerAffineProduct h w) = ∑ c : B → Option A,
      if markerAssignmentDegree c = d then markerAssignmentWeight h w c else 0 := by
  rw [markerAffineProduct_expansion, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]

end
end ModifiedCartan

