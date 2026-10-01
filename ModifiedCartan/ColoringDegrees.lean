import ModifiedCartan.ColoringOrbits
import ModifiedCartan.FiniteCyclePolynomials

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def coloringDegree {A B : Type*} [Fintype A] (f : A → B) : B →₀ ℕ :=
  ∑ a : A, Finsupp.single (f a) 1

theorem coloringDegree_comp_equiv {A C B : Type*} [Fintype A] [Fintype C]
    (f : A → B) (e : C ≃ A) : coloringDegree (f ∘ e) = coloringDegree f :=
  e.sum_comp (fun a => Finsupp.single (f a) 1)

theorem coloringDegree_apply {A B : Type*} [Fintype A] (f : A → B) (b : B) :
    coloringDegree f b = Fintype.card {a : A // f a = b} := by
  simp only [coloringDegree, Finsupp.finsetSum_apply, Finsupp.single_apply, Fintype.card_subtype,
    Finset.card_filter]

theorem coloringDegree_monomial {A B R : Type*} [Fintype A] [CommSemiring R] (f : A → B) :
    (MvPolynomial.monomial (coloringDegree f) 1 : MvPolynomial B R) =
      ∏ a : A, MvPolynomial.X (f a) := by
  rw [coloringDegree, MvPolynomial.monomial_sum_one]
  rfl

theorem coloringDegree_sum {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    ∑ b : B, coloringDegree f b = Fintype.card A := by
  simp only [coloringDegree, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

theorem coloringDegree_weight {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (w : B → ℕ) :
    ∑ b : B, w b * coloringDegree f b = ∑ a : A, w (f a) := by
  simp only [coloringDegree, Finsupp.finsetSum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

end
end ModifiedCartan


