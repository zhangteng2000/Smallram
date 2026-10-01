import ModifiedCartan.ZCycleSupportFiniteness
import ModifiedCartan.CycleSubsetLaurentProduct
import ModifiedCartan.FiniteAlphabetShift

open scoped BigOperators Classical LaurentPolynomial

namespace ModifiedCartan
noncomputable section

theorem zComplementLaurentProduct {A B : Type*} [Fintype A] [Fintype B]
    (θ : Equiv.Perm A) (Z : Finset A) :
    (∑ C : ZComplementCycleParameters θ Z,
      LaurentPolynomial.C ((-1 : MvPolynomial B ℂ) ^ C.val.card *
        ∏ c ∈ C.val, finitePowerSumPolynomial B (permutationCycleWeight θ (fun _ => 1) c)) *
      LaurentPolynomial.T (∑ c ∈ C.val, (permutationCycleWeight θ (fun _ => 1) c : ℤ))) =
    ∏ c ∈ permutationCycleImage θ (zStripComplement θ Z),
      (1 - LaurentPolynomial.T (permutationCycleWeight θ (fun _ => 1) c : ℤ) *
        LaurentPolynomial.C (finitePowerSumPolynomial B (permutationCycleWeight θ (fun _ => 1) c))) := by
  let J := permutationCycleImage θ (zStripComplement θ Z)
  let f := fun C : Finset (PermutationCycles θ) =>
    LaurentPolynomial.C ((-1 : MvPolynomial B ℂ) ^ C.card *
      ∏ c ∈ C, finitePowerSumPolynomial B (permutationCycleWeight θ (fun _ => 1) c)) *
    LaurentPolynomial.T (∑ c ∈ C, (permutationCycleWeight θ (fun _ => 1) c : ℤ))
  have he := Finset.sum_subtype (p := fun C : Finset (PermutationCycles θ) => C ⊆ J)
    (F := inferInstance) J.powerset (by intro C; exact Finset.mem_powerset) f
  change (∑ C : {C : Finset (PermutationCycles θ) // C ⊆ J}, f C.val) = _
  rw [← he]
  exact sum_signed_laurent_subsets J
    (fun c => (permutationCycleWeight θ (fun _ => 1) c : ℤ))
    (fun c => finitePowerSumPolynomial B (permutationCycleWeight θ (fun _ => 1) c))

end
end ModifiedCartan

