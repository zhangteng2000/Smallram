import ModifiedCartan.YoungPolytabloid
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- A finite family with distinct leading coordinates and strictly lower
weights on all other supported coordinates is linearly independent. -/
theorem linearIndependent_of_strict_leading_weight {I J : Type*} [Fintype I]
    (v : I → ℂ[J]) (lead : I → J) (w : J → ℕ) (hinj : Function.Injective lead)
    (hdiag : ∀ i, (v i).coeff (lead i) = 1)
    (hlow : ∀ i j, j ≠ lead i → (v i).coeff j ≠ 0 → w j < w (lead i)) :
    LinearIndependent ℂ v := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  by_contra hi
  let s : Finset I := Finset.univ.filter (fun i => a i ≠ 0)
  have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s (fun i => w (lead i)) hs
  have ham : a m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hother : ∀ j : I, j ≠ m → a j * (v j).coeff (lead m) = 0 := by
    intro j hj
    by_cases haj : a j = 0
    · rw [haj, zero_mul]
    · have hjm : w (lead j) ≤ w (lead m) :=
        hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, haj⟩)
      have hne : lead m ≠ lead j := fun he => hj (hinj he.symm)
      have hc : (v j).coeff (lead m) = 0 := by
        by_contra hc
        have hh := hlow j (lead m) hne hc
        omega
      rw [hc, mul_zero]
  have hcoef := congrArg (fun z : ℂ[J] => z.coeff (lead m)) ha
  change (∑ j, a j • v j).coeff (lead m) = 0 at hcoef
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at hcoef
  rw [Finset.sum_eq_single m] at hcoef
  · rw [hdiag, mul_one] at hcoef
    exact ham hcoef
  · intro j _ hj
    exact hother j hj
  · simp

end
end ModifiedCartan


