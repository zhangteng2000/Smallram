import ModifiedCartan.WronskianLogInequality

open scoped Topology ENNReal
open Filter MeasureTheory Set

set_option autoImplicit false

namespace ModifiedCartan

theorem finite_sum_nonnegative_sandwich {n : ℕ} (v : FewInflection.Index n → ℝ)
    (hv : 0 ≤ ∑ j, v j) :
    0 ≤ (⨆ j, v j) ∧ ∀ j, -(n : ℝ) * (⨆ i, v i) ≤ v j ∧ v j ≤ (⨆ i, v i) := by
  classical
  let M : ℝ := ⨆ j, v j
  have hle (j : FewInflection.Index n) : v j ≤ M :=
    le_ciSup (Set.finite_range v).bddAbove j
  have hsum : (∑ j, v j) ≤ (n + 1 : ℝ) * M := by
    simpa only [Finset.sum_const, Finset.card_univ, FewInflection.Index,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => hle j)
  have hM : 0 ≤ M := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨hM, fun j => ⟨?_, hle j⟩⟩
  have hsingle := Finset.single_le_sum (s := Finset.univ) (f := fun i => M - v i)
    (fun i _ => sub_nonneg.mpr (hle i)) (Finset.mem_univ j)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    FewInflection.Index, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsingle
  change -(n : ℝ) * M ≤ v j
  nlinarith

namespace Paper

/-- LaTeX label `eq:sandwich`, for the finite AE representatives of the
component limits. Its only input is the conclusion of `lem:sum`. -/
theorem eq_sandwich {n : ℕ} {U : Set ℂ} {v : FewInflection.Index n → ℂ → ℝ}
    (hv : ∀ᵐ z ∂volume.restrict U, 0 ≤ ∑ j, v j z) :
    ∀ᵐ z ∂volume.restrict U, 0 ≤ (⨆ j, v j z) ∧
      ∀ j, -(n : ℝ) * (⨆ i, v i z) ≤ v j z ∧ v j z ≤ (⨆ i, v i z) := by
  filter_upwards [hv] with z hz
  exact finite_sum_nonnegative_sandwich (fun j => v j z) hz

end Paper


end ModifiedCartan

