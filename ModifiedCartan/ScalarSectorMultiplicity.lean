import ModifiedCartan.ScalarSectorData
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Number of sectors in the actual finite family assigned to a sphere target. -/
noncomputable def scalarSectorMultiplicity {m : ℕ} (β : Fin m → WithTop ℂ)
    (a : WithTop ℂ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => β j = a)).card

theorem scalarSectorMultiplicity_zero_of_not_mem {m : ℕ} (β : Fin m → WithTop ℂ)
    {a : WithTop ℂ} (ha : a ∉ Finset.univ.image β) :
    scalarSectorMultiplicity β a = 0 := by
  classical
  unfold scalarSectorMultiplicity
  apply Finset.card_eq_zero.mpr
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro he
  exact ha (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, he⟩)

theorem scalarSectorMultiplicity_pos_iff {m : ℕ} (β : Fin m → WithTop ℂ)
    (a : WithTop ℂ) : 0 < scalarSectorMultiplicity β a ↔ ∃ j, β j = a := by
  classical
  simp only [scalarSectorMultiplicity, Finset.card_pos, Finset.Nonempty,
    Finset.mem_filter, Finset.mem_univ, true_and]

theorem scalarSectorMultiplicity_sum {m : ℕ} (β : Fin m → WithTop ℂ) :
    ∑ a ∈ Finset.univ.image β, scalarSectorMultiplicity β a = m := by
  classical
  have hfilter : Finset.univ.filter (fun j : Fin m => β j ∈ Finset.univ.image β) = Finset.univ :=
    Finset.filter_eq_self.mpr (fun j hj => Finset.mem_image_of_mem β hj)
  calc
    _ = (Finset.univ.filter (fun j : Fin m => β j ∈ Finset.univ.image β)).card :=
      Finset.sum_card_fiberwise_eq_card_filter Finset.univ (Finset.univ.image β) β
    _ = m := by rw [hfilter, Finset.card_univ, Fintype.card_fin]

theorem scalarSectorMultiplicity_hasSum {m : ℕ} (β : Fin m → WithTop ℂ) :
    HasSum (fun a => (scalarSectorMultiplicity β a : ℝ)) (m : ℝ) := by
  classical
  have hh : HasSum (fun a => (scalarSectorMultiplicity β a : ℝ))
      (∑ a ∈ Finset.univ.image β, (scalarSectorMultiplicity β a : ℝ)) :=
    hasSum_sum_of_ne_finset_zero (fun a ha => by
      rw [scalarSectorMultiplicity_zero_of_not_mem β ha, Nat.cast_zero])
  have he : (∑ a ∈ Finset.univ.image β, (scalarSectorMultiplicity β a : ℝ)) = (m : ℝ) := by
    exact_mod_cast scalarSectorMultiplicity_sum β
  simpa only [he] using hh

/-- The exact total count of the constructed subsequence targets. Identifying
these counts with rho times the scalar deficiencies is a separate theorem. -/
theorem ScalarSectorSubsequenceData.target_multiplicities_hasSum
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    (e : ScalarSectorSubsequenceData d) :
    HasSum (fun a => (scalarSectorMultiplicity e.target a : ℝ)) (2 * ρ) := by
  have he : (e.count : ℝ) = 2 * ρ := by linarith [e.order_eq]
  rw [← he]
  exact scalarSectorMultiplicity_hasSum e.target

end ModifiedCartan
#print axioms ModifiedCartan.scalarSectorMultiplicity_hasSum
#print axioms ModifiedCartan.ScalarSectorSubsequenceData.target_multiplicities_hasSum
