import ModifiedCartan.LocalRootSeparation
import Mathlib.Data.Finset.Max

open scoped Topology BigOperators Classical
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- A finite gap immediately above eight preserves exactly the certified
inner and outer root sets while putting the separating radius in (8,10). -/
theorem exists_radius_separating_finset (S : Finset ℝ) :
    ∃ η : ℝ, 8 < η ∧ η < 10 ∧ ∀ r ∈ S,
      (r < η ↔ r ≤ 8) ∧ (η < r ↔ 8 < r) := by
  let T := S.filter (fun r => 8 < r)
  by_cases hT : T.Nonempty
  · obtain ⟨b, hb, hmin⟩ := T.exists_min_image id hT
    have hb8 : 8 < b := (Finset.mem_filter.mp hb).2
    let η : ℝ := (8 + min b 10) / 2
    have h8 : 8 < η := by dsimp [η]; have := lt_min hb8 (by norm_num : (8 : ℝ) < 10); linarith
    have hηb : η < b := by dsimp [η]; have := min_le_left b 10; linarith
    have h10 : η < 10 := by dsimp [η]; have := min_le_right b 10; linarith
    refine ⟨η, h8, h10, ?_⟩
    intro r hr
    by_cases hr8 : r ≤ 8
    · constructor <;> constructor <;> intro h
      · exact hr8
      · linarith
      · linarith
      · linarith
    · have hrT : r ∈ T := Finset.mem_filter.mpr ⟨hr, lt_of_not_ge hr8⟩
      have hbr : b ≤ r := hmin r hrT
      constructor <;> constructor <;> intro h
      · linarith
      · exact False.elim (hr8 h)
      · exact lt_of_not_ge hr8
      · linarith
  · refine ⟨9, by norm_num, by norm_num, ?_⟩
    intro r hr
    have hr8 : r ≤ 8 := by
      by_contra h
      exact hT ⟨r, Finset.mem_filter.mpr ⟨hr, lt_of_not_ge h⟩⟩
    constructor <;> constructor <;> intro h <;> linarith

/-- LaTeX `lem:replacement`, separating-radius data. Extra finite radii
can be excluded at the same time, for example the roots of the monic P. -/
theorem exists_separating_radius_root_indices {M : ℕ} (a : Fin M → ℂ)
    (extra : Finset ℝ) :
    ∃ η : ℝ, 8 < η ∧ η < 10 ∧
      (∀ i, ‖a i‖ ≠ η) ∧
      (Finset.univ.filter (fun i => ‖a i‖ < η) = interiorRootIndices a) ∧
      (Finset.univ.filter (fun i => η < ‖a i‖) = exteriorRootIndices a) ∧
      ∀ r ∈ extra, r ≠ η := by
  obtain ⟨η, h8, h10, hgap⟩ := exists_radius_separating_finset
    ((Finset.univ.image (fun i => ‖a i‖)) ∪ extra)
  have hi (i : Fin M) := hgap ‖a i‖
    (Finset.mem_union_left extra (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  refine ⟨η, h8, h10, ?_, ?_, ?_, ?_⟩
  · intro i he
    have hle := (hi i).1
    have hgt := (hi i).2
    rw [he] at hgt
    exact (lt_irrefl η) (hgt.mpr h8)
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, interiorRootIndices]
    exact (hi i).1
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, exteriorRootIndices]
    exact (hi i).2
  · intro r hr he
    have hg := (hgap r (Finset.mem_union_right _ hr)).2
    rw [he] at hg
    exact (lt_irrefl η) (hg.mpr h8)

end
end ModifiedCartan
#print axioms ModifiedCartan.exists_separating_radius_root_indices
