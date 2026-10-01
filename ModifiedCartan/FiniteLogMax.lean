import ModifiedCartan.SubharmonicSup
import ModifiedCartan.SubharmonicRepresentative
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem ereal_coe_finset_sup' {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (v : ι → ℝ) :
    ((s.sup' hne v : ℝ) : EReal) = s.sup (fun i => (v i : EReal)) := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' hne v
  apply le_antisymm
  · rw [he]
    exact Finset.le_sup (f := fun i => (v i : EReal)) hj
  · apply Finset.sup_le
    intro i hi
    exact EReal.coe_le_coe_iff.mpr (Finset.le_sup' v hi)

theorem real_finset_max_nonneg_of_sum_nonneg {n : ℕ} (v : Index n → ℝ)
    (h : 0 ≤ ∑ j, v j) : 0 ≤ Finset.univ.sup' Finset.univ_nonempty v := by
  have hh : (∑ j, v j) ≤ (n + 1 : ℝ) * Finset.univ.sup' Finset.univ_nonempty v := by
    calc
      _ ≤ ∑ _j : Index n, Finset.univ.sup' Finset.univ_nonempty v :=
        Finset.sum_le_sum (fun j _ => Finset.le_sup' v (Finset.mem_univ j))
      _ = _ := by simp [Index, FewInflection.Index]
  have hp : 0 < (n + 1 : ℝ) := by positivity
  exact nonneg_of_mul_nonneg_right (h.trans hh) hp

/-- The actual finite maximum of the coordinate subharmonic limits is
subharmonic and nonnegative everywhere once their sum is nonnegative AE. -/
theorem subharmonic_coordinate_max_nonneg {n : ℕ} {D : Set ℂ} (hD : IsOpen D)
    {u : Index n → ℂ → EReal} {v : Index n → ℂ → ℝ}
    (hu : ∀ j, IsSubharmonicOn D (u j))
    (hrep : ∀ j, u j =ᵐ[volume.restrict D] (fun z => (v j z : EReal)))
    (hsum : ∀ᵐ z ∂volume.restrict D, 0 ≤ ∑ j, v j z) :
    IsSubharmonicOn D (fun z => Finset.univ.sup (fun j => u j z)) ∧
      (fun z => Finset.univ.sup (fun j => u j z)) =ᵐ[volume.restrict D]
        (fun z => ((Finset.univ.sup' Finset.univ_nonempty (fun j => v j z) : ℝ) : EReal)) ∧
      ∀ z ∈ D, 0 ≤ Finset.univ.sup (fun j => u j z) := by
  have hsub := isSubharmonicOn_finset_sup Finset.univ u (fun j _ => hu j)
  have hae : (fun z => Finset.univ.sup (fun j => u j z)) =ᵐ[volume.restrict D]
      (fun z => ((Finset.univ.sup' Finset.univ_nonempty (fun j => v j z) : ℝ) : EReal)) := by
    filter_upwards [ae_all_iff.mpr hrep] with z hz
    simp only [hz, ereal_coe_finset_sup']
  refine ⟨hsub, hae, ?_⟩
  apply (isSubharmonicOn_const D (0 : EReal) EReal.zero_ne_top).le_of_ae_le_upperSemicontinuous
    hsub.upperSemicontinuousOn hD
  filter_upwards [hae, hsum] with z hz hsz
  rw [hz]
  exact_mod_cast real_finset_max_nonneg_of_sum_nonneg (fun j => v j z) hsz

end ModifiedCartan
#print axioms ModifiedCartan.subharmonic_coordinate_max_nonneg
