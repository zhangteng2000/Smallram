import ModifiedCartan.StrictPhaseCone
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Data.Finset.Max

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem dense_nonzero_complex_real_product {d : ℂ} (hd : d ≠ 0) :
    Dense {w : ℂ | (d * w).re ≠ 0} := by
  let L : ℂ →ₗ[ℝ] ℝ :=
    { toFun := fun w => (d * w).re
      map_add' := by intro x y; simp only [mul_add, Complex.add_re]
      map_smul' := by intro t w; simp only [mul_smul_comm, Complex.smul_re, RingHom.id_apply] }
  have hi : interior (L.ker : Set ℂ) = ∅ := by
    by_contra hne
    have ht := L.ker.eq_top_of_nonempty_interior' (nonempty_iff_ne_empty.mpr hne)
    have hm : d⁻¹ ∈ L.ker := by rw [ht]; trivial
    change (d * d⁻¹).re = 0 at hm
    simpa only [mul_inv_cancel₀ hd, Complex.one_re, one_ne_zero] using hm
  exact interior_eq_empty_iff_dense_compl.mp hi

def genericPhaseDirections (A : Finset ℂ) : Set ℂ :=
  {w | ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((a - b) * w).re ≠ 0}

theorem dense_genericPhaseDirections (A : Finset ℂ) : Dense (genericPhaseDirections A) := by
  classical
  let D : ℂ × ℂ → Set ℂ := fun p => {w | p.1 ≠ p.2 → ((p.1 - p.2) * w).re ≠ 0}
  have he : genericPhaseDirections A = ⋂ p ∈ (↑(A.product A) : Set (ℂ × ℂ)), D p := by
    ext w
    simp only [genericPhaseDirections, D, mem_setOf_eq, mem_iInter, Finset.mem_coe,
      Finset.mem_product, Prod.forall, and_imp]
    aesop
  rw [he]
  refine dense_biInter_of_isOpen ?_ (A.product A).finite_toSet.countable ?_
  · intro p _
    by_cases hp : p.1 = p.2
    · simp only [D, hp, ne_eq, not_true_eq_false, false_implies, setOf_true]
      exact isOpen_univ
    · simp only [D, hp, ne_eq, not_false_eq_true, true_implies]
      exact isOpen_ne_fun (Complex.continuous_re.comp (continuous_const.mul continuous_id)) continuous_const
  · intro p _
    by_cases hp : p.1 = p.2
    · simp only [D, hp, ne_eq, not_true_eq_false, false_implies, setOf_true]
      exact dense_univ
    · simp only [D, hp, ne_eq, not_false_eq_true, true_implies]
      exact dense_nonzero_complex_real_product (sub_ne_zero.mpr hp)

theorem exists_strictPhaseCone_of_generic {A : Finset ℂ} (hA : A.Nonempty)
    {w : ℂ} (hw : w ∈ genericPhaseDirections A) :
    ∃ a ∈ A, w ∈ strictPhaseCone A a := by
  obtain ⟨a, ha, hmax⟩ := A.exists_max_image (fun b => (b * w).re) hA
  refine ⟨a, ha, ?_⟩
  intro b hb hba
  have hn := hw a ha b hb (Ne.symm hba)
  have hl : 0 ≤ ((a - b) * w).re := by
    simp only [sub_mul, Complex.sub_re]
    exact sub_nonneg.mpr (hmax b hb)
  exact lt_of_le_of_ne hl (Ne.symm hn)

end ModifiedCartan
#print axioms ModifiedCartan.dense_genericPhaseDirections

