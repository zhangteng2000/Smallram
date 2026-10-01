import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Fubini and the first-moment estimate select a line satisfying any
almost-everywhere side condition and the exact averaged integral bound. -/
theorem exists_good_horizontal_slice {F : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hcd : c < d)
    (hF : Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))))
    {P : ℝ → Prop} (hP : ∀ᵐ y ∂volume.restrict (Icc c d), P y) :
    ∃ y ∈ Icc c d, P y ∧ IntegrableOn (fun x => F (x, y)) (Icc a b) ∧
      (∫ x in Icc a b, F (x, y)) ≤
        (∫ z, F z ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) / (d - c) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let ν : Measure ℝ := volume.restrict (Icc c d)
  have hν : ν ≠ 0 := by
    intro hz
    have he : ν univ = 0 := by rw [hz]; rfl
    simp only [ν, Measure.restrict_apply_univ, Real.volume_Icc] at he
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd))) he
  let N : Set ℝ := {y | ¬(y ∈ Icc c d ∧ P y ∧ Integrable (fun x => F (x, y)) μ)}
  have hN : ν N = 0 := by
    apply ae_iff.mp
    filter_upwards [ae_restrict_mem measurableSet_Icc, hP, hF.prod_left_ae] with y hy hp hi
    exact ⟨hy, hp, hi⟩
  obtain ⟨y, hy, hbound⟩ := exists_notMem_null_le_average hν hF.integral_prod_right hN
  have hgood : y ∈ Icc c d ∧ P y ∧ Integrable (fun x => F (x, y)) μ := by
    simpa only [N, mem_ofPred_eq, not_not] using hy
  refine ⟨y, hgood.1, hgood.2.1, hgood.2.2, ?_⟩
  have hav : (⨍ y, ∫ x, F (x, y) ∂μ ∂ν) =
      (∫ z, F z ∂μ.prod ν) / (d - c) := by
    rw [average_eq, ← integral_prod_symm F hF]
    dsimp only [ν]
    rw [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le hcd.le]
    simp only [smul_eq_mul]
    ring
  rw [hav] at hbound
  exact hbound

/-- A nonzero polynomial has no zeros on almost every complete horizontal line. -/
theorem polynomial_horizontal_zero_free_ae (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∀ᵐ y : ℝ, ∀ x : ℝ, P.eval (⟨x, y⟩ : ℂ) ≠ 0 := by
  have hz : {z : ℂ | P.eval z = 0}.Finite := Polynomial.finite_setOfPred_isRoot hP
  let N : Set ℝ := Complex.im '' {z : ℂ | P.eval z = 0}
  have hN : volume N = 0 := (hz.image Complex.im).measure_zero volume
  have he : ∀ᵐ y : ℝ, y ∉ N := by
    apply ae_iff.mpr
    simpa using hN
  filter_upwards [he] with y hy
  intro x hx
  exact hy ⟨(⟨x, y⟩ : ℂ), hx, rfl⟩

/-- The same null exceptional set can avoid every polynomial in a sequence. -/
theorem polynomial_sequence_horizontal_zero_free_ae (P : ℕ → Polynomial ℂ)
    (hP : ∀ n, P n ≠ 0) :
    ∀ᵐ y : ℝ, ∀ n : ℕ, ∀ x : ℝ, (P n).eval (⟨x, y⟩ : ℂ) ≠ 0 := by
  exact ae_all_iff.mpr (fun n => polynomial_horizontal_zero_free_ae (P n) (hP n))

end ModifiedCartan
#print axioms ModifiedCartan.exists_good_horizontal_slice
#print axioms ModifiedCartan.polynomial_sequence_horizontal_zero_free_ae


