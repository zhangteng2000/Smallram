import ModifiedCartan.RayPhases
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

open scoped Topology BigOperators
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def sharpnessRootIndicator (q : ℕ) (hq : 1 ≤ q) (φ : ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    (fun j : Fin q => (rayPhase φ * sharpnessRoot q j).re)

theorem sharpnessRootIndicator_le {q : ℕ} (hq : 1 ≤ q) (φ : ℝ) (j : Fin q) :
    (rayPhase φ * sharpnessRoot q j).re ≤ sharpnessRootIndicator q hq φ :=
  Finset.le_sup' (fun l : Fin q => (rayPhase φ * sharpnessRoot q l).re) (Finset.mem_univ j)

theorem sharpnessRootIndicator_attained {q : ℕ} (hq : 1 ≤ q) (φ : ℝ) :
    ∃ j : Fin q, sharpnessRootIndicator q hq φ = (rayPhase φ * sharpnessRoot q j).re := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ : Finset (Fin q)).Nonempty from ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
    (fun j : Fin q => (rayPhase φ * sharpnessRoot q j).re)
  exact ⟨j, hj⟩

theorem sharpnessRootIndicator_continuous {q : ℕ} (hq : 1 ≤ q) :
    Continuous (sharpnessRootIndicator q hq) := by
  apply Continuous.finset_sup'_apply
  intro j _
  unfold rayPhase
  fun_prop

theorem sharpnessRoot_sum_zero {q : ℕ} (hq : 2 ≤ q) :
    (∑ j : Fin q, sharpnessRoot q j) = 0 := by
  let j0 : Fin q := ⟨0, by omega⟩
  let j1 : Fin q := ⟨1, by omega⟩
  have hne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) ≠ 1 := by
    intro he
    have hr : sharpnessRoot q j1 = sharpnessRoot q j0 := by simp [sharpnessRoot, j0, j1, he]
    have hv := congrArg Fin.val (sharpnessRoot_injective (by omega : 1 ≤ q) hr)
    simp only [j0, j1] at hv
    omega
  simp only [sharpnessRoot]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hne,
    (Complex.isPrimitiveRoot_exp q (by omega)).pow_eq_one, sub_self, zero_div]

theorem sharpnessRoot_real_sum_zero {q : ℕ} (hq : 2 ≤ q) (φ : ℝ) :
    (∑ j : Fin q, (rayPhase φ * sharpnessRoot q j).re) = 0 := by
  have hh : (∑ j : Fin q, rayPhase φ * sharpnessRoot q j) = 0 := by
    rw [← Finset.mul_sum, sharpnessRoot_sum_zero hq, mul_zero]
  have he := congrArg Complex.re hh
  simpa only [Complex.re_sum, Complex.zero_re] using he

theorem sharpnessRootIndicator_pos_of_cos_ne_zero {q : ℕ} (hq : 2 ≤ q) {φ : ℝ}
    (hcos : Real.cos φ ≠ 0) : 0 < sharpnessRootIndicator q (by omega) φ := by
  by_contra hn
  have hnon : ∀ j ∈ (Finset.univ : Finset (Fin q)), (rayPhase φ * sharpnessRoot q j).re ≤ 0 :=
    fun j _ => (sharpnessRootIndicator_le (by omega : 1 ≤ q) φ j).trans (le_of_not_gt hn)
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hnon).mp (sharpnessRoot_real_sum_zero hq φ)
  have hh := hz ⟨0, by omega⟩ (Finset.mem_univ _)
  apply hcos
  simpa only [sharpnessRoot, pow_zero, mul_one, rayPhase, Complex.exp_ofReal_mul_I_re] using hh

theorem ae_cos_mul_ne_zero {ρ : ℝ} (hρ : ρ ≠ 0) :
    ∀ᵐ θ : ℝ, Real.cos (ρ * θ) ≠ 0 := by
  have he := (countable_range (fun l : ℤ => ((2 * (l : ℝ) + 1) * Real.pi / 2) / ρ)).ae_notMem volume
  filter_upwards [he] with θ hθ
  intro hzero
  obtain ⟨l, hl⟩ := Real.cos_eq_zero_iff.mp hzero
  apply hθ
  refine ⟨l, ?_⟩
  apply (div_eq_iff hρ).mpr
  simpa only [mul_comm] using hl.symm

theorem sharpnessRootIndicator_ae_pos {q : ℕ} (hq : 2 ≤ q) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ∀ᵐ θ : ℝ, 0 < sharpnessRootIndicator q (by omega) (ρ * θ) := by
  filter_upwards [ae_cos_mul_ne_zero hρ] with θ hθ
  exact sharpnessRootIndicator_pos_of_cos_ne_zero hq hθ

end ModifiedCartan
#print axioms ModifiedCartan.sharpnessRootIndicator_ae_pos

