import ModifiedCartan.SharpnessRootIndicator
import Mathlib.Logic.Equiv.Fin.Rotate

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem cyclicSuccessor_eq_finRotate {q : ℕ} (i : Fin q) :
    cyclicSuccessor i = finRotate q i := by
  cases q with
  | zero => exact i.elim0
  | succ n =>
    apply Fin.ext
    rw [coe_finRotate]
    change (i.val + 1) % (n + 1) = if i = Fin.last n then 0 else i.val + 1
    by_cases hi : i = Fin.last n
    · simp only [hi, Fin.val_last, Nat.mod_self, ite_true]
    · have hlt := Fin.val_lt_last hi
      rw [ite_eq_right hi, Nat.mod_eq_of_lt (by omega)]

theorem cyclicSuccessor_surjective {q : ℕ} : Function.Surjective (cyclicSuccessor (q := q)) := by
  intro i
  obtain ⟨j, hj⟩ := (finRotate q).surjective i
  exact ⟨j, by rw [cyclicSuccessor_eq_finRotate, hj]⟩

theorem sharpnessRoot_successor {q : ℕ} (hq : 1 ≤ q) (j : Fin q) :
    sharpnessRoot q (cyclicSuccessor j) = rayPhase (2 * Real.pi / q) * sharpnessRoot q j := by
  have he : rayPhase (2 * Real.pi / q) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) := by
    unfold rayPhase
    congr 1
    push_cast
    ring
  rw [he]
  unfold sharpnessRoot cyclicSuccessor
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) ^ ((j.val + 1) % q) =
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) ^ j.val
  by_cases hj : j.val + 1 < q
  · rw [Nat.mod_eq_of_lt hj, pow_succ]
    ring
  · have hlast : j.val + 1 = q := by have := j.isLt; omega
    rw [hlast, Nat.mod_self, pow_zero]
    have hp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) ^ j.val =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) ^ q := by
      calc
        _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) ^ (j.val + 1) := by rw [pow_succ]; ring
        _ = _ := congrArg (fun m : ℕ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I / q) ^ m) hlast
    rw [hp, (Complex.isPrimitiveRoot_exp q (by omega)).pow_eq_one]

theorem sharpnessRootIndicator_periodic {q : ℕ} (hq : 1 ≤ q) :
    Function.Periodic (sharpnessRootIndicator q hq) (2 * Real.pi / q) := by
  intro φ
  have he (j : Fin q) : (rayPhase (φ + 2 * Real.pi / q) * sharpnessRoot q j).re =
      (rayPhase φ * sharpnessRoot q (cyclicSuccessor j)).re := by
    rw [sharpnessRoot_successor hq, ← mul_assoc, rayPhase_mul]
  unfold sharpnessRootIndicator
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    rw [he j]
    exact sharpnessRootIndicator_le hq φ (cyclicSuccessor j)
  · apply Finset.sup'_le
    intro j _
    obtain ⟨i, rfl⟩ := cyclicSuccessor_surjective j
    rw [← he i]
    exact sharpnessRootIndicator_le hq (φ + 2 * Real.pi / q) i

theorem sharpnessRoot_phase {q : ℕ} (j : Fin q) :
    sharpnessRoot q j = rayPhase (2 * (Real.pi / q) * (j.val : ℝ)) := by
  rw [sharpnessRoot_exp]
  unfold rayPhase
  congr 1
  push_cast
  ring

theorem sharpnessRoot_real_cos {q : ℕ} (φ : ℝ) (j : Fin q) :
    (rayPhase φ * sharpnessRoot q j).re = Real.cos (φ + 2 * (Real.pi / q) * (j.val : ℝ)) := by
  rw [sharpnessRoot_phase, rayPhase_mul]
  exact Complex.exp_ofReal_mul_I_re _

/-- On a centered fundamental sector the nearest root is 1. -/
theorem sharpnessRootIndicator_eq_cos {q : ℕ} (hq : 1 ≤ q) {φ : ℝ}
    (hφ : φ ∈ Icc (-(Real.pi / q)) (Real.pi / q)) :
    sharpnessRootIndicator q hq φ = Real.cos φ := by
  have hqp : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  let p : ℝ := Real.pi / q
  have hp : 0 < p := div_pos Real.pi_pos hqp
  have hqpi : (q : ℝ) * p = Real.pi := by dsimp [p]; field_simp
  have habs : |φ| ≤ p := abs_le.mpr hφ
  have hbound (j : Fin q) : Real.cos (φ + 2 * p * (j.val : ℝ)) ≤ Real.cos φ := by
    by_cases hj : j.val = 0
    · simp only [hj, Nat.cast_zero, mul_zero, add_zero, le_refl]
    have hjlo : (1 : ℝ) ≤ j.val := by exact_mod_cast (show 1 ≤ j.val by omega)
    have hjhi : (j.val : ℝ) + 1 ≤ q := by exact_mod_cast j.isLt
    let a : ℝ := φ + 2 * p * (j.val : ℝ)
    have halo : p ≤ a := by dsimp [a]; nlinarith [hφ.1]
    have hahi : a ≤ 2 * Real.pi - p := by dsimp [a]; nlinarith [hφ.2]
    by_cases ha : a ≤ Real.pi
    · have hh := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ) ha (habs.trans halo)
      simpa only [Real.cos_abs] using hh
    · have hx : |φ| ≤ 2 * Real.pi - a := by linarith
      have hxpi : 2 * Real.pi - a ≤ Real.pi := by linarith
      have hh := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ) hxpi hx
      have he : Real.cos (2 * Real.pi - a) = Real.cos a := by
        rw [show 2 * Real.pi - a = -(a - 2 * Real.pi) by ring, Real.cos_neg, Real.cos_sub_two_pi]
      rw [he, Real.cos_abs] at hh
      exact hh
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    rw [sharpnessRoot_real_cos]
    exact hbound j
  · have he := sharpnessRootIndicator_le hq φ (⟨0, by omega⟩ : Fin q)
    simpa only [sharpnessRoot_real_cos, Nat.cast_zero, mul_zero, add_zero] using he

end ModifiedCartan
#print axioms ModifiedCartan.sharpnessRootIndicator_periodic
#print axioms ModifiedCartan.sharpnessRootIndicator_eq_cos


