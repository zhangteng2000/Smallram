import ModifiedCartan.StrongIndexPowerBounds

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The growth function in additive logarithmic coordinates. -/
def logGrowthProfile (T : ℝ → ℝ) (x : ℝ) : ℝ := Real.log (T (Real.exp x))

theorem monotone_logGrowthProfile (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) (hm : MonotoneOn T (Ioi 0)) :
    Monotone (logGrowthProfile T) := by
  intro x y hxy
  exact Real.log_le_log (hT _ (Real.exp_pos x))
    (hm (Real.exp_pos x) (Real.exp_pos y) (Real.exp_le_exp_of_le hxy))

theorem strongUpperIndex_le_of_log_slope (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {p B D C : ℝ}
    (hb : ∀ x y, B ≤ x → x + D ≤ y →
      logGrowthProfile T y - logGrowthProfile T x ≤ p * (y - x) + C) :
    strongUpperIndex T ≤ (p : EReal) := by
  apply strongUpperIndex_le_of_uniform_upper T hT (Real.exp_pos C)
    (Real.one_le_exp (le_max_right D 0)) (Real.one_le_exp (le_max_right B 0))
  intro x r hx hr
  have hx0 : 0 < x := (Real.exp_pos (max D 0)).trans_le hx
  have hr0 : 0 < r := (Real.exp_pos (max B 0)).trans_le hr
  have hxlog : D ≤ Real.log x := by
    have hl := Real.log_le_log (Real.exp_pos (max D 0)) hx
    rw [Real.log_exp] at hl
    exact (le_max_left _ _).trans hl
  have hrlog : B ≤ Real.log r := by
    have hl := Real.log_le_log (Real.exp_pos (max B 0)) hr
    rw [Real.log_exp] at hl
    exact (le_max_left _ _).trans hl
  have hs := hb (Real.log r) (Real.log x + Real.log r) hrlog (by linarith)
  simp only [logGrowthProfile, Real.exp_add, Real.exp_log hx0, Real.exp_log hr0] at hs
  have hlog : Real.log (T (x * r)) ≤ C + Real.log x * p + Real.log (T r) := by
    nlinarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_add, Real.exp_log (hT _ (mul_pos hx0 hr0)),
    Real.exp_log (hT r hr0), ← Real.rpow_def_of_pos hx0 p] at he
  exact he

theorem le_strongLowerIndex_of_log_slope (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) {p B D C : ℝ}
    (hb : ∀ x y, B ≤ x → x + D ≤ y →
      p * (y - x) - C ≤ logGrowthProfile T y - logGrowthProfile T x) :
    (p : EReal) ≤ strongLowerIndex T := by
  apply le_strongLowerIndex_of_uniform_lower T hT (Real.exp_pos (-C))
    (Real.one_le_exp (le_max_right D 0)) (Real.one_le_exp (le_max_right B 0))
  intro x r hx hr
  have hx0 : 0 < x := (Real.exp_pos (max D 0)).trans_le hx
  have hr0 : 0 < r := (Real.exp_pos (max B 0)).trans_le hr
  have hxlog : D ≤ Real.log x := by
    have hl := Real.log_le_log (Real.exp_pos (max D 0)) hx
    rw [Real.log_exp] at hl
    exact (le_max_left _ _).trans hl
  have hrlog : B ≤ Real.log r := by
    have hl := Real.log_le_log (Real.exp_pos (max B 0)) hr
    rw [Real.log_exp] at hl
    exact (le_max_left _ _).trans hl
  have hs := hb (Real.log r) (Real.log x + Real.log r) hrlog (by linarith)
  simp only [logGrowthProfile, Real.exp_add, Real.exp_log hx0, Real.exp_log hr0] at hs
  have hlog : -C + Real.log x * p + Real.log (T r) ≤ Real.log (T (x * r)) := by
    nlinarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_add, Real.exp_log (hT _ (mul_pos hx0 hr0)),
    Real.exp_log (hT r hr0), ← Real.rpow_def_of_pos hx0 p] at he
  exact he

end
end ModifiedCartan
#print axioms ModifiedCartan.strongUpperIndex_le_of_log_slope
#print axioms ModifiedCartan.le_strongLowerIndex_of_log_slope
