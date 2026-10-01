import ModifiedCartan.ScalarPeakDirections
import Mathlib.RingTheory.RootsOfUnity.Complex

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem scalarSectorRotation_one_pow (m j : ℕ) :
    (scalarSectorRotation m 1) ^ j = scalarSectorRotation m j := by
  simp only [scalarSectorRotation, Nat.cast_one, one_mul, circleMap_zero_pow, one_pow]
  congr 1
  ring

theorem scalarSectorRotation_primitive {m : ℕ} (hm : m ≠ 0) :
    IsPrimitiveRoot (scalarSectorRotation m 1) m := by
  have he : scalarSectorRotation m 1 = Complex.exp (2 * Real.pi * Complex.I / m) := by
    simp only [scalarSectorRotation, Nat.cast_one, one_mul, circleMap_zero, Complex.ofReal_one]
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp m hm

theorem scalarSectorRotation_exhaust {m : ℕ} (hm : m ≠ 0) {ζ : ℂ} (hζ : ζ ^ m = 1) :
    ∃ j : Fin m, scalarSectorRotation m j.val = ζ := by
  letI : NeZero m := ⟨hm⟩
  obtain ⟨j, hj, he⟩ := (scalarSectorRotation_primitive hm).eq_pow_of_pow_eq_one hζ
  exact ⟨⟨j, hj⟩, (scalarSectorRotation_one_pow m j).symm.trans he⟩

theorem scalarSectorCenter_exhaust {m : ℕ} (hm : m ≠ 0) {a z : ℂ}
    (ha : a ≠ 0) (hz : z ^ m = a ^ m) :
    ∃ j : Fin m, scalarSectorCenter a m j = z := by
  have hdiv : (z / a) ^ m = 1 := by
    rw [div_pow, hz, div_self (pow_ne_zero m ha)]
  obtain ⟨j, hj⟩ := scalarSectorRotation_exhaust hm hdiv
  refine ⟨j, ?_⟩
  rw [scalarSectorCenter, hj]
  field_simp

/-- The branch-independent quadratic already used in the scalar norm formula. -/
noncomputable def ArbitraryRadiusLimitData.scalarQuadratic
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) (z : ℂ) : ℂ :=
  -(d.coefficient 0 z * (z * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)

theorem ArbitraryRadiusLimitData.scalarQuadratic_eq_monomial
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {k : ℕ} {c : ℂ} (hcoeff : d.coefficient 0 = fun z => c * z ^ k) (z : ℂ) :
    d.scalarQuadratic z = -(c * ((ρ⁻¹ : ℝ) : ℂ) ^ 2) * z ^ (k + 2) := by
  rw [ArbitraryRadiusLimitData.scalarQuadratic, hcoeff]
  dsimp only
  rw [pow_add, mul_pow]
  ring

theorem ArbitraryRadiusLimitData.scalarQuadratic_powerChart
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : ρ ≠ 0) (a : ℂ) {w : ℂ} (hw : w ∈ powerChartDomain a ρ) :
    d.scalarQuadratic (powerChart a ρ w) = d.scalarQuadratic a * w ^ 2 :=
  d.scalar_square_powerChart hρ a hw

/-- All points sharing the peak quadratic value are the explicit peak centers. -/
theorem ArbitraryRadiusLimitData.scalar_peak_root_exhaust
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : ρ ≠ 0) {k : ℕ} {c a z : ℂ} (hc : c ≠ 0)
    (hcoeff : d.coefficient 0 = fun z => c * z ^ k)
    (ha : a ≠ 0) (hz : d.scalarQuadratic z = d.scalarQuadratic a) :
    ∃ j : Fin (k + 2), scalarSectorCenter a (k + 2) j = z := by
  have hC : -(c * ((ρ⁻¹ : ℝ) : ℂ) ^ 2) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hc (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (inv_ne_zero hρ))))
  rw [d.scalarQuadratic_eq_monomial hcoeff z, d.scalarQuadratic_eq_monomial hcoeff a] at hz
  exact scalarSectorCenter_exhaust (by omega) ha (mul_left_cancel₀ hC hz)

end ModifiedCartan
#print axioms ModifiedCartan.scalarSectorRotation_exhaust
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_peak_root_exhaust
