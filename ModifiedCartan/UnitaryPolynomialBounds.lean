import ModifiedCartan.PointJetUpper

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The component bound retained after the actual unitary changes.
It is uniform in the sequence of unitary matrices. -/
theorem unitary_polynomial_coordinate_eventual_bound {n : ℕ} {s : ℕ → ℝ}
    {p : ℕ → Index n → Polynomial ℂ} {C : ℝ}
    (hs : Tendsto s atTop atTop)
    (hb : ∀ᶠ ν in atTop, ∀ j z, z ∈ ball (0 : ℂ) 4 → ‖(p ν j).eval z‖ ≤ Real.exp (C * s ν))
    (V : ℕ → Matrix.unitaryGroup (Index n) ℂ) :
    ∀ᶠ ν in atTop, ∀ j z, z ∈ ball (0 : ℂ) 4 →
      ‖(polynomialMatrixGauge (p ν) (V ν : Matrix (Index n) (Index n) ℂ) j).eval z‖ ≤
        Real.exp ((C + 1) * s ν) := by
  have hcard : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  filter_upwards [hb, hs.eventually_ge_atTop (Real.log (Real.sqrt (n + 1)))]
    with ν hbν hss j z hz
  have hh := (norm_le_pi_norm
    (fun k => (polynomialMatrixGauge (p ν) (V ν : Matrix (Index n) (Index n) ℂ) k).eval z) j).trans
      (norm_le_euclideanNorm _)
  rw [polynomialMatrixGauge_unitary_norm] at hh
  have hn : ‖(fun k => (p ν k).eval z)‖ ≤ Real.exp (C * s ν) :=
    (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr (fun k => hbν k z hz)
  exact hh.trans ((euclideanNorm_le _).trans ((mul_le_mul_of_nonneg_left hn hcard.le).trans
    (constant_mul_exp_le_exp hcard hss)))

theorem ereal_coe_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ S, f i : ℝ) : EReal) = ∑ i ∈ S, (f i : EReal) := by
  exact map_sum (⟨⟨((↑) : ℝ → EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f S

end ModifiedCartan
#print axioms ModifiedCartan.unitary_polynomial_coordinate_eventual_bound
