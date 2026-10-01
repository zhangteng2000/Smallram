import ModifiedCartan.UnitaryPowerGradient
import ModifiedCartan.TwoPhaseLocalForm

open scoped Topology BigOperators ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Exact scalar specialization of the constant polynomial in the power chart. -/
theorem ArbitraryRadiusLimitData.scalar_powerChart_polynomial
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) (a x : ℂ) :
    (∑ i : Index 1,
      (d.fullCoefficient i a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ (1 + 1 - i.val)) * x ^ i.val) =
      d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2 := by
  have h0 : d.fullCoefficient 0 = d.coefficient 0 := d.fullCoefficient_castSucc (0 : Fin 1)
  have h1 : d.fullCoefficient 1 = fun _ => 0 := d.fullCoefficient_last
  have hs := Fin.sum_univ_two (fun i : Fin 2 =>
    (d.fullCoefficient i a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ (1 + 1 - i.val)) * x ^ i.val)
  simpa only [Fin.val_zero, Fin.val_one, h0, h1, pow_zero, mul_one, zero_mul,
    add_zero, Nat.add_sub_cancel, Nat.sub_zero] using! hs

/-- The two actual opposite roots for an n=1 component. The root is constructed
using algebraic closedness, and its equation is retained explicitly. -/
theorem ArbitraryRadiusLimitData.unitary_component_powerChart_quadratic
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha4 : ‖a‖ < 4)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ)
    (j : Index 1) {u : ℂ → EReal} {v : ℂ → ℝ}
    (hu : IsSubharmonicOn (ball (0 : ℂ) 4) u)
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hlim : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z)) v) :
    ∃ (b : ℂ) (H : ℂ → ℂ),
      b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) ∧
      IsSubharmonicOn (powerChartDomain a ρ)
        (fun w => ((u (powerChart a ρ w)).toReal : EReal)) ∧
      HasWeakComplexGradient (powerChartDomain a ρ) (fun w => (u (powerChart a ρ w)).toReal) H ∧
      ∀ᵐ w ∂volume.restrict (powerChartDomain a ρ), H w = b ∨ H w = -b := by
  obtain ⟨H, hsub, hH, he⟩ := d.unitary_component_powerChart_gradient_equation hρ ha ha4 hns V j hu hrep hlim
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)) (n := 2) (by norm_num)
  refine ⟨b, H, hb, hsub, hH, ?_⟩
  filter_upwards [he] with w hw
  rw [d.scalar_powerChart_polynomial] at hw
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [hb]
  exact eq_neg_of_add_eq_zero_left hw

/-- Exact local three-form classification of an actual scalar component
limit on its power chart. Context: LaTeX `thm:A`, remaining conclusion (b). -/
theorem ArbitraryRadiusLimitData.unitary_component_powerChart_two_phase
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha4 : ‖a‖ < 4)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ)
    (j : Index 1) {u : ℂ → EReal} {v : ℂ → ℝ}
    (hu : IsSubharmonicOn (ball (0 : ℂ) 4) u)
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hlim : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z)) v) :
    ∃ b : ℂ, b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) ∧
      ∀ c ∈ powerChartDomain a ρ, ∃ s : ℝ, 0 < s ∧ ball c s ⊆ powerChartDomain a ρ ∧
        (EqOn (fun w => (u (powerChart a ρ w)).toReal)
          (fun w => (u (powerChart a ρ c)).toReal + (b * (w - c)).re) (ball c s) ∨
         EqOn (fun w => (u (powerChart a ρ w)).toReal)
          (fun w => (u (powerChart a ρ c)).toReal - (b * (w - c)).re) (ball c s) ∨
         EqOn (fun w => (u (powerChart a ρ w)).toReal)
          (fun w => (u (powerChart a ρ c)).toReal + |(b * (w - c)).re|) (ball c s)) := by
  obtain ⟨b, H, hb, hsub, hH, he⟩ := d.unitary_component_powerChart_quadratic hρ ha ha4 hns V j hu hrep hlim
  refine ⟨b, hb, fun c hc => ?_⟩
  simpa only [EReal.toReal_coe] using
    hsub.locally_two_phase_form (powerChartDomain_isOpen a ρ) EventuallyEq.rfl hH b he hc

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_component_powerChart_quadratic
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_component_powerChart_two_phase

