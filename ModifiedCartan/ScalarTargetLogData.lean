import ModifiedCartan.ScalarPrescribedUnitaryLimits
import ModifiedCartan.ScalarTargetUnitary
import ModifiedCartan.ArbitraryRadiusReindex

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual fixed-target logarithmic limit data, constructed below from every
arbitrary-radius limit after a subsequence. Auxiliary to LaTeX `thm:A` (b). -/
structure ScalarTargetLogLimitData {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ}
    (d : ArbitraryRadiusLimitData f r ρ) (β : WithTop ℂ) where
  u : ℂ → EReal
  v : ℂ → ℝ
  subharmonic : IsSubharmonicOn (ball (0 : ℂ) 4) u
  representative : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal))
  convergence : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
    (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq ν)))
      (fun z => (polynomialMatrixGauge (d.polynomial ν)
        (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) 0).eval z)) v
  bounds : ∀ z ∈ ball (0 : ℂ) 4,
    -(d.U z).toReal ≤ (u z).toReal ∧ (u z).toReal ≤ (d.U z).toReal

/-- Existence uses the proved arbitrary prescribed unitary basis compactness,
including the Wronskian-derived lower bound for both components. -/
theorem ArbitraryRadiusLimitData.exists_scalar_target_log_limit
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (β : WithTop ℂ) :
    ∃ ns : ℕ → ℕ, ∃ hns : StrictMono ns,
      Nonempty (ScalarTargetLogLimitData (d.reindex ns hns) β) := by
  obtain ⟨ns, hns, u, v, hu, _, hb⟩ :=
    d.scalar_exists_prescribed_unitary_log_limits (fun _ => scalarTargetUnitary β)
  exact ⟨ns, hns, ⟨⟨u 0, v 0, (hu 0).1, (hu 0).2.2.1, (hu 0).2.2.2, hb 0⟩⟩⟩

theorem ScalarTargetLogLimitData.regular
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β) :
    (∀ z ∈ ball (0 : ℂ) 4, e.u z = ((e.u z).toReal : EReal)) ∧
      LocallyLipschitzOn (ball (0 : ℂ) 4) (fun z => (e.u z).toReal) :=
  d.unitary_component_regular (ns := id) strictMono_id (fun _ => scalarTargetUnitary β)
    0 e.subharmonic e.representative e.convergence

theorem ScalarTargetLogLimitData.real_convergence
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β) :
    LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (characteristic f (r (d.subseq ν)))⁻¹ *
        Real.log ‖(polynomialMatrixGauge (d.polynomial ν)
          (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) 0).eval z‖)
      (fun z => (e.u z).toReal) := by
  apply e.convergence.normalizedLog_real.congr_ae (fun _ => EventuallyEq.rfl)
  filter_upwards [e.representative] with z hz
  rw [hz, EReal.toReal_coe]

theorem ScalarTargetLogLimitData.polynomial_ne_zero
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β) (ν : ℕ) :
    polynomialMatrixGauge (d.polynomial ν)
      (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) 0 ≠ 0 := by
  intro hzero
  obtain ⟨z, _, hz⟩ := e.convergence.normalizedLog_nontrivial isOpen_ball
    (nonempty_ball.mpr (by norm_num : (0 : ℝ) < 4)) (d.scale_pos ν)
  rw [hzero, Polynomial.eval_zero] at hz
  exact hz rfl

/-- Reindex actual target data without changing its fixed target or limit. -/
noncomputable def ScalarTargetLogLimitData.reindex
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    {β : WithTop ℂ} (e : ScalarTargetLogLimitData d β)
    (ns : ℕ → ℕ) (hns : StrictMono ns) : ScalarTargetLogLimitData (d.reindex ns hns) β where
  u := e.u
  v := e.v
  subharmonic := e.subharmonic
  representative := e.representative
  convergence := e.convergence.comp_tendsto hns.tendsto_atTop
  bounds := e.bounds

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.exists_scalar_target_log_limit
#print axioms ModifiedCartan.ScalarTargetLogLimitData.real_convergence
#print axioms ModifiedCartan.ScalarTargetLogLimitData.reindex
