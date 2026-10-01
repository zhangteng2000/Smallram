import ModifiedCartan.PointwiseUnitaryBalance
import ModifiedCartan.WeakGradientLocalConstancy

open scoped Topology BigOperators NNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem HasWeakComplexGradient.exists_const_of_ae_zero_continuousOn
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : HasWeakComplexGradient U u g) (hc : ContinuousOn u U)
    (hg : g =ᵐ[volume.restrict U] (fun _ => 0)) :
    ∃ k : ℝ, ∀ x ∈ U, u x = k := by
  have hloc (x : ℂ) (hx : x ∈ U) : u =ᶠ[𝓝 x] (fun _ => u x) := by
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    have hb : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hs : ball x (ε / 4) ⊆ U := (ball_subset_ball (by linarith : ε / 4 ≤ ε)).trans hεU
    have hg0 : ∀ᵐ z ∂volume.restrict U, ‖g z‖ ≤ ((0 : ℝ≥0) : ℝ) := by
      filter_upwards [hg] with z hz
      simp [hz]
    obtain ⟨w, hw, he⟩ := hu.exists_lipschitz_rep_on_ball (by linarith : ε / 4 < ε / 2) hb hg0
    have hp := Measure.eqOn_open_of_ae_eq he isOpen_ball (hc.mono hs) hw.continuous.continuousOn
    filter_upwards [ball_mem_nhds x (by positivity : 0 < ε / 4)] with y hy
    rw [hp hy, hp (mem_ball_self (by positivity : 0 < ε / 4))]
    apply dist_eq_zero.mp
    exact le_antisymm (by simpa using hw.dist_le_mul y x) dist_nonneg
  have hd (x : ℂ) (hx : x ∈ U) : HasFDerivAt u (0 : ℂ →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (u x) x).congr_of_eventuallyEq (hloc x hx)
  exact hU.exists_is_const_of_fderiv_eq_zero hUc
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hd x hx).fderiv)

theorem ArbitraryRadiusLimitData.fullCoefficient_eq_zero_of_order_lt_one
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : ρ < 1) (i : Index n) : d.fullCoefficient i = 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact d.fullCoefficient_last
  · rw [d.fullCoefficient_castSucc]
    rcases d.coefficient_monomial j with ⟨m, hm, _⟩ | ⟨_, hz⟩
    · have hq : (0 : ℝ) < (n + 1 - j.val : ℕ) := Nat.cast_pos.mpr (by omega)
      have hneg : ((n + 1 - j.val : ℕ) : ℝ) * (ρ - 1) < 0 := mul_neg_of_pos_of_neg hq (by linarith)
      rw [hm] at hneg
      exact (not_lt_of_ge (Nat.cast_nonneg m) hneg).elim
    · exact hz

/-- For the formally permitted case rho < 1 all limiting coefficients vanish;
the actual norm limit is zero. This permits the nontrivial conformal case to
use rho >= 1 without strengthening the homogeneity statement. -/
theorem ArbitraryRadiusLimitData.norm_limit_eq_zero_of_order_lt_one
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : ρ < 1) : ∀ z ∈ ball (0 : ℂ) 4, d.U z = 0 := by
  obtain ⟨a, _, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr (by norm_num : (0 : ℝ) < 2))) d.good_centers.full_measure
  obtain ⟨ns, hns, V, u, v, hu, hmax, _, _⟩ := Paper.lem_basis_at_point d a ha
  have hreg (j : Index n) := d.unitary_component_regular hns V j
    (hu j).1 (hu j).2.2.1 (hu j).2.2.2
  have hc (j : Index n) : ∀ z ∈ ball (0 : ℂ) 4, u j z = u j 0 := by
    obtain ⟨g, hg, he⟩ := d.unitary_component_real_gradient hns V j (hu j).2.2.1 (hu j).2.2.2
    have hz : g =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun _ => 0) := by
      filter_upwards [he] with z hz
      have hp : g z ^ (n + 1) = 0 := by
        simpa only [d.fullCoefficient_eq_zero_of_order_lt_one hρ, Pi.zero_apply, zero_mul,
          Finset.sum_const_zero, add_zero] using hz
      exact eq_zero_of_pow_eq_zero hp
    obtain ⟨k, hk⟩ := hg.exists_const_of_ae_zero_continuousOn isOpen_ball
      (convex_ball (0 : ℂ) 4).isPreconnected (hreg j).2.continuousOn hz
    intro z hz
    rw [(hreg j).1 z hz, (hreg j).1 0 (mem_ball_self (by norm_num)), hk z hz,
      hk 0 (mem_ball_self (by norm_num))]
  intro z hz
  calc
    d.U z = Finset.univ.sup (fun j => u j z) := hmax hz
    _ = Finset.univ.sup (fun j => u j 0) := Finset.sup_congr rfl (fun j _ => hc j z hz)
    _ = d.U 0 := (hmax (mem_ball_self (by norm_num))).symm
    _ = 0 := d.origin_zero

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.norm_limit_eq_zero_of_order_lt_one

