import ModifiedCartan.JetLogCompactness

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Cauchy's estimate and upper semicontinuity give the reverse point
inequality in Step 2 of `lem:basis-at-point`. -/
theorem jet_exponent_le_log_limit_value {n : ℕ} {s : ℕ → ℝ} {f : ℕ → ℂ → ℂ}
    {a : ℂ} {ell : ℝ} {u : ℂ → EReal} {v : ℂ → ℝ}
    (ha : a ∈ ball (0 : ℂ) 4) (hspos : ∀ ν, 0 < s ν) (hs : Tendsto s atTop atTop)
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) (ball 0 4))
    (hnz : ∀ ν, ∃ z ∈ ball (0 : ℂ) 4, f ν z ≠ 0)
    (hu : IsSubharmonicOn (ball (0 : ℂ) 4) u)
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hconv : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (s ν) (f ν)) v)
    (hj : ∀ᶠ ν in atTop, 0 < scaledJetLength n (s ν) (f ν) a)
    (hlim : Tendsto (fun ν => Real.log (scaledJetLength n (s ν) (f ν) a) / s ν)
      atTop (𝓝 ell)) : (ell : EReal) ≤ u a := by
  by_contra hn
  obtain ⟨M, huM, hMl⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hMell : M < ell := EReal.coe_lt_coe_iff.mp hMl
  let ε : ℝ := (ell - M) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : M + 2 * ε < ell := by dsimp [ε]; linarith
  have hevent : ∀ᶠ z in 𝓝 a, u z < (M : EReal) := by
    simpa only [isOpen_ball.nhdsWithin_eq ha] using hu.upperSemicontinuousOn a ha (M : EReal) huM
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hevent (isOpen_ball.mem_nhds ha))
  have hhalf : 0 < R / 2 := half_pos hR
  have hquarter : 0 < R / 4 := by positivity
  have hclosed : closedBall a (R / 2) ⊆ ball (0 : ℂ) 4 :=
    ((closedBall_subset_ball (half_lt_self hR)).trans hRsub).trans inter_subset_right
  have hV : closure (ball a (R / 2)) ⊆ ball (0 : ℂ) 4 := by
    rw [closure_ball a hhalf.ne']
    exact hclosed
  have hreal : ∀ᵐ z ∂volume.restrict (ball a (R / 2)), v z ≤ M := by
    filter_upwards [hrep.filter_mono (ae_mono (Measure.restrict_mono_set _
      (ball_subset_closedBall.trans hclosed))), ae_restrict_mem measurableSet_ball] with z hz hzD
    have he : u z < (M : EReal) := (hRsub ((ball_subset_ball (half_le_self hR.le)) hzD)).1
    rw [hz] at he
    exact (EReal.coe_lt_coe_iff.mp he).le
  have hsub (ν : ℕ) := normalizedExtendedLog_isSubharmonicOn isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected (hf ν) (hnz ν) (hspos ν)
  have hupper := subharmonic_eventually_upper_bound hsub hconv.real_convergence
    (isCompact_closedBall a (R / 4)) (V := ball a (R / 2)) isOpen_ball
    (by rw [closure_ball a hhalf.ne']; exact isCompact_closedBall _ _)
    (closedBall_subset_ball (by linarith : R / 4 < R / 2)) hV hreal hε
  have hK := jetCauchyConstant_pos n hquarter
  have hKsub : closedBall a (R / 4) ⊆ ball (0 : ℂ) 4 :=
    (closedBall_subset_closedBall (by linarith : R / 4 ≤ R / 2)).trans hclosed
  have hfalse : ∀ᶠ ν : ℕ in atTop, False := by
    filter_upwards [hupper, hs.eventually_ge_atTop 1, hj,
      hs.eventually_ge_atTop (Real.log (jetCauchyConstant n (R / 4)) / ε),
      hlim.eventually (lt_mem_nhds hgap)] with ν hν hsν hjν hsK hlogν
    have hfn : ∀ z ∈ sphere a (R / 4), ‖f ν z‖ ≤ Real.exp ((M + ε) * s ν) := by
      intro z hz
      exact (normalizedExtendedLog_le_iff_norm_le_exp (hspos ν) (f ν) z (M + ε)).mp
        (hν z (sphere_subset_closedBall hz))
    have hjet := scaledJetLength_le_of_sphere_bound (n := n) hsν hquarter (Real.exp_pos _).le
      ((hf ν).differentiableOn.diffContOnCl_ball hKsub) hfn
    have hsmall : jetCauchyConstant n (R / 4) * Real.exp ((M + ε) * s ν) ≤
        Real.exp ((M + 2 * ε) * s ν) := by
      rw [← Real.exp_log hK, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := (div_le_iff₀ hε).mp hsK
      nlinarith
    have hh := Real.log_le_log hjν (hjet.trans hsmall)
    rw [Real.log_exp] at hh
    exact (not_lt_of_ge ((div_le_iff₀ (hspos ν)).mpr hh) hlogν)
  exact hfalse.exists.elim (fun _ h => h)

end ModifiedCartan
#print axioms ModifiedCartan.jet_exponent_le_log_limit_value
