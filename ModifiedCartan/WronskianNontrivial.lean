import ModifiedCartan.CanonicalGauge

open scoped BigOperators Topology
open Filter Set

namespace ModifiedCartan

theorem wronskian_congr_nhds {n : ℕ} {g h : Index n → ℂ → ℂ} {z : ℂ}
    (he : ∀ j, g j =ᶠ[𝓝 z] h j) :
    FewInflection.wronskian n g z = FewInflection.wronskian n h z := by
  unfold FewInflection.wronskian
  congr 1
  funext i j
  exact Filter.EventuallyEq.iteratedDeriv_eq i (he j)

theorem wronskian_cons_one {n : ℕ} (h : Index n → ℂ → ℂ) (z : ℂ) :
    FewInflection.wronskian (n + 1) (Fin.cons (fun _ => 1) h) z =
      FewInflection.wronskian n (fun j => deriv (h j)) z := by
  let H : Index (n + 1) → ℂ → ℂ := Fin.cons (fun _ => 1) h
  let M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
    fun i j => iteratedDeriv (i : ℕ) (H j) z
  change M.det = _
  rw [Matrix.det_succ_column_zero M, Fin.sum_univ_succ]
  simp only [M, H, Fin.val_zero, pow_zero, Fin.cons_zero, one_mul,
    Matrix.submatrix, Fin.succAbove_zero, Fin.cons_succ, Fin.val_succ,
    iteratedDeriv_const, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, ite_true,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simp only [iteratedDeriv_succ', FewInflection.wronskian]
  rfl

theorem wronskian_quotient_deriv {n : ℕ} {g : Index (n + 1) → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (h0 : g 0 z ≠ 0) :
    FewInflection.wronskian (n + 1) g z = g 0 z ^ (n + 2) *
      FewInflection.wronskian n (fun j => deriv (fun w => g j.succ w / g 0 w)) z := by
  let h : Index n → ℂ → ℂ := fun j w => g j.succ w / g 0 w
  let H : Index (n + 1) → ℂ → ℂ := Fin.cons (fun _ => 1) h
  have hH : ∀ j, AnalyticAt ℂ (H j) z := by
    intro j
    refine Fin.cases analyticAt_const (fun k => ?_) j
    exact (hg k.succ).fun_div (hg 0) h0
  have he : ∀ j, g j =ᶠ[𝓝 z] (fun w => g 0 w * H j w) := by
    intro j
    filter_upwards [(hg 0).continuousAt.eventually_ne h0] with w hw
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [H]
    · change g k.succ w = g 0 w * (g k.succ w / g 0 w)
      field_simp
  rw [wronskian_congr_nhds he, FewInflection.wronskian_scalar_mul (g 0) H z
    (hg 0).contDiffAt (fun j => (hH j).contDiffAt), wronskian_cons_one]

theorem lift_quotient_derivative_relation {n : ℕ} {U V : Set ℂ} {a : ℂ}
    (hUc : IsConnected U) (hV : IsOpen V) (hVc : IsPreconnected V)
    (hVU : V ⊆ U) (ha : a ∈ V) {g : Index (n + 1) → ℂ → ℂ}
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) (h0 : ∀ z ∈ V, g 0 z ≠ 0)
    {c : Index n → ℂ} (hc : c ≠ 0)
    (hrel : ∀ z ∈ V, ∑ j, c j * deriv (fun w => g j.succ w / g 0 w) z = 0) :
    ∃ b : Index (n + 1) → ℂ, b ≠ 0 ∧ ∀ z ∈ U, ∑ j, b j * g j z = 0 := by
  let q : Index n → ℂ → ℂ := fun j z => g j.succ z / g 0 z
  have hq : ∀ j, AnalyticOnNhd ℂ (q j) V :=
    fun j z hz => (hg j.succ z (hVU hz)).fun_div (hg 0 z (hVU hz)) (h0 z hz)
  let F : ℂ → ℂ := fun z => ∑ j, c j * q j z
  have hF : AnalyticOnNhd ℂ F V := by
    intro z hz
    apply Finset.analyticAt_fun_sum
    intro j _
    exact analyticAt_const.fun_mul (hq j z hz)
  have hF' : ∀ z ∈ V, deriv F z = 0 := by
    intro z hz
    change deriv (fun w => ∑ j, c j * q j w) z = 0
    rw [deriv_fun_sum (fun j _ =>
      (analyticAt_const.fun_mul (hq j z hz)).differentiableAt)]
    simp only [deriv_const_mul_field]
    exact hrel z hz
  have hconst : EqOn F (fun _ => F a) V := by
    apply hV.eqOn_of_deriv_eq hVc hF.differentiableOn (differentiableOn_const (F a))
      _ ha rfl
    intro z hz
    simp only [hF' z hz, deriv_const]
  let b : Index (n + 1) → ℂ := Fin.cons (-F a) c
  have hb : b ≠ 0 := by
    intro hb0
    apply hc
    funext j
    have hh := congrFun hb0 j.succ
    exact hh
  have hlocal : ∀ z ∈ V, ∑ j, b j * g j z = 0 := by
    intro z hz
    have hsum : (∑ j : Index n, c j * g j.succ z) = g 0 z * F z := by
      dsimp [F]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [q]
      field_simp [h0 z hz]
    rw [Fin.sum_univ_succ]
    change -F a * g 0 z + (∑ j : Index n, c j * g j.succ z) = 0
    rw [hsum, hconst hz]
    ring
  have hB : AnalyticOnNhd ℂ (fun z => ∑ j, b j * g j z) U := by
    intro z hz
    apply Finset.analyticAt_fun_sum
    intro j _
    exact analyticAt_const.fun_mul (hg j z hz)
  have he : (fun z => ∑ j, b j * g j z) =ᶠ[𝓝 a] 0 := by
    filter_upwards [hV.mem_nhds ha] with z hz
    exact hlocal z hz
  exact ⟨b, hb, fun z hz =>
    hB.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc.isPreconnected (hVU ha) he hz⟩

theorem linear_relation_of_wronskian_eq_zero {n : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsConnected U) {g : Index n → ℂ → ℂ}
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (hW : ∀ z ∈ U, FewInflection.wronskian n g z = 0) :
    ∃ c : Index n → ℂ, c ≠ 0 ∧ ∀ z ∈ U, ∑ j, c j * g j z = 0 := by
  induction n generalizing U with
  | zero =>
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro hc
      have hh := congrFun hc 0
      simp at hh
    · intro z hz
      let M : Matrix (Fin 1) (Fin 1) ℂ := fun _ j => g j z
      have hh : M.det = 0 := hW z hz
      have hz0 : g 0 z = 0 := (Matrix.det_fin_one M).symm.trans hh
      simpa [Index, FewInflection.Index] using hz0
  | succ n ih =>
    by_cases hzero : ∀ z ∈ U, g 0 z = 0
    · refine ⟨Fin.cons 1 (fun _ => 0), ?_, ?_⟩
      · intro hc
        have hh := congrFun hc 0
        simp at hh
      · intro z hz
        rw [Fin.sum_univ_succ]
        simp [hzero z hz]
    push Not at hzero
    obtain ⟨a, ha, hga0⟩ := hzero
    have he : ∀ᶠ z in 𝓝 a, z ∈ U ∧ g 0 z ≠ 0 := by
      filter_upwards [hU.mem_nhds ha, (hg 0 a ha).continuousAt.eventually_ne hga0] with z hz h0
      exact ⟨hz, h0⟩
    obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp he
    have haV : a ∈ Metric.ball a r := Metric.mem_ball_self hr
    have hVU : Metric.ball a r ⊆ U := fun z hz => (hb z hz).1
    have h0 : ∀ z ∈ Metric.ball a r, g 0 z ≠ 0 := fun z hz => (hb z hz).2
    have hVc : IsConnected (Metric.ball a r) :=
      ⟨⟨a, haV⟩, (convex_ball a r).isPreconnected⟩
    let q : Index n → ℂ → ℂ := fun j w => g j.succ w / g 0 w
    have hq : ∀ j, AnalyticOnNhd ℂ (q j) (Metric.ball a r) :=
      fun j z hz => (hg j.succ z (hVU hz)).fun_div (hg 0 z (hVU hz)) (h0 z hz)
    have hqd : ∀ j, AnalyticOnNhd ℂ (deriv (q j)) (Metric.ball a r) :=
      fun j z hz => (hq j z hz).deriv
    have hWq : ∀ z ∈ Metric.ball a r, FewInflection.wronskian n (fun j => deriv (q j)) z = 0 := by
      intro z hz
      have hh := wronskian_quotient_deriv (fun j => hg j z (hVU hz)) (h0 z hz)
      rw [hW z (hVU hz)] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ (h0 z hz))
    obtain ⟨c, hc, hrel⟩ := ih Metric.isOpen_ball hVc hqd hWq
    exact lift_quotient_derivative_relation hUc Metric.isOpen_ball hVc.isPreconnected
      hVU haV hg h0 hc hrel

theorem exists_wronskian_ne_zero_of_linearIndependent {n : ℕ} {g : Index n → ℂ → ℂ}
    (hg : ∀ j, Differentiable ℂ (g j)) (hlin : LinearIndependent ℂ g) :
    ∃ z, FewInflection.wronskian n g z ≠ 0 := by
  by_contra hnone
  push Not at hnone
  obtain ⟨c, hc, hrel⟩ := linear_relation_of_wronskian_eq_zero isOpen_univ isConnected_univ
    (fun j => Complex.analyticOnNhd_univ_iff_differentiable.mpr (hg j))
    (fun z _ => hnone z)
  apply hc
  have hsum : ∑ j, c j • g j = 0 := by
    funext z
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      hrel z (mem_univ z)
  exact funext (Fintype.linearIndependent_iff.mp hlin c hsum)

/-- Background fact required before applying the paper's operator construction
to a linearly nondegenerate curve; no Wronskian hypothesis is added to the curve. -/
theorem curve_wronskian_nontrivial {n : ℕ} (f : Curve n) (hlin : f.linearlyNonDegenerate) :
    ∃ z, FewInflection.wronskian n f.coord z ≠ 0 :=
  exists_wronskian_ne_zero_of_linearIndependent f.holomorphic hlin

end ModifiedCartan

