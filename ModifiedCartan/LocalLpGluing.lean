import ModifiedCartan.UniformLocalLp

open scoped Topology ENNReal ContDiff
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Local convergence on neighborhoods implies convergence on every compact
subset, supporting `lem:logderivlimit`. A finite ball cover bounds the integral
of the p-th norm power; no uniform bound on the whole domain is assumed. -/

theorem tendsto_eLpNorm_of_finite_cover {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] {f : ℕ → ℂ → E}
    {K : Set ℂ} {V : ι → Set ℂ} (hcover : K ⊆ ⋃ i, V i)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hlim : ∀ i, Tendsto (fun n => eLpNorm (f n) p (volume.restrict (V i))) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) p (volume.restrict K)) atTop (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpower (n : ℕ) (i : ι) :
      (∫⁻ z in V i, ‖f n z‖ₑ ^ p.toReal) = eLpNorm (f n) p (volume.restrict (V i)) ^ p.toReal := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hp, eLpNorm_eq_eLpNorm' hp0 hpt]
  have ht (i : ι) : Tendsto (fun n => ∫⁻ z in V i, ‖f n z‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hpower, ENNReal.zero_rpow_of_pos hp] using
      ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto (0 : ℝ≥0∞)).comp (hlim i)
  have hsum : Tendsto (fun n => ∑ i, ∫⁻ z in V i, ‖f n z‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => ht i)
  have hbound : Tendsto (fun n => (∑ i, ∫⁻ z in V i, ‖f n z‖ₑ ^ p.toReal) ^ (1 / p.toReal))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] using
      ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto (0 : ℝ≥0∞)).comp hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun _ => bot_le)
  intro n
  dsimp only
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  calc
    _ ≤ ∫⁻ z in ⋃ i, V i, ‖f n z‖ₑ ^ p.toReal := lintegral_mono_set hcover
    _ ≤ _ := by simpa only [tsum_fintype] using lintegral_iUnion_le V (fun z => ‖f n z‖ₑ ^ p.toReal)

theorem localLpConvergence_of_locally {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {U : Set ℂ}
    {f : ℕ → ℂ → E} {g : ℂ → E}
    (hf : ∀ K, IsCompact K → K ⊆ U → ∀ n, MemLp (f n) p (volume.restrict K))
    (hg : ∀ K, IsCompact K → K ⊆ U → MemLp g p (volume.restrict K))
    (hlocal : ∀ x ∈ U, ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ LocalLpConvergence p V f g) :
    LocalLpConvergence p U f g := by
  classical
  refine ⟨hf, hg, ?_⟩
  intro K hK hKU
  have hsmall (x : K) : ∃ r > 0, Tendsto
      (fun n => eLpNorm (f n - g) p (volume.restrict (closedBall (x : ℂ) r))) atTop (𝓝 0) := by
    obtain ⟨V, hV, hxV, hlim⟩ := hlocal x (hKU x.2)
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV x hxV
    exact ⟨ε / 2, half_pos hε, hlim.tendsto _ (isCompact_closedBall _ _)
      ((closedBall_subset_ball (half_lt_self hε)).trans hεV)⟩
  choose r hr hlim using hsmall
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℂ) (r x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩)
  have hcover : K ⊆ ⋃ i : S, closedBall ((i : K) : ℂ) (r i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hS hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, ball_subset_closedBall hxi⟩
  exact tendsto_eLpNorm_of_finite_cover hcover hp0 hpt (fun i : S => hlim i)



end ModifiedCartan


