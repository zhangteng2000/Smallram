import ModifiedCartan.UniformLipschitzCompactness
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue

open scoped Topology ENNReal NNReal BoundedContinuousFunction
open Filter MeasureTheory Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Arzela--Ascoli for a sequence that is Lipschitz only on the compact
set under consideration. The target may be a finite tuple of complex numbers. -/
theorem exists_uniformly_convergent_subsequence_of_lipschitzOn
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {K : Set ℂ} (hK : IsCompact K) {F : ℕ → ℂ → E} {L : ℝ≥0}
    (hL : ∀ n, LipschitzOnWith L (F n) K) {B : ℝ}
    (hB : ∀ n x, x ∈ K → ‖F n x‖ ≤ B) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : ℂ → E,
      TendstoUniformlyOn (fun n => F (ns n)) g atTop K := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G : ℕ → (K →ᵇ E) := fun n =>
    { toFun := fun x => F n x
      continuous_toFun := (hL n).to_restrict.continuous
      map_bounded' := ⟨2 * B, fun x y => by
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans ((add_le_add (hB n x x.property) (hB n y y.property)).trans
          (by linarith))⟩ }
  have hequi : Equicontinuous ((↑) : range G → K → E) := by
    apply equicontinuous_of_continuity_modulus (fun t : ℝ => (L : ℝ) * t)
      (by simpa only [mul_zero, id_eq] using ((tendsto_id : Tendsto (fun t : ℝ => t)
        (𝓝 0) (𝓝 0)).const_mul (L : ℝ)))
    intro x y g
    obtain ⟨n, hn⟩ := g.property
    have heq : (g : K →ᵇ E) = G n := hn.symm
    change dist ((g : K →ᵇ E) x) ((g : K →ᵇ E) y) ≤ (L : ℝ) * dist x y
    rw [heq]
    exact (hL n).dist_le_mul x x.property y y.property
  have hcompact := BoundedContinuousFunction.arzela_ascoli (closedBall (0 : E) B)
    (isCompact_closedBall 0 B) (range G) (fun f x hf => by
      obtain ⟨n, rfl⟩ := hf
      rw [mem_closedBall, dist_zero_right]
      exact hB n x x.property) hequi
  obtain ⟨g, _, ns, hns, hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  let g' : ℂ → E := fun z => if hz : z ∈ K then g ⟨z, hz⟩ else 0
  refine ⟨ns, hns, g', ?_⟩
  have huni := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp huni ε hε] with n hn z hz
  have hnz := hn (⟨z, hz⟩ : K)
  change dist (g ⟨z, hz⟩) (F (ns n) z) < ε at hnz
  simpa only [g', dite_eq_left hz] using hnz

theorem holomorphic_deriv_bound_on_inner_disk {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {B : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 8))
    (hB : ∀ z ∈ ball (0 : ℂ) 6, ‖f z‖ ≤ B) {z : ℂ} (hz : z ∈ closedBall 0 5) :
    ‖deriv f z‖ ≤ 2 * B := by
  have hsub : closedBall z (1 / 2 : ℝ) ⊆ ball (0 : ℂ) 6 := by
    intro w hw
    have hw' : ‖w - z‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hz' : ‖z‖ ≤ 5 := by simpa only [mem_closedBall, dist_zero_right] using hz
    have ht : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa only [sub_add_cancel] using norm_add_le (w - z) z
    rw [mem_ball, dist_zero_right]
    linarith
  have he := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 2)
    (hf.diffContOnCl_ball (hsub.trans (ball_subset_ball (by norm_num : (6 : ℝ) ≤ 8))))
    (fun w hw => hB w (hsub (sphere_subset_closedBall hw)))
  convert! he using 1
  ring

theorem holomorphic_lipschitzOn_inner_disk {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {B : ℝ}
    (hB0 : 0 ≤ B) (hf : DifferentiableOn ℂ f (ball 0 8))
    (hB : ∀ z ∈ ball (0 : ℂ) 6, ‖f z‖ ≤ B) :
    LipschitzOnWith ⟨2 * B, by positivity⟩ f (closedBall 0 5) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℂ)
  · intro z hz
    apply hf.differentiableAt
    exact isOpen_ball.mem_nhds ((closedBall_subset_ball (by norm_num : (5 : ℝ) < 8)) hz)
  · intro z hz
    exact holomorphic_deriv_bound_on_inner_disk hf hB hz
  · exact convex_closedBall 0 5

/-- A bounded holomorphic sequence has a common uniformly convergent
subsequence on the smaller closed disk. Applied to a finite complex tuple,
this gives simultaneous coefficient compactness in `prop:localcompact`. -/
theorem exists_holomorphic_uniform_limit_on_inner_disk {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {F : ℕ → ℂ → E} {B : ℝ} (hB0 : 0 ≤ B)
    (hF : ∀ ν, DifferentiableOn ℂ (F ν) (ball 0 8))
    (hB : ∀ ν z, z ∈ ball (0 : ℂ) 6 → ‖F ν z‖ ≤ B) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : ℂ → E,
      AnalyticOnNhd ℂ g (ball 0 5) ∧
      TendstoUniformlyOn (fun ν => F (ns ν)) g atTop (closedBall 0 5) ∧
      ∀ z ∈ closedBall (0 : ℂ) 5, ‖g z‖ ≤ B := by
  have hsub : closedBall (0 : ℂ) 5 ⊆ ball 0 6 :=
    closedBall_subset_ball (by norm_num)
  obtain ⟨ns, hns, g, hconv⟩ := exists_uniformly_convergent_subsequence_of_lipschitzOn
    (isCompact_closedBall (0 : ℂ) 5)
    (fun ν => holomorphic_lipschitzOn_inner_disk hB0 (hF ν) (hB ν))
    (fun ν z hz => hB ν z (hsub hz))
  refine ⟨ns, hns, g, ?_, hconv, ?_⟩
  · apply DifferentiableOn.analyticOnNhd _ isOpen_ball
    apply ((hconv.mono ball_subset_closedBall).tendstoLocallyUniformlyOn).differentiableOn
    · exact Eventually.of_forall (fun ν => (hF (ns ν)).mono
        (ball_subset_ball (by norm_num : (5 : ℝ) ≤ 8)))
    · exact isOpen_ball
  · intro z hz
    exact le_of_tendsto' (hconv.tendsto_at hz).norm (fun ν => hB (ns ν) z (hsub hz))

theorem exists_holomorphic_uniform_limit_of_eventually_bounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {F : ℕ → ℂ → E} {B : ℝ} (hB0 : 0 ≤ B)
    (hF : ∀ ν, DifferentiableOn ℂ (F ν) (ball 0 8))
    (hB : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 6, ‖F ν z‖ ≤ B) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : ℂ → E,
      AnalyticOnNhd ℂ g (ball 0 5) ∧
      TendstoUniformlyOn (fun ν => F (ns ν)) g atTop (closedBall 0 5) ∧
      ∀ z ∈ closedBall (0 : ℂ) 5, ‖g z‖ ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hB
  obtain ⟨ns, hns, g, hg, hc, hb⟩ := exists_holomorphic_uniform_limit_on_inner_disk
    hB0 (fun ν => hF (ν + N)) (fun ν => hN (ν + N) (by omega))
  refine ⟨fun ν => ns ν + N, ?_, g, hg, hc, hb⟩
  intro i j hij
  have := hns hij
  dsimp only
  omega

theorem exists_simultaneous_holomorphic_uniform_limits {ι : Type*} [Fintype ι]
    {F : ℕ → ι → ℂ → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hF : ∀ ν i, AnalyticOnNhd ℂ (F ν i) (ball 0 8))
    (hB : ∀ᶠ ν in atTop, ∀ i z, z ∈ ball (0 : ℂ) 6 → ‖F ν i z‖ ≤ B) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : ι → ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (g i) (ball 0 5)) ∧
      (∀ i, TendstoUniformlyOn (fun ν => F (ns ν) i) (g i) atTop (closedBall 0 5)) ∧
      ∀ i z, z ∈ closedBall (0 : ℂ) 5 → ‖g i z‖ ≤ B := by
  let G := fun ν z i => F ν i z
  have hG (ν : ℕ) : DifferentiableOn ℂ (G ν) (ball 0 8) :=
    differentiableOn_pi.mpr (fun i => (hF ν i).differentiableOn)
  have hGb : ∀ᶠ ν in atTop, ∀ z ∈ ball (0 : ℂ) 6, ‖G ν z‖ ≤ B := by
    filter_upwards [hB] with ν hν z hz
    exact (pi_norm_le_iff_of_nonneg hB0).mpr (fun i => hν i z hz)
  obtain ⟨ns, hns, g, hg, hc, hb⟩ :=
    exists_holomorphic_uniform_limit_of_eventually_bounded hB0 hG hGb
  refine ⟨ns, hns, fun i z => g z i, ?_, ?_, ?_⟩
  · exact analyticOnNhd_pi_iff.mp hg
  · intro i
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc ε hε] with ν hν z hz
    have he := hν z hz
    rw [dist_eq_norm] at he ⊢
    exact (norm_le_pi_norm (g z - G (ns ν) z) i).trans_lt he
  · intro i z hz
    exact (norm_le_pi_norm (g z) i).trans (hb z hz)

end ModifiedCartan
#print axioms ModifiedCartan.exists_uniformly_convergent_subsequence_of_lipschitzOn
#print axioms ModifiedCartan.holomorphic_deriv_bound_on_inner_disk
#print axioms ModifiedCartan.exists_holomorphic_uniform_limit_on_inner_disk
#print axioms ModifiedCartan.exists_simultaneous_holomorphic_uniform_limits
