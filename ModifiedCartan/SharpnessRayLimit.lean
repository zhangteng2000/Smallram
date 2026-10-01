import ModifiedCartan.VectorRayGrowth
import ModifiedCartan.RayModeRealization
import ModifiedCartan.ScalarRayGrowthUpper
import ModifiedCartan.RayPhases

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Exact vector growth in ray time. The scalar lower mode is realized inside
this actual prescribed solution system, so no change-of-basis assumption remains. -/
theorem IsSharpnessSystem.ray_log_limit_of_maximal_positive_mode {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1)
    {ρ β : ℝ} (hρ : 0 < ρ) (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k)
    {δ η : ℂ} (hδ : δ ≠ 0) (hη : η ≠ 0) (hphase : δ ^ q = η ^ k)
    (j : Fin q) (hpos : 0 < (raySpectralValues q δ η j).re)
    (hmax : ∀ i : Fin q, (raySpectralValues q δ η i).re ≤ (raySpectralValues q δ η j).re) :
    Tendsto (fun t => Real.log (euclideanNorm (fun l => g l (rayPoint ρ η t))) / t)
      atTop (𝓝 (raySpectralValues q δ η j).re) := by
  obtain ⟨T, hT, X, hd, _hli, hl⟩ :=
    rayCompanion_tail_fundamental_system_exists (by omega : 1 ≤ q) ρ β hδ hη
  obtain ⟨c, d, hd0, hdl⟩ := h.realizes_positive_ray_mode hq hqn hρ
    (lt_of_lt_of_le zero_lt_one hT) hρβ hβ hδ hη hphase (X j) j (hd j) (hl j) hpos
  let f : ℝ → ℂ := fun t => sharpnessCombination g c (rayPoint ρ η t)
  let b := rayDiagonalPower q ρ β + ((n + 1 - q : ℕ) : ℝ) * rayPrimitivePower ρ
  have hn : Tendsto (fun t : ℝ => t ^ (-b) •
      (Complex.exp (-raySpectralValues q δ η j * (t : ℂ)) • f t)) atTop (𝓝 d) := by
    apply hdl.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (powerExpProfile_normalization ht _ _ b).symm
  have hflog := log_norm_div_t_tendsto_of_power_exp_limit hd0 hn
  have hfne : ∀ᶠ t in atTop, f t ≠ 0 := by
    filter_upwards [hn.eventually_ne hd0] with t ht
    intro he
    apply ht
    simp only [he, smul_zero]
  let C : ℝ := 1 + ∑ l, ‖c l‖
  have hC : 0 < C := by dsimp [C]; positivity
  have hb : ∀ᶠ t in atTop, ‖f t‖ ≤ C * euclideanNorm (fun l => g l (rayPoint ρ η t)) := by
    apply Eventually.of_forall
    intro t
    have hh := norm_linearCombination_le c (fun l => g l (rayPoint ρ η t))
      (fun l => (norm_le_pi_norm (fun l => g l (rayPoint ρ η t)) l).trans
        (norm_le_euclideanNorm (fun l => g l (rayPoint ρ η t))))
    change ‖sharpnessCombination g c (rayPoint ρ η t)‖ ≤ _
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (euclideanNorm_nonneg _)
    dsimp [C]
    linarith
  exact vector_log_limit_of_scalar_lower hC
    (Eventually.of_forall (fun t => (h.curve hq hqn).vector_ne_zero (rayPoint ρ η t))) hfne
    (fun l => h.coordinate_ray_upper_rate hq hqn hρ hρβ hβ hδ hη hphase hpos.le hmax l) hb hflog

/-- LaTeX `eq:sharpness-ray-limit`, expressed in the original radius, for every
ray whose explicitly diagonalized spectrum has a positive maximal mode. -/
theorem IsSharpnessSystem.ray_radius_log_limit_of_maximal_positive_mode {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1)
    {ρ β : ℝ} (hρ : 0 < ρ) (hρβ : ρ = 1 + β) (hβ : β * (q : ℝ) = k)
    {δ η : ℂ} (hδ : δ ≠ 0) (hη : η ≠ 0) (hphase : δ ^ q = η ^ k)
    (j : Fin q) (hpos : 0 < (raySpectralValues q δ η j).re)
    (hmax : ∀ i : Fin q, (raySpectralValues q δ η i).re ≤ (raySpectralValues q δ η j).re) :
    Tendsto (fun r : ℝ => Real.log (euclideanNorm (fun l => g l ((r : ℂ) * η))) / r ^ ρ)
      atTop (𝓝 ((raySpectralValues q δ η j).re / ρ)) := by
  have ht := h.ray_log_limit_of_maximal_positive_mode hq hqn hρ hρβ hβ hδ hη hphase j hpos hmax
  have hh := (ht.comp (rayTime_tendsto hρ)).div_const ρ
  change Tendsto (fun r : ℝ => (Real.log (euclideanNorm (fun l =>
    g l (rayPoint ρ η (rayTime ρ r)))) / rayTime ρ r) / ρ)
    atTop (𝓝 ((raySpectralValues q δ η j).re / ρ)) at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold rayPoint
  rw [rayRadius_time hρ hr]
  unfold rayTime
  field_simp

end ModifiedCartan
#print axioms ModifiedCartan.IsSharpnessSystem.ray_log_limit_of_maximal_positive_mode
#print axioms ModifiedCartan.IsSharpnessSystem.ray_radius_log_limit_of_maximal_positive_mode

