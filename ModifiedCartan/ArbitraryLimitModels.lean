import ModifiedCartan.ArbitraryCoefficientCompactness
import ModifiedCartan.MeasureDilationCompatibility

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A single coefficient subsequence, with compatible analytic models
at every positive scale and for every epsilon in the manuscript interval. -/
theorem arbitrary_coefficient_limit_scale_models {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∃ ι : ℕ → ℕ, StrictMono ι ∧ ∃ a : Fin n → ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (a i) (ball 0 4) ∧
        LocalMeasureConvergence (ball (0 : ℂ) 4)
          (fun ν z => (((r (ι ν) / characteristic f (r (ι ν))) : ℝ) : ℂ) ^
            (n + 1 - i.val) * canonicalCoefficient n f.coord i.castSucc ((r (ι ν) : ℂ) * z)) (a i)) ∧
      ∀ ε : ℝ, 0 < ε → ε < ρ → ∃ K : ℝ, 0 < K ∧
        ∀ R : ℝ, 0 < R → ∀ i : Fin n, ∃ b : ℂ → ℂ,
          AnalyticOnNhd ℂ b (ball 0 4) ∧ (∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K) ∧
          (fun z : ℂ => a i ((R : ℂ) * z)) =ᶠ[𝓝 0]
            (fun z => ((arbitraryScaleWeight ρ ε R / R : ℝ) : ℂ) ^ (n + 1 - i.val) * b z) := by
  obtain ⟨_, _, hcompact⟩ := arbitrary_coefficient_relative_compactness f hlin htrans hsmall
    hρ (ε := ρ / 2) (by positivity) (by linarith) hl hu hr
  obtain ⟨ι, hι, a, ha⟩ := hcompact 1 zero_lt_one id strictMono_id
  have ha' : ∀ i, AnalyticOnNhd ℂ (a i) (ball 0 4) ∧
      LocalMeasureConvergence (ball (0 : ℂ) 4)
        (fun ν z => (((r (ι ν) / characteristic f (r (ι ν))) : ℝ) : ℂ) ^ (n + 1 - i.val) *
          canonicalCoefficient n f.coord i.castSucc ((r (ι ν) : ℂ) * z)) (a i) := by
    intro i
    refine ⟨(ha i).1, ?_⟩
    simpa only [id_eq, one_mul, arbitraryScaleWeight_one, Complex.ofReal_one] using (ha i).2.1
  refine ⟨ι, hι, a, ha', ?_⟩
  intro ε hε hερ
  obtain ⟨K, hK, hcomp⟩ := arbitrary_coefficient_relative_compactness f hlin htrans hsmall
    hρ hε hερ hl hu hr
  refine ⟨K, hK, ?_⟩
  intro R hR i
  obtain ⟨σ, hσ, b, hb⟩ := hcomp R hR ι hι
  refine ⟨b i, (hb i).1, (hb i).2.2, ?_⟩
  let V : Set ℂ := ball 0 4 ∩ (fun z : ℂ => (R : ℂ) * z) ⁻¹' ball 0 4
  have hV : IsOpen V := isOpen_ball.inter
    (isOpen_ball.preimage (continuous_const.mul continuous_id))
  have hV0 : (0 : ℂ) ∈ V := by
    constructor <;> simp only [mem_preimage, mul_zero, mem_ball, dist_self] <;> norm_num
  have heq := ((ha' i).2.comp hσ.tendsto_atTop).dilation_compatible isOpen_ball hV hR.ne'
    (((arbitraryScaleWeight ρ ε R / R : ℝ) : ℂ) ^ (n + 1 - i.val))
    ((hb i).2.1.mono inter_subset_left)
    (ha' i).1.continuousOn ((hb i).1.continuousOn.mono inter_subset_left)
    (fun _ hz => hz.2) (by
      intro ν z _
      simpa only [Complex.ofReal_mul] using
        arbitrary_rescaling_relation (canonicalCoefficient n f.coord i.castSucc)
          (r := r (ι (σ ν))) (S := characteristic f (r (ι (σ ν))))
          hR (arbitraryScaleWeight_pos ρ ε hR) (n + 1 - i.val) z)
  filter_upwards [hV.mem_nhds hV0] with z hz
  exact heq hz

end ModifiedCartan
#print axioms ModifiedCartan.arbitrary_coefficient_limit_scale_models
