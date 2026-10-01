import ModifiedCartan.PeakCoefficientCompactness
import ModifiedCartan.MeasureDilationCompatibility
import ModifiedCartan.PeakRescaling

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Local limits at one peak scale, together with bounded analytic models
at every other positive scale. This realizes the local alternative to the
diagonal entire-limit construction in Step 1 of `prop:indices`. -/
theorem peak_coefficient_limit_scale_models {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {r ε : ℕ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hrpos : ∀ ν, 0 < r ν) (hr : Tendsto r atTop atTop)
    (hεpos : ∀ ν, 0 < ε ν) (hε : Tendsto ε atTop (𝓝 0))
    (hpeak : ∀ ν t, ε ν ≤ t → t ≤ (ε ν)⁻¹ →
      characteristic f (t * r ν) ≤ (1 + ε ν) * t ^ μ * characteristic f (r ν)) :
    ∃ K : ℝ, 0 < K ∧ ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ a : Fin n → ℂ → ℂ,
      ∀ i, AnalyticOnNhd ℂ (a i) (ball 0 4) ∧
        LocalMeasureConvergence (ball (0 : ℂ) 4)
          (fun ν z => (((r (ρ ν) / characteristic f (r (ρ ν))) : ℝ) : ℂ) ^ (n + 1 - i.val) *
            canonicalCoefficient n f.coord i.castSucc ((r (ρ ν) : ℂ) * z)) (a i) ∧
        ∀ R : ℝ, 0 < R → ∃ b : ℂ → ℂ, AnalyticOnNhd ℂ b (ball 0 4) ∧
          (∀ z ∈ ball (0 : ℂ) 1, ‖b z‖ ≤ K) ∧
          (fun z : ℂ => a i ((R : ℂ) * z)) =ᶠ[𝓝 0]
            (fun z => (R ^ (((n + 1 - i.val : ℕ) : ℝ) * (μ - 1)) : ℝ) * b z) := by
  obtain ⟨K, hK, hcompact⟩ := peak_coefficient_relative_compactness f hlin htrans hsmall
    hμ hrpos hr hεpos hε hpeak
  obtain ⟨ρ, hρ, a, ha⟩ := hcompact 1 zero_lt_one id strictMono_id
  have ha' : ∀ i, AnalyticOnNhd ℂ (a i) (ball 0 4) ∧
      LocalMeasureConvergence (ball (0 : ℂ) 4)
        (fun ν z => (((r (ρ ν) / characteristic f (r (ρ ν))) : ℝ) : ℂ) ^ (n + 1 - i.val) *
          canonicalCoefficient n f.coord i.castSucc ((r (ρ ν) : ℂ) * z)) (a i) := by
    intro i
    refine ⟨(ha i).1, ?_⟩
    simpa only [id_eq, one_mul, Real.one_rpow, Complex.ofReal_one] using (ha i).2.1
  refine ⟨K, hK, ρ, hρ, a, ?_⟩
  intro i
  refine ⟨(ha' i).1, (ha' i).2, ?_⟩
  intro R hR
  obtain ⟨σ, hσ, b, hb⟩ := hcompact R hR ρ hρ
  refine ⟨b i, (hb i).1, (hb i).2.2, ?_⟩
  let V : Set ℂ := ball 0 4 ∩ (fun z : ℂ => (R : ℂ) * z) ⁻¹' ball 0 4
  have hV : IsOpen V := isOpen_ball.inter
    (isOpen_ball.preimage (continuous_const.mul continuous_id))
  have hV0 : (0 : ℂ) ∈ V := by
    constructor <;> simp only [mem_preimage, mul_zero, mem_ball, dist_self] <;> norm_num
  have heq := ((ha' i).2.comp hσ.tendsto_atTop).dilation_compatible isOpen_ball hV hR.ne'
    (((R ^ (((n + 1 - i.val : ℕ) : ℝ) * (μ - 1)) : ℝ) : ℂ))
    ((hb i).2.1.mono inter_subset_left)
    (ha' i).1.continuousOn ((hb i).1.continuousOn.mono inter_subset_left)
    (fun _ hz => hz.2) (by
      intro ν z _
      simpa only [Complex.ofReal_mul] using
        peak_rescaling_relation (canonicalCoefficient n f.coord i.castSucc)
          (r := r (ρ (σ ν))) (S := characteristic f (r (ρ (σ ν)))) (μ := μ)
          hR (n + 1 - i.val) z)
  filter_upwards [hV.mem_nhds hV0] with z hz
  exact heq hz

end
end ModifiedCartan
#print axioms ModifiedCartan.peak_coefficient_limit_scale_models
