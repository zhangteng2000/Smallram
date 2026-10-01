import ModifiedCartan.MeasureDilation
import ModifiedCartan.MonomialExtension

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The analytic limit on the original disk determines all dilation
models and hence convergence on every compact subset of the plane. -/
theorem global_localMeasureConvergence_of_scale_models
    {F : ℕ → ℂ → ℂ} {a : ℂ → ℂ}
    (ha : AnalyticOnNhd ℂ a univ)
    (hlocal : LocalMeasureConvergence (ball (0 : ℂ) 4) F a)
    (hcompact : ∀ R : ℝ, 0 < R → ∀ ι : ℕ → ℕ, StrictMono ι →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ (B : ℕ → ℂ → ℂ) (b : ℂ → ℂ) (c : ℂ),
        (∀ ν, Measurable (B ν)) ∧ AnalyticOnNhd ℂ b (ball 0 4) ∧
        LocalMeasureConvergence (ball (0 : ℂ) 4) B b ∧
        ∀ ν z, F (ι (σ ν)) ((R : ℂ) * z) = c * B ν z) :
    LocalMeasureConvergence univ F a := by
  intro K hK _
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hlim : LocalMeasureConvergence (ball (0 : ℂ) R) F a := by
    apply localMeasureConvergence_of_subseq
    intro ns hns
    obtain ⟨τ, hτ, hnsτ⟩ := strictMono_subseq_of_tendsto_atTop hns
    obtain ⟨σ, hσ, B, b, c, hBmeas, hb, hB, hrel⟩ := hcompact R hR (ns ∘ τ) hnsτ
    refine ⟨τ ∘ σ, ?_⟩
    let V : Set ℂ := ball 0 4 ∩ (fun z : ℂ => (R : ℂ) * z) ⁻¹' ball 0 4
    have hV : IsOpen V := isOpen_ball.inter
      (isOpen_ball.preimage (continuous_const.mul continuous_id))
    have hV0 : (0 : ℂ) ∈ V := by
      constructor <;> simp only [mem_preimage, mul_zero, mem_ball, dist_self] <;> norm_num
    have heq := ((hlocal.comp hnsτ.tendsto_atTop).comp hσ.tendsto_atTop).dilation_compatible
      isOpen_ball hV hR.ne' c (hB.mono inter_subset_left)
      (ha.continuousOn.mono (subset_univ _)) (hb.continuousOn.mono inter_subset_left)
      (fun _ hz => hz.2) (fun ν z _ => hrel ν z)
    have hgerm : (fun z : ℂ => a ((R : ℂ) * z)) =ᶠ[𝓝 0] (fun z => c * b z) := by
      filter_upwards [hV.mem_nhds hV0] with z hz
      exact heq hz
    have heqfull := entire_dilation_model_eqOn ha hb hgerm
    have hpull := hB.dilate_const_mul isOpen_ball (inv_ne_zero hR.ne') c hBmeas
    have hmap : MapsTo (fun z : ℂ => ((R⁻¹ : ℝ) : ℂ) * z) (ball 0 R) (ball 0 4) := by
      intro z hz
      simp only [mem_ball, dist_zero_right] at hz ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr hR).le]
      have hh : R⁻¹ * ‖z‖ < 1 := by
        rw [inv_mul_eq_div]
        exact (div_lt_one hR).mpr hz
      linarith
    have hcancel (z : ℂ) : (R : ℂ) * (((R⁻¹ : ℝ) : ℂ) * z) = z := by
      rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne'), one_mul]
    intro L hL hLR
    apply (hpull L hL (fun z hz => hmap (hLR hz))).congr
    · intro ν
      filter_upwards [ae_restrict_mem hL.measurableSet] with z _
      simpa only [Function.comp_def, hcancel] using (hrel ν (((R⁻¹ : ℝ) : ℂ) * z)).symm
    · filter_upwards [ae_restrict_mem hL.measurableSet] with z hz
      simpa only [hcancel] using (heqfull (hmap (hLR hz))).symm
  exact hlim K hK hKR

end ModifiedCartan
#print axioms ModifiedCartan.global_localMeasureConvergence_of_scale_models
