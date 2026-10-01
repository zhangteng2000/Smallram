import ModifiedCartan.RayPowerClock

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def powerExpWeight (a b t : ℝ) : ℝ := t ^ b * Real.exp (a * t)
noncomputable def powerExpProfile (lam : ℂ) (b t : ℝ) : ℂ :=
  ((t ^ b : ℝ) : ℂ) * Complex.exp (lam * (t : ℂ))

theorem powerExpWeight_pos {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    0 < powerExpWeight a b t := mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)

theorem powerExpWeight_hasDerivAt {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    HasDerivAt (powerExpWeight a b) ((a + b / t) * powerExpWeight a b t) t := by
  have hd := (Real.hasDerivAt_rpow_const (p := b) (Or.inl ht.ne')).mul
    (((hasDerivAt_id t).const_mul a).exp)
  apply hd.congr_deriv
  rw [Real.rpow_sub_one ht.ne']
  dsimp [powerExpWeight]
  ring

theorem powerExpWeight_tendsto {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (powerExpWeight a b) atTop atTop := by
  apply (tendsto_exp_mul_div_rpow_atTop (-b) a ha).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [powerExpWeight, Real.rpow_neg ht.le, div_inv_eq_mul, mul_comm]

theorem powerExpWeight_tail_deriv_lower {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t, T ≤ t →
      a / 2 * powerExpWeight a b t ≤ (a + b / t) * powerExpWeight a b t := by
  have hl : Tendsto (fun t : ℝ => b / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨S, hS⟩ := eventually_atTop.mp ((tendsto_order.mp hl).1 (-a / 2) (by linarith))
  refine ⟨max 1 S, le_max_left _ _, ?_⟩
  intro t ht
  have h1 : 1 ≤ t := (le_max_left 1 S).trans ht
  have hb := hS t ((le_max_right 1 S).trans ht)
  exact mul_le_mul_of_nonneg_right (by linarith) (powerExpWeight_pos (by linarith) a b).le

theorem powerExpProfile_norm {t : ℝ} (ht : 0 < t) (lam : ℂ) (b : ℝ) :
    ‖powerExpProfile lam b t‖ = powerExpWeight lam.re b t := by
  simp only [powerExpProfile, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, powerExpWeight]

theorem powerExpProfile_ne_zero {t : ℝ} (ht : 0 < t) (lam : ℂ) (b : ℝ) :
    powerExpProfile lam b t ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [powerExpProfile_norm ht]
  exact (powerExpWeight_pos ht lam.re b).ne'

theorem powerExpProfile_hasDerivAt {t : ℝ} (ht : 0 < t) (lam : ℂ) (b : ℝ) :
    HasDerivAt (powerExpProfile lam b)
      ((lam + ((b / t : ℝ) : ℂ)) * powerExpProfile lam b t) t := by
  have he : HasDerivAt (fun s : ℝ => Complex.exp (lam * (s : ℂ)))
      (Complex.exp (lam * (t : ℂ)) * lam) t := by
    simpa only [mul_one, id_eq] using! (((hasDerivAt_id (t : ℂ)).const_mul lam).cexp).comp_ofReal
  have hd := (Real.hasDerivAt_rpow_const (p := b) (Or.inl ht.ne')).ofReal_comp.mul he
  apply hd.congr_deriv
  rw [Real.rpow_sub_one ht.ne']
  dsimp [powerExpProfile]
  push_cast
  ring

theorem powerExpProfile_normalization {t : ℝ} (ht : 0 < t) (lam z : ℂ) (b : ℝ) :
    t ^ (-b) • (Complex.exp (-lam * (t : ℂ)) • z) = z / powerExpProfile lam b t := by
  rw [Real.rpow_neg ht.le]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_inv, powerExpProfile]
  rw [show -lam * (t : ℂ) = -(lam * (t : ℂ)) by ring, Complex.exp_neg]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.powerExpProfile_hasDerivAt
#print axioms ModifiedCartan.powerExpWeight_tail_deriv_lower

