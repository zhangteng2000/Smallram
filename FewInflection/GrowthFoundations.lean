import FewInflection.PolynomialGrowth

open scoped BigOperators Topology
open Filter Asymptotics
open Set

namespace FewInflection

noncomputable section

/-! ### A uniform logarithmic regular-variation estimate

The compact-set form used by `RegularlyVarying` is proved here directly.  On
a compact set of positive multipliers, `|log c|` is uniformly bounded; after
choosing the radius so that `log r` dominates that bound, the quotient differs
from one by `log c / log r`.
-/

theorem regularlyVarying_log :
    RegularlyVarying (fun r : ℝ => Real.log r) 0 := by
  intro K hK hKpos ε hε
  by_cases hKempty : K = ∅
  · subst K
    refine ⟨1, by norm_num, ?_⟩
    intro r hr c hc
    exact hc.elim
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
  have hlogcont : ContinuousOn (fun c : ℝ => |Real.log c|) K := by
    exact (continuousOn_id.log (fun c hc => (ne_of_gt (hKpos hc)))).abs
  obtain ⟨M, hM⟩ := hK.bddAbove_image hlogcont
  have hMnonneg : 0 ≤ M := by
    obtain ⟨c, hc⟩ := hKne
    have hMc := hM (mem_image_of_mem _ hc)
    exact le_trans (abs_nonneg _) hMc
  let R : ℝ := max 2 (Real.exp ((M + 1) / ε))
  refine ⟨R, ?_, ?_⟩
  · have hExp : 1 < Real.exp ((M + 1) / ε) := by
      exact Real.one_lt_exp_iff.mpr (by positivity)
    exact lt_max_of_lt_right (by positivity)
  · intro r hr c hc
    have hr2 : 2 < r := lt_of_le_of_lt (le_max_left _ _) hr
    have hRexp : Real.exp ((M + 1) / ε) < r :=
      lt_of_le_of_lt (le_max_right _ _) hr
    have hrpos : 0 < r := lt_trans (by norm_num) hr2
    have hlogpos : 0 < Real.log r := Real.log_pos (lt_trans (by norm_num) hr2)
    have hloglower : (M + 1) / ε < Real.log r := by
      exact (Real.lt_log_iff_exp_lt hrpos).2 hRexp
    have hcpos : 0 < c := hKpos hc
    have hlogmul : Real.log (c * r) = Real.log c + Real.log r :=
      Real.log_mul (ne_of_gt hcpos) (ne_of_gt hrpos)
    have habs : |Real.log c| ≤ M := hM (mem_image_of_mem _ hc)
    have hbound : |Real.log c| / Real.log r < ε := by
      apply (div_lt_iff₀ hlogpos).2
      have htmp := (div_lt_iff₀ hε).mp hloglower
      have hMle : M ≤ ε * Real.log r - 1 := by nlinarith
      nlinarith [habs, abs_nonneg (Real.log c)]
    change |Real.log (c * r) / Real.log r - Real.rpow c 0| < ε
    rw [hlogmul]
    have hpow : Real.rpow c (0 : ℝ) = 1 := by norm_num
    rw [hpow]
    have heq : (Real.log c + Real.log r) / Real.log r - 1 =
        Real.log c / Real.log r := by
      field_simp [ne_of_gt hlogpos]
      ring
    rw [heq, abs_div, abs_of_pos hlogpos]
    exact hbound

theorem characteristic_monomialCurve_regularlyVarying {n : ℕ} (hn : 0 < n) :
    RegularlyVarying (characteristic (monomialCurve n)) 0 := by
  intro K hK hKpos ε hε
  by_cases hKempty : K = ∅
  · subst K
    refine ⟨1, by norm_num, ?_⟩
    intro r hr c hc
    exact hc.elim
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
  obtain ⟨c0, hc0K, hc0min⟩ := hK.exists_isMinOn hKne continuousOn_id
  have hc0pos : 0 < c0 := hKpos hc0K
  have hlog := regularlyVarying_log K hK hKpos ε hε
  rcases hlog with ⟨Rlog, hRlog, hlogbound⟩
  let R : ℝ := max Rlog (max 1 (c0⁻¹ + 1))
  refine ⟨R, ?_, ?_⟩
  · exact lt_max_of_lt_left hRlog
  · intro r hr c hc
    have hcpos : 0 < c := hKpos hc
    have hrlog : Rlog < r := lt_of_le_of_lt (le_max_left _ _) hr
    have hR1 : 1 ≤ R := by
      have hinner : (1 : ℝ) ≤ max 1 (c0⁻¹ + 1) := le_max_left _ _
      exact le_trans hinner (le_max_right Rlog (max 1 (c0⁻¹ + 1)))
    have hr1 : 1 ≤ r := le_trans hR1 (le_of_lt hr)
    have hcinv : c⁻¹ ≤ c0⁻¹ :=
      (inv_le_inv₀ hcpos hc0pos).2 (hc0min hc)
    have hcrinv : c⁻¹ < r := by
      have hRc : c0⁻¹ + 1 ≤ R := by
        have hinner : c0⁻¹ + 1 ≤ max 1 (c0⁻¹ + 1) := le_max_right _ _
        exact le_trans hinner (le_max_right Rlog (max 1 (c0⁻¹ + 1)))
      have hstep : c0⁻¹ < c0⁻¹ + 1 := by linarith
      exact lt_of_le_of_lt hcinv (lt_trans hstep (lt_of_le_of_lt hRc hr))
    have hcr1 : 1 ≤ c * r := by
      have hmul := mul_lt_mul_of_pos_left hcrinv hcpos
      have hcrlt : c * c⁻¹ < c * r := by
        simpa [mul_inv_cancel₀ (ne_of_gt hcpos)] using hmul
      exact le_of_lt (by simpa [mul_inv_cancel₀ (ne_of_gt hcpos)] using hcrlt)
    have hchar_r := characteristic_monomialCurve_atTop (n := n) hr1
    have hchar_cr := characteristic_monomialCurve_atTop (n := n) hcr1
    have hc0invpos : 0 < c0⁻¹ := inv_pos.mpr hc0pos
    have hRgt1 : 1 < R := by
      have hinner0 : 1 < c0⁻¹ + 1 := by linarith
      have hinner : 1 < max 1 (c0⁻¹ + 1) :=
        lt_of_lt_of_le hinner0 (le_max_right _ _)
      exact lt_of_lt_of_le hinner (le_max_right Rlog (max 1 (c0⁻¹ + 1)))
    have hrgt1 : 1 < r := lt_trans hRgt1 hr
    have hlogr : 0 < Real.log r := Real.log_pos hrgt1
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hquot : characteristic (monomialCurve n) (c * r) /
          characteristic (monomialCurve n) r =
          Real.log (c * r) / Real.log r := by
      rw [hchar_cr, hchar_r, Real.log_pow, Real.log_pow]
      field_simp [hnreal, ne_of_gt hlogr]
    change |characteristic (monomialCurve n) (c * r) /
      characteristic (monomialCurve n) r - Real.rpow c 0| < ε
    rw [hquot]
    exact hlogbound r hrlog c hc

theorem slowlyVarying_monomial_log {n : ℕ} (hn : 0 < n) :
    SlowlyVarying (fun r : ℝ => (n : ℝ) * Real.log (max r 2)) := by
  let ell : ℝ → ℝ := fun r => (n : ℝ) * Real.log (max r 2)
  change SlowlyVarying ell
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have hlog : 0 < Real.log (max r 2) := by
      apply Real.log_pos
      exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    exact mul_pos (by exact_mod_cast hn) hlog
  · have hmax : Continuous (fun r : ℝ => max r 2) :=
      continuous_id.max continuous_const
    exact continuousOn_const.mul (hmax.continuousOn.log (fun r hr => by
      have : 0 < max r 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
      exact ne_of_gt this))
  · intro ε hε
    let R : ℝ := max 2 (Real.exp ((Real.log 2 + 1) / ε))
    refine ⟨R, ?_, ?_⟩
    · exact lt_max_of_lt_left (by norm_num)
    · intro r hr c hc
      have hr2 : 2 < r := lt_of_le_of_lt (le_max_left _ _) hr
      have hRexp : Real.exp ((Real.log 2 + 1) / ε) < r :=
        lt_of_le_of_lt (le_max_right _ _) hr
      have hrpos : 0 < r := lt_trans (by norm_num) hr2
      have hlogpos : 0 < Real.log r := Real.log_pos (lt_trans (by norm_num) hr2)
      have hloglower : (Real.log 2 + 1) / ε < Real.log r :=
        (Real.lt_log_iff_exp_lt hrpos).2 hRexp
      have hc1 : 1 ≤ c := hc.1
      have hc2 : c ≤ 2 := hc.2
      have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc1
      have hcr2 : 2 ≤ c * r := by
        have htwo : 2 ≤ 2 * r := by nlinarith
        nlinarith
      have hmaxr : max r 2 = r := max_eq_left (le_of_lt hr2)
      have hmaxcr : max (c * r) 2 = c * r := max_eq_left hcr2
      have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
      have hlogc2 : Real.log c ≤ Real.log 2 := by
        exact (Real.strictMonoOn_log.le_iff_le hcpos (by norm_num)).2 hc2
      have hlogbound : |Real.log c| / Real.log r < ε := by
        rw [abs_of_nonneg hlogc0]
        apply (div_lt_iff₀ hlogpos).2
        have htmp := (div_lt_iff₀ hε).mp hloglower
        nlinarith
      change |ell (c * r) / ell r - 1| < ε
      dsimp [ell]
      rw [hmaxcr, hmaxr]
      have hlogmul : Real.log (c * r) = Real.log c + Real.log r :=
        Real.log_mul (ne_of_gt hcpos) (ne_of_gt hrpos)
      rw [hlogmul]
      have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      have heq : (n : ℝ) * (Real.log c + Real.log r) /
            ((n : ℝ) * Real.log r) - 1 = Real.log c / Real.log r := by
        field_simp [hnreal, ne_of_gt hlogpos]
        ring
      rw [heq, abs_div, abs_of_pos hlogpos]
      exact hlogbound

theorem monomial_characteristic_factor {n : ℕ} (hn : 0 < n) :
    ∃ ell : ℝ → ℝ, SlowlyVarying ell ∧
      ∀ᶠ r in atTop,
        characteristic (monomialCurve n) r = Real.rpow r 0 * ell r := by
  refine ⟨fun r : ℝ => (n : ℝ) * Real.log (max r 2),
    slowlyVarying_monomial_log hn, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  rw [characteristic_monomialCurve_atTop (le_trans (by norm_num) hr), Real.log_pow]
  have hmax : max r 2 = r := max_eq_left hr
  simp [hmax]

end

end FewInflection
