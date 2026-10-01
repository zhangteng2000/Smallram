import ModifiedCartan.FundamentalOperator

open scoped BigOperators Topology
open Filter Set

namespace ModifiedCartan

noncomputable section

/-- Logarithmic derivative of an inverse Wronskian root, defined without a branch.
LaTeX context: the differential-polynomial argument in `lem:canonical-gauge`. -/
def canonicalLogDerivative (n : ℕ) (g : Index n → ℂ → ℂ) (z : ℂ) : ℂ :=
  -deriv (fun w => FewInflection.wronskian n g w) z /
    ((n + 1 : ℂ) * FewInflection.wronskian n g z)

def logarithmicJet (a : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 1
  | k + 1 => fun z => deriv (logarithmicJet a k) z + a z * logarithmicJet a k z

theorem analyticAt_logarithmicJet {a : ℂ → ℂ} {z : ℂ}
    (ha : AnalyticAt ℂ a z) (k : ℕ) : AnalyticAt ℂ (logarithmicJet a k) z := by
  induction k with
  | zero => exact analyticAt_const
  | succ k ih => exact ih.deriv.add (ha.mul ih)

theorem meromorphicAt_logarithmicJet {a : ℂ → ℂ} {z : ℂ}
    (ha : MeromorphicAt a z) (k : ℕ) : MeromorphicAt (logarithmicJet a k) z := by
  induction k with
  | zero => exact MeromorphicAt.const 1 z
  | succ k ih => exact ih.deriv.add (ha.mul ih)

theorem analyticAt_canonicalLogDerivative {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0) :
    AnalyticAt ℂ (canonicalLogDerivative n g) z := by
  have hw := FewInflection.analyticAt_wronskian hg
  exact hw.deriv.neg.div (analyticAt_const.mul hw)
    (mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) hW)

theorem meromorphicAt_canonicalLogDerivative {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) : MeromorphicAt (canonicalLogDerivative n g) z := by
  have hw := (FewInflection.analyticAt_wronskian hg).meromorphicAt
  exact hw.deriv.neg.div ((MeromorphicAt.const (n + 1 : ℂ) z).mul hw)

theorem normalizing_factor_deriv {n : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {g : Index n → ℂ → ℂ} (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    {η : ℂ → ℂ} (hη : AnalyticOnNhd ℂ η U) (hη0 : ∀ z ∈ U, η z ≠ 0)
    (hroot : ∀ z ∈ U, η z ^ (n + 1) * FewInflection.wronskian n g z = 1)
    {z : ℂ} (hz : z ∈ U) :
    deriv η z = canonicalLogDerivative n g z * η z := by
  have hW : FewInflection.wronskian n g z ≠ 0 := by
    intro hzero
    have hh := hroot z hz
    simp [hzero] at hh
  have hw := FewInflection.analyticAt_wronskian (fun j => hg j z hz)
  have he : (fun w => η w ^ (n + 1) * FewInflection.wronskian n g w) =ᶠ[𝓝 z]
      (fun _ => (1 : ℂ)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hroot w hw
  have hd := ((hη z hz).differentiableAt.hasDerivAt.pow (n + 1)).mul
    hw.differentiableAt.hasDerivAt
  have hderiv := hd.deriv
  have hederiv := he.deriv_eq
  rw [deriv_const] at hederiv
  change deriv (fun w => η w ^ (n + 1) * FewInflection.wronskian n g w) z = _ at hderiv
  rw [hderiv] at hederiv
  simp only [Nat.add_sub_cancel] at hederiv
  rw [pow_succ] at hederiv
  simp only [Nat.cast_add, Nat.cast_one, Pi.mul_apply, Pi.pow_apply] at hederiv
  have hprod : η z ^ n * ((n + 1 : ℂ) * FewInflection.wronskian n g z * deriv η z +
      η z * deriv (fun w => FewInflection.wronskian n g w) z) = 0 := by
    linear_combination hederiv
  have hzero := (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ (hη0 z hz))
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  unfold canonicalLogDerivative
  field_simp [hn, hW]
  linear_combination hzero

theorem iteratedDeriv_eq_logarithmicJet_mul {U : Set ℂ} (hU : IsOpen U)
    {a η : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a U) (hη : AnalyticOnNhd ℂ η U)
    (hderiv : ∀ z ∈ U, deriv η z = a z * η z) (k : ℕ) :
    ∀ z ∈ U, iteratedDeriv k η z = logarithmicJet a k z * η z := by
  induction k with
  | zero => intro z hz; simp [logarithmicJet]
  | succ k ih =>
    intro z hz
    have he : iteratedDeriv k η =ᶠ[𝓝 z] (fun w => logarithmicJet a k w * η w) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact ih w hw
    rw [iteratedDeriv_succ, he.deriv_eq,
      deriv_fun_mul (analyticAt_logarithmicJet (ha z hz) k).differentiableAt
        (hη z hz).differentiableAt, hderiv z hz]
    simp only [logarithmicJet]
    ring

def covariantJet (a f : ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (m + 1),
    (m.choose k : ℂ) * logarithmicJet a k z * iteratedDeriv (m - k) f z

theorem analyticAt_covariantJet {a f : ℂ → ℂ} {z : ℂ}
    (ha : AnalyticAt ℂ a z) (hf : AnalyticAt ℂ f z) (m : ℕ) :
    AnalyticAt ℂ (covariantJet a f m) z := by
  apply Finset.analyticAt_fun_sum
  intro k _
  exact (analyticAt_const.mul (analyticAt_logarithmicJet ha k)).mul
    (FewInflection.analyticAt_iteratedDeriv hf (m - k))

theorem meromorphicAt_covariantJet {a f : ℂ → ℂ} {z : ℂ}
    (ha : MeromorphicAt a z) (hf : AnalyticAt ℂ f z) (m : ℕ) :
    MeromorphicAt (covariantJet a f m) z := by
  apply MeromorphicAt.fun_sum
  intro k _
  exact ((MeromorphicAt.const (m.choose k : ℂ) z).mul (meromorphicAt_logarithmicJet ha k)).mul
    (FewInflection.analyticAt_iteratedDeriv hf (m - k)).meromorphicAt

theorem iteratedDeriv_mul_eq_covariantJet {U : Set ℂ} (hU : IsOpen U)
    {a η f : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a U) (hη : AnalyticOnNhd ℂ η U)
    (hf : AnalyticOnNhd ℂ f U) (hderiv : ∀ z ∈ U, deriv η z = a z * η z)
    (m : ℕ) {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv m (fun w => η w * f w) z = η z * covariantJet a f m z := by
  change iteratedDeriv m (η * f) z = _
  rw [iteratedDeriv_mul (hη z hz).contDiffAt (hf z hz).contDiffAt]
  simp_rw [iteratedDeriv_eq_logarithmicJet_mul hU ha hη hderiv _ z hz]
  unfold covariantJet
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

def canonicalNumerator (n : ℕ) (g : Index n → ℂ → ℂ)
    (i : Index n) (z : ℂ) : ℂ :=
  Matrix.det (Function.update
    (fun (k j : Index n) => covariantJet (canonicalLogDerivative n g) (g j) k z) i
    (fun j => -covariantJet (canonicalLogDerivative n g) (g j) (n + 1) z))

/-- The canonical coefficients of derivative order `i`, defined on the original
domain without choosing a root of the Wronskian. -/
def canonicalCoefficient (n : ℕ) (g : Index n → ℂ → ℂ)
    (i : Index n) (z : ℂ) : ℂ :=
  canonicalNumerator n g i z / FewInflection.wronskian n g z

theorem meromorphicAt_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℂ → Matrix ι ι ℂ} {z : ℂ}
    (hM : ∀ i j, MeromorphicAt (fun w => M w i j) z) :
    MeromorphicAt (fun w => (M w).det) z := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply MeromorphicAt.fun_sum
  intro σ _
  exact (MeromorphicAt.const _ z).mul (MeromorphicAt.fun_prod (fun i _ => hM (σ i) i))

theorem analyticAt_canonicalNumerator {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0)
    (i : Index n) : AnalyticAt ℂ (canonicalNumerator n g i) z := by
  have ha := analyticAt_canonicalLogDerivative hg hW
  apply FewInflection.analyticAt_matrix_det
  intro k j
  by_cases hki : k = i
  · subst k
    simpa only [Function.update_self] using (analyticAt_covariantJet ha (hg j) (n + 1)).fun_neg
  · simpa only [Function.update_of_ne hki] using analyticAt_covariantJet ha (hg j) k

theorem meromorphicAt_canonicalNumerator {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (i : Index n) :
    MeromorphicAt (canonicalNumerator n g i) z := by
  have ha := meromorphicAt_canonicalLogDerivative hg
  apply meromorphicAt_matrix_det
  intro k j
  by_cases hki : k = i
  · subst k
    simpa only [Function.update_self] using (meromorphicAt_covariantJet ha (hg j) (n + 1)).fun_neg
  · simpa only [Function.update_of_ne hki] using meromorphicAt_covariantJet ha (hg j) k

theorem analyticAt_canonicalCoefficient {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hW : FewInflection.wronskian n g z ≠ 0)
    (i : Index n) : AnalyticAt ℂ (canonicalCoefficient n g i) z :=
  (analyticAt_canonicalNumerator hg hW i).div (FewInflection.analyticAt_wronskian hg) hW

theorem meromorphicAt_canonicalCoefficient {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (i : Index n) :
    MeromorphicAt (canonicalCoefficient n g i) z :=
  (meromorphicAt_canonicalNumerator hg i).div (FewInflection.analyticAt_wronskian hg).meromorphicAt

theorem fundamentalNumerator_normalizing_factor {n : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {g : Index n → ℂ → ℂ} (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    {η : ℂ → ℂ} (hη : AnalyticOnNhd ℂ η U) (hη0 : ∀ z ∈ U, η z ≠ 0)
    (hroot : ∀ z ∈ U, η z ^ (n + 1) * FewInflection.wronskian n g z = 1)
    (i : Index n) {z : ℂ} (hz : z ∈ U) :
    FewInflection.fundamentalNumerator n (fun j w => η w * g j w) i z =
      η z ^ (n + 1) * canonicalNumerator n g i z := by
  have ha : AnalyticOnNhd ℂ (canonicalLogDerivative n g) U := by
    intro w hw
    apply analyticAt_canonicalLogDerivative (fun j => hg j w hw)
    intro hzero
    have hh := hroot w hw
    simp [hzero] at hh
  have hderiv : ∀ w ∈ U, deriv η w = canonicalLogDerivative n g w * η w :=
    fun w hw => normalizing_factor_deriv hU hg hη hη0 hroot hw
  have hj (j : Index n) (m : ℕ) :
      iteratedDeriv m (fun w => η w * g j w) z =
        η z * covariantJet (canonicalLogDerivative n g) (g j) m z :=
    iteratedDeriv_mul_eq_covariantJet hU ha hη (hg j) hderiv m hz
  unfold FewInflection.fundamentalNumerator canonicalNumerator
  have hmat : (Function.update
      (fun (k j : Index n) => iteratedDeriv k (fun w => η w * g j w) z) i
      (fun j => -iteratedDeriv (n + 1) (fun w => η w * g j w) z) :
        Matrix (Index n) (Index n) ℂ) =
      η z • (Function.update
        (fun (k j : Index n) => covariantJet (canonicalLogDerivative n g) (g j) k z) i
        (fun j => -covariantJet (canonicalLogDerivative n g) (g j) (n + 1) z) :
          Matrix (Index n) (Index n) ℂ) := by
    funext k j
    by_cases hki : k = i
    · subst k
      simp only [Pi.smul_apply, smul_eq_mul, Function.update_self, hj, mul_neg]
    · simp only [Pi.smul_apply, smul_eq_mul, Function.update_of_ne hki, hj]
  rw [hmat]
  convert! Matrix.det_smul (Function.update
    (fun (k j : Index n) => covariantJet (canonicalLogDerivative n g) (g j) k z) i
    (fun j => -covariantJet (canonicalLogDerivative n g) (g j) (n + 1) z)) (η z) using 1
  simp only [Index, FewInflection.Index, Fintype.card_fin]

/-- Identification of the explicit global formula with every local root gauge.
LaTeX label: `lem:canonical-gauge` (meromorphic continuation part). -/
theorem canonicalCoefficient_eq_normalized {n : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {g : Index n → ℂ → ℂ} (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    {η : ℂ → ℂ} (hη : AnalyticOnNhd ℂ η U) (hη0 : ∀ z ∈ U, η z ≠ 0)
    (hroot : ∀ z ∈ U, η z ^ (n + 1) * FewInflection.wronskian n g z = 1)
    (i : Index n) {z : ℂ} (hz : z ∈ U) :
    canonicalCoefficient n g i z =
      FewInflection.fundamentalCoefficients n (fun j w => η w * g j w) z i := by
  rw [FewInflection.fundamentalCoefficients_eq_quotient,
    fundamentalNumerator_normalizing_factor hU hg hη hη0 hroot i hz,
    FewInflection.wronskian_scalar_mul η g z (hη z hz).contDiffAt
      (fun j => (hg j z hz).contDiffAt)]
  unfold canonicalCoefficient
  rw [mul_div_mul_left _ _ (pow_ne_zero _ (hη0 z hz))]

end
end ModifiedCartan

