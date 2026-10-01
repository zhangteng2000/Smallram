import FewInflection.FundamentalOperator

/-!
# Analytic and meromorphic fundamental coefficients

This supplies part (ii) of the paper's fundamental-operator lemma.  The
coefficient functions are the unique coefficients already constructed by
linear algebra; the quotient formula below proves their analytic properties.
All analyticity statements are local and therefore also apply to local frames.
-/

open scoped BigOperators Topology

namespace FewInflection

noncomputable section

theorem analyticAt_iteratedDeriv {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (m : ℕ) :
    AnalyticAt ℂ (iteratedDeriv m g) z := by
  simpa only [iteratedDeriv_eq_iterate] using hg.iterated_deriv m

theorem analyticAt_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℂ → Matrix ι ι ℂ} {z : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) :
    AnalyticAt ℂ (fun w => (M w).det) z := by
  simp only [Matrix.det_apply]
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact (Finset.analyticAt_fun_prod _ (fun i _ => hM (σ i) i)).const_smul

theorem analyticAt_wronskian {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) :
    AnalyticAt ℂ (fun w => wronskian n g w) z := by
  apply analyticAt_matrix_det
  intro i j
  exact analyticAt_iteratedDeriv (hg j) i

/- The row expansion of the determinant is convenient for differentiating a
finite jet matrix.  Mathlib's primitive expansion is column-oriented, so this
is obtained by applying it to the transpose. -/
lemma Matrix.det_apply_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    A.det = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i : ι, A i (σ i) := by
  rw [← Matrix.det_transpose A, Matrix.det_apply]
  simp only [Matrix.transpose_apply]

lemma deriv_det_updateRow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M M' : ℂ → Matrix ι ι ℂ} {z : ℂ}
    (hM : ∀ i j, HasDerivAt (fun w => M w i j) (M' z i j) z) :
    deriv (fun w => (M w).det) z =
      ∑ i : ι, ((M z).updateRow i (fun j => M' z i j)).det := by
  have hdetfun : (fun w => (M w).det) =
      (fun w => ∑ σ : Equiv.Perm ι,
        Equiv.Perm.sign σ • ∏ i : ι, M w i (σ i)) := by
    funext w
    rw [Matrix.det_apply_row]
  rw [hdetfun]
  have hterm : ∀ σ : Equiv.Perm ι,
      HasDerivAt
        (fun w => Equiv.Perm.sign σ • ∏ i : ι, M w i (σ i))
        (Equiv.Perm.sign σ •
          (∑ i : ι,
            (Finset.univ.erase i).prod (fun j => M z j (σ j)) • M' z i (σ i))) z := by
    intro σ
    apply HasDerivAt.const_smul
    have hp := HasDerivAt.finsetProd (u := (Finset.univ : Finset ι))
      (fun i hi => hM i (σ i))
    have heq : (fun w => ∏ i : ι, M w i (σ i)) =
        (∏ i : ι, fun w => M w i (σ i)) := by
      funext w
      simp only [Finset.prod_apply]
    rw [heq]
    exact hp
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Equiv.Perm ι)))
    (fun σ hσ => hterm σ)
  have hderiv := hsum.deriv
  rw [hderiv]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.det_apply_row]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hprod :
      (Finset.univ.prod
        (fun k => (M z).updateRow i (fun j => M' z i j) k (σ k))) =
        ((Finset.univ.erase i).prod (fun k => M z k (σ k))) *
          M' z i (σ i) := by
    calc
      (Finset.univ.prod
          (fun k => (M z).updateRow i (fun j => M' z i j) k (σ k))) =
          ((Finset.univ.erase i).prod
            (fun k => (M z).updateRow i (fun j => M' z i j) k (σ k))) *
            (M z).updateRow i (fun j => M' z i j) i (σ i) := by
              symm
              exact Finset.prod_erase_mul (Finset.univ : Finset ι)
                (fun k => (M z).updateRow i (fun j => M' z i j) k (σ k))
                (Finset.mem_univ i)
      _ = ((Finset.univ.erase i).prod (fun k => M z k (σ k))) *
            M' z i (σ i) := by
              congr 1
              · apply Finset.prod_congr rfl
                intro k hk
                have hki : k ≠ i := (Finset.mem_erase.mp hk).1
                simp [Matrix.updateRow_apply, hki]
              · simp [Matrix.updateRow_apply]
  rw [hprod]
  congr 1

theorem deriv_wronskian_update_last
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) :
    deriv (fun w => wronskian n g w) z =
      Matrix.det (Matrix.updateRow
        (fun (i j : Index n) => iteratedDeriv (i : ℕ) (g j) z)
        ⟨n, Nat.lt_succ_self n⟩
        (fun j => iteratedDeriv (n + 1) (g j) z)) := by
  let M : ℂ → Matrix (Index n) (Index n) ℂ :=
    fun w i j => iteratedDeriv (i : ℕ) (g j) w
  let M' : ℂ → Matrix (Index n) (Index n) ℂ :=
    fun w i j => iteratedDeriv ((i : ℕ) + 1) (g j) w
  have hM : ∀ i j, HasDerivAt (fun w => M w i j) (M' z i j) z := by
    intro i j
    simpa only [M, M', iteratedDeriv_succ] using
      (analyticAt_iteratedDeriv (hg j) (i : ℕ)).differentiableAt.hasDerivAt
  have hd := deriv_det_updateRow hM
  change deriv (fun w => (M w).det) z = _ at hd
  rw [show (fun w => (M w).det) =
      (fun w => wronskian n g w) by rfl] at hd
  have hzero (i : Index n)
      (hi : i ≠ ⟨n, Nat.lt_succ_self n⟩) :
      ((M z).updateRow i (fun j => M' z i j)).det = 0 := by
    have hiltn : (i : ℕ) < n := by
      by_contra hnot
      have hge : n ≤ (i : ℕ) := Nat.le_of_not_gt hnot
      have hle : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
      have heq : (i : ℕ) = n := le_antisymm hle hge
      apply hi
      exact Fin.ext heq
    let k : Index n := ⟨(i : ℕ) + 1, by omega⟩
    have hik : i ≠ k := by
      intro h
      have hh := congrArg (fun x : Index n => (x : ℕ)) h
      simp [k] at hh
    have hrow : (fun j => M' z i j) = M z k := by
      funext j
      simp [M, M', k]
    rw [hrow]
    exact Matrix.det_updateRow_eq_zero hik.symm
  have hsum :
      (∑ i : Index n, ((M z).updateRow i (fun j => M' z i j)).det) =
        ((M z).updateRow ⟨n, Nat.lt_succ_self n⟩
          (fun j => M' z ⟨n, Nat.lt_succ_self n⟩ j)).det := by
    simpa using
      (Finset.sum_eq_single (s := (Finset.univ : Finset (Index n)))
        (f := fun i : Index n => ((M z).updateRow i (fun j => M' z i j)).det)
        ⟨n, Nat.lt_succ_self n⟩
        (by
          intro b hb hbn
          exact hzero b hbn)
        (by
          intro hlast
          exact False.elim (hlast (Finset.mem_univ _))))
  rw [hsum] at hd
  simpa [M, M'] using hd

/-- The numerator obtained by replacing row `i` of the jet matrix by the
negative highest derivative.  This includes the Cramer sign convention. -/
def fundamentalNumerator (n : ℕ) (g : Index n → ℂ → ℂ)
    (i : Index n) (z : ℂ) : ℂ :=
  Matrix.det (Function.update
    (fun (k j : Index n) => iteratedDeriv (k : ℕ) (g j) z) i
    (fun j => -iteratedDeriv (n + 1) (g j) z))

theorem fundamentalCoefficients_eq_quotient
    (n : ℕ) (g : Index n → ℂ → ℂ) (z : ℂ) (i : Index n) :
    fundamentalCoefficients n g z i =
      fundamentalNumerator n g i z / wronskian n g z := by
  classical
  by_cases hW : wronskian n g z ≠ 0
  · have h := congrFun (fundamentalCoefficients_cramer hW) i
    let M : Matrix (Index n) (Index n) ℂ :=
      fun k j => iteratedDeriv (k : ℕ) (g j) z
    let rhs : Index n → ℂ :=
      fun j => -iteratedDeriv (n + 1) (g j) z
    change M.det • fundamentalCoefficients n g z i =
      M.transpose.cramer rhs i at h
    simp only [smul_eq_mul] at h
    rw [Matrix.cramer_transpose_apply] at h
    rw [mul_comm] at h
    apply (eq_div_iff hW).2
    have hmat :
        Matrix.of (Function.update
          (fun (k j : Index n) => iteratedDeriv (k : ℕ) (g j) z) i
          (fun j => -iteratedDeriv (n + 1) (g j) z)) =
          (Function.update
            (fun (k j : Index n) => iteratedDeriv (k : ℕ) (g j) z) i
            (fun j => -iteratedDeriv (n + 1) (g j) z) :
            Matrix (Index n) (Index n) ℂ) := by
      ext k j
      rfl
    have hdet := congrArg Matrix.det hmat
    simpa only [wronskian, fundamentalNumerator, M, rhs, Matrix.updateRow,
      Matrix.of_apply] using h.trans (by simpa only [hdet])
  · simp [fundamentalCoefficients, hW, not_ne_iff.mp hW]

theorem fundamental_last_coefficient_mul_wronskian
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hW : wronskian n g z ≠ 0) :
    fundamentalCoefficients n g z ⟨n, Nat.lt_succ_self n⟩ * wronskian n g z =
      -deriv (fun w => wronskian n g w) z := by
  let last : Index n := ⟨n, Nat.lt_succ_self n⟩
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv (i : ℕ) (g j) z
  let H : Index n → ℂ := fun j => iteratedDeriv (n + 1) (g j) z
  have hquot := fundamentalCoefficients_eq_quotient n g z last
  have hmul : fundamentalCoefficients n g z last * wronskian n g z =
      fundamentalNumerator n g last z := by
    exact (eq_div_iff hW).mp hquot
  have hnum : fundamentalNumerator n g last z =
      -Matrix.det (M.updateRow last H) := by
    have hmat :
        Matrix.of (Function.update
          (fun (i j : Index n) => iteratedDeriv (i : ℕ) (g j) z) last
          (fun j => -iteratedDeriv (n + 1) (g j) z)) =
          M.updateRow last (fun j => -H j) := by
      ext i j
      simp only [Matrix.of_apply]
      by_cases hi : i = last
      · subst i
        rw [Matrix.updateRow_self]
        simp [H]
      · rw [Function.update_of_ne hi, Matrix.updateRow_apply]
        simp [M, hi]
    unfold fundamentalNumerator
    rw [show Matrix.det (Function.update
          (fun (i j : Index n) => iteratedDeriv (i : ℕ) (g j) z) last
          (fun j => -iteratedDeriv (n + 1) (g j) z)) =
        Matrix.det (Matrix.of (Function.update
          (fun (i j : Index n) => iteratedDeriv (i : ℕ) (g j) z) last
          (fun j => -iteratedDeriv (n + 1) (g j) z))) by rfl]
    rw [hmat]
    have hsmul : (fun j => -H j) = (-1 : ℂ) • H := by
      funext j
      simp
    rw [hsmul, Matrix.det_updateRow_smul]
    simp
  rw [hmul, hnum]
  have hd := deriv_wronskian_update_last hg
  change deriv (fun w => wronskian n g w) z =
    Matrix.det (M.updateRow last H) at hd
  rw [hd]

theorem fundamentalCoefficients_const_mul
    {n : ℕ} {g : Index n → ℂ → ℂ} {z c : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hc : c ≠ 0)
    (hW : wronskian n g z ≠ 0) :
    fundamentalCoefficients n (fun j x => c * g j x) z =
      fundamentalCoefficients n g z := by
  have hWc : wronskian n (fun j x => c * g j x) z ≠ 0 := by
    rw [wronskian_const_gauge g c z]
    · exact mul_ne_zero (pow_ne_zero _ hc) hW
    · intro i j
      exact (hg j).contDiffAt
  apply funext
  intro i
  have hu := fundamentalCoefficients_unique hWc
    (b := fundamentalCoefficients n g z) (by
      intro j
      have hs := fundamentalCoefficients_spec hW j
      simp only [iteratedDeriv_const_mul_field]
      have hsum :
          (∑ i : Index n, fundamentalCoefficients n g z i *
              (c * iteratedDeriv (i : ℕ) (g j) z)) =
            c * ∑ i : Index n, fundamentalCoefficients n g z i *
              iteratedDeriv (i : ℕ) (g j) z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsum]
      linear_combination c * hs)
  exact congrFun hu.symm i

theorem fundamental_last_coefficient_eq_neg_deriv_div
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hW : wronskian n g z ≠ 0) :
    fundamentalCoefficients n g z ⟨n, Nat.lt_succ_self n⟩ =
      -deriv (fun w => wronskian n g w) z / wronskian n g z := by
  apply (eq_div_iff hW).2
  exact fundamental_last_coefficient_mul_wronskian hg hW

theorem analyticAt_fundamentalNumerator
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (i : Index n) :
    AnalyticAt ℂ (fundamentalNumerator n g i) z := by
  apply analyticAt_matrix_det
  intro k j
  by_cases hki : k = i
  · subst k
    apply (analyticAt_iteratedDeriv (hg j) (n + 1)).neg.congr
    filter_upwards [] with w
    simp only [Function.update_self]
    rfl
  · simpa only [Function.update_of_ne hki] using
      analyticAt_iteratedDeriv (hg j) k

theorem meromorphicAt_fundamentalCoefficients
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (i : Index n) :
    MeromorphicAt (fun w => fundamentalCoefficients n g w i) z := by
  simp_rw [fundamentalCoefficients_eq_quotient]
  exact (analyticAt_fundamentalNumerator hg i).meromorphicAt.div
    (analyticAt_wronskian hg).meromorphicAt

theorem analyticAt_fundamentalCoefficients
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hW : wronskian n g z ≠ 0) (i : Index n) :
    AnalyticAt ℂ (fun w => fundamentalCoefficients n g w i) z := by
  simp_rw [fundamentalCoefficients_eq_quotient]
  exact (analyticAt_fundamentalNumerator hg i).div (analyticAt_wronskian hg) hW

theorem meromorphic_fundamentalCoefficients {n : ℕ} (f : Curve n) (i : Index n) :
    Meromorphic (fun w => fundamentalCoefficients n f.coord w i) := by
  intro z
  exact meromorphicAt_fundamentalCoefficients
    (fun j => (f.holomorphic j).analyticAt z) i

end

end FewInflection
