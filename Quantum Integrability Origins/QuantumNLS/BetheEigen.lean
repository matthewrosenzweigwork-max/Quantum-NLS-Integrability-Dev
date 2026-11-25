import QuantumNLS.BetheCollision
import QuantumNLS.BetheH1
import QuantumNLS.ContactOperator
import QuantumNLS.CollisionIdentification

/-!
Second integration by parts for the actual, unnormalized Bethe extension.
Target: periodic_basis.tex:43, R-8E4D05E7, eigenvector component only.
All imported author modules are frozen inputs.
The declarations below retain the boundary terms until they are proved to cancel.
-/

noncomputable section
open scoped BigOperators Topology Interval InnerProductSpace ComplexConjugate
open Filter MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.ProductWeakDerivatives QuantumNLS.CollisionIdentification
  QuantumNLS.BetheWavefunctions QuantumNLS.BetheWeakGradient
  QuantumNLS.BetheExtension QuantumNLS.BetheH1 QuantumNLS.BetheCollision

namespace QuantumNLS.BetheEigen

/-- The literal source energy, with no shift or scaling. -/
def energy {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) : ℝ :=
  ∑ j, BetheSmooth.sourceRoots L n c j ^ 2

/-- Inserting the moving coordinate is a smooth chamber chart, also at
its endpoints; its derivative there is the literal finite ansatz partial. -/
theorem ansatz_insert_hasDerivAt {N : ℕ} (c : ℝ) (q : Fin (N+1) → ℝ)
    (r : Fin (N+1)) (y : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (fun s => coordinateAnsatz c q (r.insertNth s y))
      (ansatzPartial c q r (r.insertNth t y)) t := by
  have h := coordinateAnsatz_update_hasDerivAt c q (r.insertNth t y) r t
  simpa only [Fin.update_insertNth] using h

/-- The chamber gradient along the insertion chart is differentiated without
discarding the endpoint value. -/
theorem ansatzPartial_insert_hasDerivAt {N : ℕ} (c : ℝ) (q : Fin (N+1) → ℝ)
    (r : Fin (N+1)) (y : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ansatzPartial c q r (r.insertNth s y))
      (ansatzSecondPartial c q r (r.insertNth t y)) t := by
  have h := ansatzPartial_update_hasDerivAt c q (r.insertNth t y) r t
  simpa only [Fin.update_insertNth] using h

/-- Actual opposite-face normal gradients agree. The cyclic identification
is the same one used for the values in the source proof. -/
theorem ansatzPartial_outer_faces {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (y : Fin N → ℝ) :
    ansatzPartial c (BetheSmooth.sourceRoots L n c) 0 (Fin.cons L y) =
      ansatzPartial c (BetheSmooth.sourceRoots L n c) (Fin.last N) (Fin.snoc y 0) := by
  have hu := (ansatz_insert_hasDerivAt c (BetheSmooth.sourceRoots L n c) 0 y L).scomp_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).const_add L) (by simp)
  have hd := ansatz_insert_hasDerivAt c (BetheSmooth.sourceRoots L n c) (Fin.last N) y 0
  simp only [Fin.insertNth_zero', Fin.insertNth_last', one_smul] at hu hd
  change HasDerivAt (fun s => coordinateAnsatz c (BetheSmooth.sourceRoots L n c)
    (Fin.cons (L+s) y)) _ 0 at hu
  have he : (fun s => coordinateAnsatz c (BetheSmooth.sourceRoots L n c)
      (Fin.cons (L+s) y)) = (fun s => coordinateAnsatz c (BetheSmooth.sourceRoots L n c)
      (Fin.snoc y s)) := by
    funext s
    exact BethePeriodic.wavefunction_periodic_faces hL hc hn y s
  rw [he] at hu
  exact hu.unique hd

/-- The two insertion charts give the very same wall tuple. This identifies
their endpoint traces before taking any integrals. -/
theorem insert_wall_eq {N : ℕ} (y : Fin (N+1) → ℝ) (r : Fin (N+1)) :
    (r.castSucc.insertNth (y r) y : Fin (N+2) → ℝ) =
      r.succ.insertNth (y r) y := by
  induction N with
  | zero =>
    have hr : r = 0 := Fin.ext (by omega)
    subst r
    ext i
    fin_cases i <;> simp [Fin.insertNth, Fin.succAboveCases]
  | succ N ih =>
    refine Fin.cases ?_ (fun r => ?_) r
    · change (Fin.insertNth (0 : Fin (N+3)) (y 0) y : Fin (N+3) → ℝ) =
        Fin.insertNth ((0 : Fin (N+2)).succ) (y 0) y
      rw [Fin.insertNth_zero']
      conv_rhs => rw [← Fin.cons_self_tail y]
      rw [Fin.insertNth_succ_cons, Fin.insertNth_zero']
      simp
    · rw [← Fin.cons_self_tail y]
      rw [← Fin.succ_castSucc]
      simp only [Fin.cons_succ, Fin.insertNth_succ_cons]
      rw [ih]

/-- The actual adjacent wall jump of the moving-coordinate chart gradient
is c times the unnormalized wall value. There is no prescribed jump premise. -/
theorem insertion_gradient_jump {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+2) → ℤ} (hn : Antitone n)
    (y : Fin (N+1) → ℝ) (r : Fin (N+1)) :
    ansatzPartial c (BetheSmooth.sourceRoots L n c) r.castSucc
        (r.castSucc.insertNth (y r) y) -
      ansatzPartial c (BetheSmooth.sourceRoots L n c) r.succ
        (r.succ.insertNth (y r) y) =
      (c : ℂ) * wavefunction L c n (r.castSucc.insertNth (y r) y) := by
  rw [← insert_wall_eq]
  apply wavefunction_partial_contact hL hc hn _ rfl
  rw [Fin.insertNth_apply_same, insert_wall_eq, Fin.insertNth_apply_same]

/-- Exact finite telescoping, retaining every internal jump once and the
two outer endpoints. It also applies when some cutpoints coincide. -/
theorem boundary_telescope {N : ℕ} (A B : Fin (N+1) → ℂ) :
    (∑ r, (A r - B r)) = A 0 - B (Fin.last N) +
      ∑ r : Fin N, (A r.succ - B r.castSucc) := by
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ A, Fin.sum_univ_castSucc B,
    Finset.sum_sub_distrib]
  ring

/-- Summing the actual source jumps supplies precisely c per moving
coordinate; the two coordinates of a collision together supply 2c. -/
theorem insertion_boundary_sum {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+2) → ℤ} (hn : Antitone n)
    (y : Fin (N+1) → ℝ) (φ : ℝ → ℂ) (hφ : φ L = φ 0) :
    (∑ r : Fin (N+2),
      (conj (ansatzPartial c (BetheSmooth.sourceRoots L n c) r
          (r.insertNth (Fin.cases L y r) y)) * φ (Fin.cases L y r) -
        conj (ansatzPartial c (BetheSmooth.sourceRoots L n c) r
          (r.insertNth (Fin.lastCases 0 y r) y)) * φ (Fin.lastCases 0 y r))) =
      -(c : ℂ) * ∑ r : Fin (N+1),
        conj (wavefunction L c n (r.castSucc.insertNth (y r) y)) * φ (y r) := by
  rw [boundary_telescope]
  simp only [Fin.cases_zero, Fin.lastCases_last, Fin.cases_succ,
    Fin.lastCases_castSucc, Fin.insertNth_zero, Fin.insertNth_last]
  rw [ansatzPartial_outer_faces hL hc hn, hφ, sub_self, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hj := congrArg conj (insertion_gradient_jump hL hc hn y r)
  simp only [map_sub, map_mul, Complex.conj_ofReal] at hj
  linear_combination -(φ (y r)) * hj

/-- Insertion between its ordered neighbors gives an antitone chart.
Spectator ties are permitted. -/
theorem antitone_insert {N : ℕ} (y : Fin N → ℝ) (hy : Antitone y)
    (r : Fin (N+1)) (t : ℝ)
    (hl : ∀ j : Fin N, j.castSucc < r → t ≤ y j)
    (hr : ∀ j : Fin N, r ≤ j.castSucc → y j ≤ t) :
    Antitone (r.insertNth t y) := by
  intro a b hab
  by_cases ha : a = r
  · subst a
    by_cases hb : b = r
    · subst b; exact le_rfl
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hb
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      exact hr j ((Fin.lt_succAbove_iff_le_castSucc r j).1
        (lt_of_le_of_ne hab (Fin.succAbove_ne r j).symm))
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
    by_cases hb : b = r
    · subst b
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      exact hl j ((Fin.succAbove_le_iff r j).1 hab)
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hb
      simp only [Fin.insertNth_apply_succAbove]
      apply hy
      exact (Fin.strictMono_succAbove r).le_iff_le.1 hab

/-- The nearest two cutpoints suffice for ordering an insertion chart. -/
theorem antitone_insert_of_bounds {N : ℕ} (L : ℝ) (y : Fin N → ℝ)
    (hy : Antitone y) (r : Fin (N+1)) (t : ℝ)
    (ht : Fin.lastCases 0 y r ≤ t ∧ t ≤ Fin.cases L y r) :
    Antitone (r.insertNth t y) := by
  apply antitone_insert y hy r t
  · intro j hj
    cases r using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hj).elim
    | succ r =>
      have hjr : j ≤ r := by
        rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hj
        exact Fin.le_def.mpr (Nat.le_of_lt_succ hj)
      have hu : t ≤ y r := by simpa only [Fin.cases_succ] using ht.2
      exact hu.trans (hy hjr)
  · intro j hj
    cases r using Fin.lastCases with
    | last => exact (not_le_of_gt (Fin.castSucc_lt_last j) hj).elim
    | cast r =>
      have hrj : r ≤ j := Fin.castSucc_le_castSucc_iff.1 hj
      have hl : y r ≤ t := by simpa only [Fin.lastCases_castSucc] using ht.1
      exact (hy hrj).trans hl

/-- A fixed permutation relates every insertion chart to a fixed moving
coordinate. It depends only on the rank, never on the moving value. -/
def insertionPermutation {N : ℕ} (r : Fin (N+1)) : Equiv.Perm (Fin (N+1)) :=
  (finSuccEquiv' r).trans (finSuccEquiv' 0).symm

theorem insert_eq_cons_permute {N : ℕ} (r : Fin (N+1)) (t : ℝ) (y : Fin N → ℝ) :
    r.insertNth t y = Fin.cons t y ∘ insertionPermutation r := by
  apply Fin.insertNth_eq_iff.2
  constructor
  · simp [insertionPermutation]
  · funext j
    simp [insertionPermutation, Fin.removeNth]

/-- On a closed insertion interval the actual symmetric extension is the
literal chamber expression, including the endpoint wall tuples. -/
theorem symmetricExtension_insertion_chart {N : ℕ} (L c : ℝ)
    (n : Fin (N+1) → ℤ) (y : Fin N → ℝ) (hy : Antitone y)
    (r : Fin (N+1)) {t : ℝ}
    (ht : Fin.lastCases 0 y r ≤ t ∧ t ≤ Fin.cases L y r) :
    symmetricExtension L c n (Fin.cons t y) =
      coordinateAnsatz c (BetheSmooth.sourceRoots L n c) (r.insertNth t y) := by
  rw [← symmetricExtension_permute L c n _ (insertionPermutation r),
    ← insert_eq_cons_permute]
  exact symmetricExtension_eq L c n (antitone_insert_of_bounds L y hy r t ht)

/-- On each open chart the actual moving-coordinate gradient agrees with
the corresponding chamber derivative. Endpoint traces use the continuous
chamber formula instead of the deliberately zero-valued wall gradient. -/
theorem gradient_insertion_chart {N : ℕ} (L c : ℝ) (n : Fin (N+1) → ℤ)
    (y : Fin N → ℝ) (hy : Antitone y) (r : Fin (N+1)) {t : ℝ}
    (ht : Fin.lastCases 0 y r < t ∧ t < Fin.cases L y r) :
    gradient L c n 0 (Fin.cons t y) =
      ansatzPartial c (BetheSmooth.sourceRoots L n c) r (r.insertNth t y) := by
  have hreg : regular (0 : Fin (N+1)) (Fin.cons t y) := by
    intro j hj
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
    simp only [Fin.cons_zero, Fin.cons_succ]
    by_cases h : j.castSucc < r
    · have hlt : t < y j := by
        cases r using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ h).elim
        | succ r =>
          have hu : t < y r := by simpa only [Fin.cases_succ] using ht.2
          have hjr : j ≤ r := by
            rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h
            exact Fin.le_def.mpr (Nat.le_of_lt_succ h)
          exact hu.trans_le (hy hjr)
      exact hlt.ne
    · have hlt : y j < t := by
        cases r using Fin.lastCases with
        | last => exact (h (Fin.castSucc_lt_last j)).elim
        | cast r =>
          have hl : y r < t := by simpa only [Fin.lastCases_castSucc] using ht.1
          exact (hy (Fin.castSucc_le_castSucc_iff.1 (le_of_not_gt h))).trans_lt hl
      exact hlt.ne'
  have he : (fun s => symmetricExtension L c n (Fin.cons s y)) =ᶠ[𝓝 t]
      (fun s => coordinateAnsatz c (BetheSmooth.sourceRoots L n c) (r.insertNth s y)) := by
    filter_upwards [eventually_gt_nhds ht.1, eventually_lt_nhds ht.2] with s hs₁ hs₂
    exact symmetricExtension_insertion_chart L c n y hy r ⟨hs₁.le, hs₂.le⟩
  have hd := (ansatz_insert_hasDerivAt c (BetheSmooth.sourceRoots L n c) r y t).congr_of_eventuallyEq he
  simp only [BetheWeakGradient.gradient, hreg, ↓reduceIte, Fin.cons_zero, Fin.update_cons_zero]
  exact hd.deriv

/-- Second IBP in an insertion chart, including both endpoint traces. -/
theorem insertion_second_integrationByParts {N : ℕ} (c : ℝ) (q : Fin (N+1) → ℝ)
    (r : Fin (N+1)) (y : Fin N → ℝ) (a b : ℝ) (φ : ℝ → ℂ)
    (hφ : ContDiff ℝ 1 φ) :
    (∫ t in a..b, conj (ansatzPartial c q r (r.insertNth t y)) * deriv φ t) =
      conj (ansatzPartial c q r (r.insertNth b y)) * φ b -
      conj (ansatzPartial c q r (r.insertNth a y)) * φ a -
      ∫ t in a..b, conj (ansatzSecondPartial c q r (r.insertNth t y)) * φ t := by
  simpa only [Fin.update_insertNth] using
    chamber_second_integrationByParts c q (r.insertNth 0 y) r a b φ hφ

/-- All second-IBP boundary terms of the sorted insertion charts cancel
to the actual contact values, with c per crossing. This is a sum of chart
integrals; identification with the global cube integral is a further step. -/
theorem sum_insertion_second_integrationByParts {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+2) → ℤ} (hn : Antitone n)
    (y : Fin (N+1) → ℝ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hper : φ L = φ 0) :
    (∑ r : Fin (N+2), ∫ t in (Fin.lastCases 0 y r)..(Fin.cases L y r),
      conj (ansatzPartial c (BetheSmooth.sourceRoots L n c) r (r.insertNth t y)) *
        deriv φ t) =
      -(c : ℂ) * ∑ r : Fin (N+1),
        conj (wavefunction L c n (r.castSucc.insertNth (y r) y)) * φ (y r) -
      ∑ r : Fin (N+2), ∫ t in (Fin.lastCases 0 y r)..(Fin.cases L y r),
        conj (ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) r
          (r.insertNth t y)) * φ t := by
  simp_rw [insertion_second_integrationByParts c _ _ _ _ _ φ hφ]
  rw [Finset.sum_sub_distrib, insertion_boundary_sum hL hc hn y φ hper]

/-- The insertion intervals have their actual orientation in the closed
cube. Zero length intervals are retained when spectator values repeat. -/
theorem insertion_interval_order {N : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (y : Fin N → ℝ) (hy : Antitone y) (hbox : ∀ j, y j ∈ Icc 0 L)
    (r : Fin (N+1)) : (Fin.lastCases (0 : ℝ) y r : ℝ) ≤ Fin.cases L y r := by
  cases N with
  | zero =>
    have hr : r = 0 := Fin.ext (by omega)
    subst r
    exact hL
  | succ N =>
    refine Fin.cases ?_ (fun r => ?_) r
    · change Fin.lastCases (0 : ℝ) y ((0 : Fin (N+1)).castSucc) ≤ L
      simpa only [Fin.lastCases_castSucc] using (hbox 0).2
    · cases r using Fin.lastCases with
      | last =>
        have hl : (Fin.lastCases (0 : ℝ) y (Fin.succ (Fin.last N)) : ℝ) = (0 : ℝ) := by
          rw [Fin.succ_last, Fin.lastCases_last]
        rw [hl]
        simpa only [Fin.cases_succ] using (hbox (Fin.last N)).1
      | cast r =>
        have hl : Fin.lastCases (0 : ℝ) y r.castSucc.succ = y r.succ := by
          rw [Fin.succ_castSucc, Fin.lastCases_castSucc]
        rw [hl, Fin.cases_succ]
        exact hy (Fin.castSucc_le_succ r)

/-- The finitely many insertion intervals partition the whole coordinate
integral. This identity retains zero length pieces and needs no strict
ordering or distinctness hypothesis on the cutpoints. -/
theorem integral_insertion_partition {N : ℕ} (L : ℝ) (y : Fin N → ℝ)
    (f : ℝ → ℂ) (hf : ∀ a b, IntervalIntegrable f volume a b) :
    (∫ t in (0 : ℝ)..L, f t) =
      ∑ r : Fin (N+1), ∫ t in (Fin.lastCases 0 y r)..(Fin.cases L y r), f t := by
  have he (r : Fin (N+1)) :
      (∫ t in (Fin.lastCases 0 y r)..(Fin.cases L y r), f t) =
        (∫ t in (0 : ℝ)..(Fin.cases L y r), f t) -
        ∫ t in (0 : ℝ)..(Fin.lastCases 0 y r), f t :=
    (intervalIntegral.integral_interval_sub_left (hf _ _) (hf _ _)).symm
  simp_rw [he]
  rw [boundary_telescope]
  simp

/-- Actual second IBP on an entire sorted coordinate slice: the chart
partition and its endpoint traces are now assembled, including every
collision and periodic outer-face cancellation. The bulk second partials
are still displayed chart by chart for the subsequent global Fubini step. -/
theorem sorted_slice_second_integrationByParts {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+2) → ℤ} (hn : Antitone n)
    (y : Fin (N+1) → ℝ) (hy : Antitone y) (hbox : ∀ j, y j ∈ Icc 0 L)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hper : φ L = φ 0) :
    (∫ t in (0 : ℝ)..L, conj (gradient L c n 0 (Fin.cons t y)) * deriv φ t) =
      -(c : ℂ) * ∑ r : Fin (N+1),
        conj (symmetricExtension L c n (Fin.cons (y r) y)) * φ (y r) -
      ∑ r : Fin (N+2), ∫ t in (Fin.lastCases 0 y r)..(Fin.cases L y r),
        conj (ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) r
          (r.insertNth t y)) * φ t := by
  have hi (a b : ℝ) : IntervalIntegrable
      (fun t => conj (gradient L c n 0 (Fin.cons t y)) * deriv φ t) volume a b := by
    have hm₀ : Measurable (fun t : ℝ => gradient L c n 0 (Fin.cons t y)) :=
      (measurable_gradient L c n 0).comp
        (by fun_prop : Measurable (fun t : ℝ => (Fin.cons t y : Fin (N+2) → ℝ)))
    have hm : AEStronglyMeasurable
        (fun t : ℝ => conj (gradient L c n 0 (Fin.cons t y))) volume :=
      (Complex.continuous_conj.measurable.comp hm₀).aestronglyMeasurable
    have hg : IntervalIntegrable (fun t => conj (gradient L c n 0 (Fin.cons t y))) volume a b := by
      constructor <;> exact (integrable_const (gradientBound c (BetheSmooth.sourceRoots L n c))).mono'
        hm.restrict (Filter.Eventually.of_forall fun t => by
          simpa only [Complex.norm_conj] using norm_gradient_le L c n 0 (Fin.cons t y))
    exact hg.mul_continuousOn hφ.continuous_deriv_one.continuousOn
  rw [integral_insertion_partition L y _ hi]
  have he (r : Fin (N+2)) :
      (∫ t in (Fin.lastCases 0 y r)..(Fin.cases L y r),
        conj (gradient L c n 0 (Fin.cons t y)) * deriv φ t) =
      ∫ t in (Fin.lastCases 0 y r)..(Fin.cases L y r),
        conj (ansatzPartial c (BetheSmooth.sourceRoots L n c) r (r.insertNth t y)) *
          deriv φ t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (Fin.cases L y r)] with t ht hmem
    rw [uIoc_of_le (insertion_interval_order hL.le y hy hbox r)] at hmem
    rw [gradient_insertion_chart L c n y hy r ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩]
  simp_rw [he]
  rw [sum_insertion_second_integrationByParts hL hc hn y φ hφ hper]
  congr 2
  apply Finset.sum_congr rfl
  intro r _
  congr 2
  symm
  apply symmetricExtension_insertion_chart L c n y hy r.castSucc
  constructor
  · simp
  · cases r using Fin.cases with
    | zero => simpa using (hbox 0).2
    | succ r =>
      simpa only [← Fin.succ_castSucc, Fin.cases_succ] using
        hy (Fin.castSucc_le_succ r)

/-- Coordinate covariance of the actual weak-gradient representative,
including its specified zero values on the collision walls. -/
theorem gradient_permute {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    gradient L c n i (x ∘ σ) = gradient L c n (σ i) x := by
  classical
  have hr : regular i (x ∘ σ) ↔ regular (σ i) x := by
    constructor
    · intro h
      simpa [Function.comp_def] using regular_permute h σ.symm
    · intro h
      simpa only [Equiv.symm_apply_apply] using regular_permute h σ
  by_cases hi : regular (σ i) x
  · have he : (fun t => symmetricExtension L c n (Function.update (x ∘ σ) i t)) =
        (fun t => symmetricExtension L c n (Function.update x (σ i) t)) := by
      funext t
      rw [← Function.update_comp_eq_of_injective x σ.injective i t]
      exact symmetricExtension_permute L c n _ σ
    simp only [BetheWeakGradient.gradient, hi, hr.2 hi, ↓reduceIte, Function.comp_apply]
    rw [he]
  · simp only [BetheWeakGradient.gradient, hi, not_congr hr |>.2 hi, ↓reduceIte]

/-- The fixed insertion permutation sends the moving slot to the first
coordinate. -/
theorem insertionPermutation_self {N : ℕ} (r : Fin (N+1)) :
    insertionPermutation r r = 0 := by
  simp [insertionPermutation]

/-- The actual coordinate derivative on every insertion slice has the same
value as the derivative with the moving coordinate placed first. -/
theorem gradient_insert {N : ℕ} (L c : ℝ) (n : Fin (N+1) → ℤ)
    (i : Fin (N+1)) (t : ℝ) (y : Fin N → ℝ) :
    gradient L c n i (i.insertNth t y) = gradient L c n 0 (Fin.cons t y) := by
  rw [insert_eq_cons_permute, gradient_permute, insertionPermutation_self]

/-- Sorting spectator coordinates leaves the moving-coordinate gradient
unchanged. The statement is literal, including tied spectators. -/
theorem gradient_cons_permute {N : ℕ} (L c : ℝ) (n : Fin (N+1) → ℤ)
    (t : ℝ) (y : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    gradient L c n 0 (Fin.cons t (y ∘ σ)) = gradient L c n 0 (Fin.cons t y) := by
  rw [cons_permute, gradient_permute]
  simp [headPermutation]

/-- Entire coordinate-slice second IBP for arbitrary spectator order and
any moving coordinate. Every collision term is the actual symmetric Bethe
value on that collision, indexed once by its spectator. The bulk remains a
sum of the explicit sorted chamber second-partial integrals. -/
theorem slice_second_integrationByParts {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+2) → ℤ} (hn : Antitone n)
    (i : Fin (N+2)) (y : Fin (N+1) → ℝ) (hbox : ∀ j, y j ∈ Icc 0 L)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hper : φ L = φ 0) :
    (∫ t in (0 : ℝ)..L, conj (gradient L c n i (i.insertNth t y)) * deriv φ t) =
      -(c : ℂ) * ∑ j : Fin (N+1),
        conj (symmetricExtension L c n (i.insertNth (y j) y)) * φ (y j) -
      ∑ r : Fin (N+2),
        ∫ t in (Fin.lastCases 0 (decreasing y) r)..(Fin.cases L (decreasing y) r),
          conj (ansatzSecondPartial c (BetheSmooth.sourceRoots L n c) r
            (r.insertNth t (decreasing y))) * φ t := by
  have hsortbox : ∀ j, decreasing y j ∈ Icc 0 L := fun j => hbox _
  have h := sorted_slice_second_integrationByParts hL hc hn (decreasing y)
    (decreasing_antitone y) hsortbox φ hφ hper
  have hg (t : ℝ) : gradient L c n 0 (Fin.cons t (decreasing y)) =
      gradient L c n i (i.insertNth t y) := by
    rw [gradient_insert]
    exact gradient_cons_permute L c n t y (Tuple.sort (α := ℝᵒᵈ) y)
  simp_rw [hg] at h
  rw [h]
  congr 2
  have hs (j : Fin (N+1)) :
      symmetricExtension L c n (Fin.cons (decreasing y j) (decreasing y)) =
        symmetricExtension L c n (i.insertNth (y (Tuple.sort (α := ℝᵒᵈ) y j)) y) := by
    rw [insert_eq_cons_permute, symmetricExtension_permute]
    exact symmetricExtension_cons_permute L c n _ y _
  simp_rw [hs]
  exact Equiv.sum_comp (Tuple.sort (α := ℝᵒᵈ) y) (fun j =>
    conj (symmetricExtension L c n (i.insertNth (y j) y)) * φ (y j))

/-- Distinct real coordinates coincide only on a null set in the actual
cube measure. Fubini, rather than a dimension-count premise, proves this. -/
theorem cube_ae_ne {N : ℕ} (L : ℝ) {i j : Fin (N+1)} (hij : i ≠ j) :
    ∀ᵐ x ∂cubeMeasure (N+1) L, x i ≠ x j := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij.symm
  let μ : Measure ℝ := volume.restrict (Icc 0 L)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℝ) i
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) i
  have ha : ∀ᵐ p : ℝ × (Fin N → ℝ) ∂μ.prod (Measure.pi fun _ : Fin N => μ),
      p.1 ≠ p.2 k := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · filter_upwards with t
      exact (Measure.ae_eval_ne (fun _ : Fin N => μ) k t).mono fun _ h => h.symm
    · exact (isClosed_eq (f := fun p : ℝ × (Fin N → ℝ) => p.1)
        (g := fun p => p.2 k) (by fun_prop) (by fun_prop)).measurableSet.compl
  have h := hp.quasiMeasurePreserving.ae ha
  change ∀ᵐ x ∂Measure.pi (fun _ : Fin (N+1) => μ), x i ≠ x (i.succAbove k) at h
  simpa only [cubeMeasure_eq_pi, μ] using h

/-- Almost every spectator tuple has distinct coordinates. This also covers
the simultaneous exclusion of every higher coincidence in the slice base. -/
theorem cube_ae_injective {N : ℕ} (L : ℝ) :
    ∀ᵐ x ∂cubeMeasure N L, Function.Injective x := by
  cases N with
  | zero => exact Filter.Eventually.of_forall fun _ => Function.injective_of_subsingleton _
  | succ N =>
    have h : ∀ i j : Fin (N+1), ∀ᵐ x ∂cubeMeasure (N+1) L, i ≠ j → x i ≠ x j := by
      intro i j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · exact (cube_ae_ne L hij).mono fun _ ht _ => ht
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h i)] with x hx
    intro i j he
    by_contra hij
    exact hx i j hij he

/-- Almost every finite tuple for a nonatomic coordinate measure is
injective. In particular this applies to the independent coordinates of
dy_ij, including its common coordinate. -/
theorem pi_ae_injective {I A : Type*} [Fintype I]
    [TopologicalSpace A] [T2Space A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A)
    [SigmaFinite μ] [NullSingletonClass μ] :
    ∀ᵐ x ∂Measure.pi (fun _ : I => μ), Function.Injective x := by
  have hfin (M : ℕ) : ∀ᵐ x ∂Measure.pi (fun _ : Fin M => μ), Function.Injective x := by
    cases M with
    | zero => exact Filter.Eventually.of_forall fun _ => Function.injective_of_subsingleton _
    | succ M =>
      have hne (i j : Fin (M+1)) (hij : i ≠ j) :
          ∀ᵐ x ∂Measure.pi (fun _ : Fin (M+1) => μ), x i ≠ x j := by
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij.symm
        have ha : ∀ᵐ p : A × (Fin M → A) ∂μ.prod (Measure.pi fun _ : Fin M => μ),
            p.1 ≠ p.2 k := by
          apply (Measure.ae_prod_iff_ae_ae ?_).2
          · filter_upwards with t
            exact (Measure.ae_eval_ne (fun _ : Fin M => μ) k t).mono fun _ h => h.symm
          · exact (isClosed_eq (f := fun p : A × (Fin M → A) => p.1)
              (g := fun p => p.2 k) (by fun_prop) (by fun_prop)).measurableSet.compl
        exact (measurePreserving_piFinSuccAbove (fun _ : Fin (M+1) => μ) i).quasiMeasurePreserving.ae ha
      have h (i j : Fin (M+1)) :
          ∀ᵐ x ∂Measure.pi (fun _ : Fin (M+1) => μ), i ≠ j → x i ≠ x j := by
        by_cases hij : i = j
        · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
        · exact (hne i j hij).mono fun _ ht _ => ht
      filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h i)] with x hx
      intro i j he
      by_contra hij
      exact hx i j hij he
  let e := (Fintype.equivFin I).symm
  have h := (measurePreserving_piCongrLeft (fun _ : I => μ) e).symm.quasiMeasurePreserving.ae
    (hfin (Fintype.card I))
  filter_upwards [h] with x hx
  intro i j he
  apply e.symm.injective
  apply hx
  simpa [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, e] using he

/-- Higher coincidences on a collision face are null for exactly the
printed common-coordinate times spectator measure dy_ij. No Euclidean
hypersurface measure or square-root-of-two factor occurs. -/
theorem dyij_ae_no_higher_coincidence {L : ℝ} [Fact (0 < L)] {N : ℕ}
    (i j : Fin N) : ∀ᵐ p ∂dyij (L := L) i j,
      (∀ r, p.2 r ≠ p.1) ∧ Function.Injective p.2 := by
  let : NullSingletonClass (volume : Measure (AddCircle L)) := ⟨fun x => by
    have h := AddCircle.volume_closedBall (T := L) (x := x) 0
    simpa only [Metric.closedBall_zero, mul_zero, min_eq_right (Fact.out : 0 < L).le,
      ENNReal.ofReal_zero] using h⟩
  have h := (measurePreserving_unitSumPositions L (QuantumNLS.CollisionTrace.Rest N i j)).symm.quasiMeasurePreserving.ae
      (pi_ae_injective (I := DCoord i j) (volume : Measure (AddCircle L)))
  filter_upwards [h] with p hp
  constructor
  · intro r he
    have he' : (unitSumPositions L (QuantumNLS.CollisionTrace.Rest N i j)).symm p (.inr r) =
        (unitSumPositions L (QuantumNLS.CollisionTrace.Rest N i j)).symm p (.inl ()) := he
    exact Sum.inr_ne_inl (hp he')
  · intro r s he
    have he' : (unitSumPositions L (QuantumNLS.CollisionTrace.Rest N i j)).symm p (.inr r) =
        (unitSumPositions L (QuantumNLS.CollisionTrace.Rest N i j)).symm p (.inr s) := he
    exact Sum.inr.inj (hp he')

/-- The final operator step, explicitly conditional on the still-separate
global weak identity. It specializes the accepted variational theorem to
the actual unnormalized Bethe H¹ vector and the literal source energy.
This implication alone does not establish that its hypothesis holds. -/
theorem Hop_eigen_of_weak_identity {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (hweak : ∀ φ : ContactOperator.VSym L (N+1),
      ContactForm.q c φ.1 (waveH1 (L := L) hc hn) =
        (energy L c n : ℂ) * ⟪φ.1.val, (waveH1 (L := L) hc hn).val⟫_ℂ) :
    ∃ h : (ContactOperator.valSym (waveH1Sym (L := L) hc hn) : ContactOperator.SymL2 L (N+1)) ∈
        (ContactOperator.Hop c hc.le).domain,
      ContactOperator.Hop c hc.le ⟨ContactOperator.valSym (waveH1Sym hc hn), h⟩ =
        (energy L c n : ℂ) • ContactOperator.valSym (waveH1Sym hc hn) := by
  apply ContactOperator.mem_domain_of_variational hc.le (waveH1Sym hc hn)
    ((energy L c n : ℂ) • ContactOperator.valSym (waveH1Sym hc hn))
  intro φ
  change ContactForm.q c φ.1 (waveH1 (L := L) hc hn) =
    ⟪φ.1.val, (energy L c n : ℂ) • (waveH1 (L := L) hc hn).val⟫_ℂ
  rw [inner_smul_right]
  exact hweak φ

end QuantumNLS.BetheEigen

#print axioms QuantumNLS.BetheEigen.energy
#print axioms QuantumNLS.BetheEigen.ansatz_insert_hasDerivAt
#print axioms QuantumNLS.BetheEigen.ansatzPartial_insert_hasDerivAt
#print axioms QuantumNLS.BetheEigen.ansatzPartial_outer_faces
#print axioms QuantumNLS.BetheEigen.insert_wall_eq
#print axioms QuantumNLS.BetheEigen.insertion_gradient_jump
#print axioms QuantumNLS.BetheEigen.boundary_telescope
#print axioms QuantumNLS.BetheEigen.insertion_boundary_sum
#print axioms QuantumNLS.BetheEigen.antitone_insert
#print axioms QuantumNLS.BetheEigen.antitone_insert_of_bounds
#print axioms QuantumNLS.BetheEigen.insertionPermutation
#print axioms QuantumNLS.BetheEigen.insert_eq_cons_permute
#print axioms QuantumNLS.BetheEigen.symmetricExtension_insertion_chart
#print axioms QuantumNLS.BetheEigen.gradient_insertion_chart
#print axioms QuantumNLS.BetheEigen.insertion_second_integrationByParts
#print axioms QuantumNLS.BetheEigen.sum_insertion_second_integrationByParts
#print axioms QuantumNLS.BetheEigen.insertion_interval_order
#print axioms QuantumNLS.BetheEigen.integral_insertion_partition
#print axioms QuantumNLS.BetheEigen.sorted_slice_second_integrationByParts
#print axioms QuantumNLS.BetheEigen.gradient_permute
#print axioms QuantumNLS.BetheEigen.insertionPermutation_self
#print axioms QuantumNLS.BetheEigen.gradient_insert
#print axioms QuantumNLS.BetheEigen.gradient_cons_permute
#print axioms QuantumNLS.BetheEigen.slice_second_integrationByParts
#print axioms QuantumNLS.BetheEigen.cube_ae_ne
#print axioms QuantumNLS.BetheEigen.cube_ae_injective
#print axioms QuantumNLS.BetheEigen.pi_ae_injective
#print axioms QuantumNLS.BetheEigen.dyij_ae_no_higher_coincidence
#print axioms QuantumNLS.BetheEigen.Hop_eigen_of_weak_identity
