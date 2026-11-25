import NlsGge.Hierarchy.ALBoundaryKappa38
import NlsGge.Analysis.H1Fourier
import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Spectral.ActualComplexZsDysonVolterraWithinODEV3
import NlsGge.Spectral.ActualComplexZsDysonRepresentativeInvarianceV1
import NlsGge.Spectral.ActualComplexZsDysonIntegralEquationContinuousPotentialV6

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Filter Topology Set MeasureTheory
open NlsGge.SpectralFoundations NlsGge.Pilot NlsGge.Analysis NlsGge.Schur

/-! ### A matrix norm on `2 × 2` complex matrices (maximal absolute row sum) -/

/-- Maximal absolute row sum of a `2 × 2` complex matrix. -/
def alNm38 (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  max (‖A 0 0‖ + ‖A 0 1‖) (‖A 1 0‖ + ‖A 1 1‖)

theorem alNm38_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ alNm38 A :=
  le_max_of_le_left (by positivity)

theorem alNm38_entry_le (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : ‖A i j‖ ≤ alNm38 A := by
  unfold alNm38
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one]
  · exact le_max_of_le_left (by linarith [norm_nonneg (A 0 1)])
  · exact le_max_of_le_left (by linarith [norm_nonneg (A 0 0)])
  · exact le_max_of_le_right (by linarith [norm_nonneg (A 1 1)])
  · exact le_max_of_le_right (by linarith [norm_nonneg (A 1 0)])

theorem alNm38_le_of_entries {A : Matrix (Fin 2) (Fin 2) ℂ} {b : ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ b) : alNm38 A ≤ 2 * b := by
  unfold alNm38
  apply max_le
  · linarith [h 0 0, h 0 1]
  · linarith [h 1 0, h 1 1]

theorem alNm38_add_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    alNm38 (A + B) ≤ alNm38 A + alNm38 B := by
  have hA := alNm38_entry_le A
  have hB := alNm38_entry_le B
  unfold alNm38
  apply max_le
  · simp only [Matrix.add_apply]
    have h1 := norm_add_le (A 0 0) (B 0 0)
    have h2 := norm_add_le (A 0 1) (B 0 1)
    have := le_max_left (‖A 0 0‖ + ‖A 0 1‖) (‖A 1 0‖ + ‖A 1 1‖)
    have := le_max_left (‖B 0 0‖ + ‖B 0 1‖) (‖B 1 0‖ + ‖B 1 1‖)
    linarith
  · simp only [Matrix.add_apply]
    have h1 := norm_add_le (A 1 0) (B 1 0)
    have h2 := norm_add_le (A 1 1) (B 1 1)
    have := le_max_right (‖A 0 0‖ + ‖A 0 1‖) (‖A 1 0‖ + ‖A 1 1‖)
    have := le_max_right (‖B 0 0‖ + ‖B 0 1‖) (‖B 1 0‖ + ‖B 1 1‖)
    linarith

theorem alNm38_neg (A : Matrix (Fin 2) (Fin 2) ℂ) : alNm38 (-A) = alNm38 A := by
  simp [alNm38]

theorem alNm38_sub_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    alNm38 (A - B) ≤ alNm38 A + alNm38 B := by
  rw [sub_eq_add_neg]
  exact (alNm38_add_le _ _).trans (by rw [alNm38_neg])

theorem alNm38_smul (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    alNm38 (c • A) = ‖c‖ * alNm38 A := by
  simp only [alNm38, Matrix.smul_apply, smul_eq_mul, norm_mul]
  rw [← mul_add, ← mul_add, mul_max_of_nonneg _ _ (norm_nonneg c)]

theorem alNm38_mul_le (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    alNm38 (A * B) ≤ alNm38 A * alNm38 B := by
  have hB0 : ‖B 0 0‖ + ‖B 0 1‖ ≤ alNm38 B := le_max_left _ _
  have hB1 : ‖B 1 0‖ + ‖B 1 1‖ ≤ alNm38 B := le_max_right _ _
  have hn := alNm38_nonneg B
  have row : ∀ i : Fin 2, ‖(A * B) i 0‖ + ‖(A * B) i 1‖ ≤
      (‖A i 0‖ + ‖A i 1‖) * alNm38 B := by
    intro i
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    have e1 := norm_add_le (A i 0 * B 0 0) (A i 1 * B 1 0)
    have e2 := norm_add_le (A i 0 * B 0 1) (A i 1 * B 1 1)
    simp only [norm_mul] at e1 e2
    have a0 := norm_nonneg (A i 0)
    have a1 := norm_nonneg (A i 1)
    nlinarith [mul_le_mul_of_nonneg_left hB0 a0, mul_le_mul_of_nonneg_left hB1 a1]
  have hA0 : ‖A 0 0‖ + ‖A 0 1‖ ≤ alNm38 A := le_max_left _ _
  have hA1 : ‖A 1 0‖ + ‖A 1 1‖ ≤ alNm38 A := le_max_right _ _
  unfold alNm38 at *
  apply max_le
  · exact (row 0).trans (mul_le_mul_of_nonneg_right hA0 hn)
  · exact (row 1).trans (mul_le_mul_of_nonneg_right hA1 hn)

theorem alNm38_one : alNm38 (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  simp [alNm38]

theorem norm_trace_le_alNm38 (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖Matrix.trace A‖ ≤ 2 * alNm38 A := by
  rw [Matrix.trace_fin_two]
  have := norm_add_le (A 0 0) (A 1 1)
  have := alNm38_entry_le A 0 0
  have := alNm38_entry_le A 1 1
  linarith

/-! ### One-step expansion of the transfer matrix -/

theorem alSqrtInv_bounds38 {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) :
    1 ≤ (Real.sqrt (1 - r))⁻¹ ∧ (Real.sqrt (1 - r))⁻¹ ≤ 1 + r := by
  have hq : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.mpr (by linarith)
  have hq1 : Real.sqrt (1 - r) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  refine ⟨?_, ?_⟩
  · exact one_le_inv_iff₀.mpr ⟨hq, hq1⟩
  · have : (1 + r)⁻¹ ≤ Real.sqrt (1 - r) := by
      apply Real.le_sqrt_of_sq_le
      rw [inv_pow]
      refine (inv_le_iff_one_le_mul₀' (by positivity)).2 ?_
      nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
    calc (Real.sqrt (1 - r))⁻¹ ≤ ((1 + r)⁻¹)⁻¹ := inv_anti₀ (by positivity) this
      _ = 1 + r := inv_inv _

theorem alTransfer38_expansion {R K h lam : ℝ} {w : ℂ} (hR : 0 ≤ R) (hh : 0 < h)
    (hhR : h * R ≤ 1) (hhK : h * K ≤ 1 / 2) (hlam : |lam| ≤ R) (hw : ‖w‖ ≤ K) :
    alNm38 (alTransfer38 ((h : ℂ) * w) (Complex.exp ((h * lam : ℝ) * Complex.I)) - 1 -
      (h : ℂ) • !![Complex.I * lam, w; star w, -(Complex.I * lam)]) ≤
      2 * (K ^ 2 + R ^ 2) * h ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg w).trans hw
  set z : ℂ := Complex.exp ((h * lam : ℝ) * Complex.I) with hz
  have hzn : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hzi : z⁻¹ = Complex.exp (-((h * lam : ℝ) * Complex.I)) := by rw [hz, Complex.exp_neg]
  set r : ℝ := ‖(h : ℂ) * w‖ ^ 2 with hr
  have hrn : ‖(h : ℂ) * w‖ ≤ h * K := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left hw hh.le
  have hr0 : 0 ≤ r := by positivity
  have hrK : r ≤ h ^ 2 * K ^ 2 := by
    rw [hr]
    have := pow_le_pow_left₀ (norm_nonneg _) hrn 2
    nlinarith
  have hr1 : r ≤ 1 / 2 := by
    have : r ≤ (h * K) ^ 2 := by rw [hr]; exact pow_le_pow_left₀ (norm_nonneg _) hrn 2
    nlinarith [mul_nonneg hh.le hK0]
  obtain ⟨hs1, hs2⟩ := alSqrtInv_bounds38 hr0 hr1
  set s : ℝ := (Real.sqrt (1 - r))⁻¹ with hs
  have hsc : ((Real.sqrt (1 - ‖(h : ℂ) * w‖ ^ 2) : ℝ) : ℂ)⁻¹ = (s : ℂ) := by
    rw [hs, hr]; push_cast; rfl
  have hθ : ‖((h * lam : ℝ) : ℂ) * Complex.I‖ ≤ h * R := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left hlam hh.le
  have hθ2 : ‖((h * lam : ℝ) : ℂ) * Complex.I‖ ^ 2 ≤ (h * R) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hθ 2
  have e1 : ‖z - 1 - ((h * lam : ℝ) : ℂ) * Complex.I‖ ≤ (h * R) ^ 2 :=
    (Complex.norm_exp_sub_one_sub_id_le (hθ.trans hhR)).trans hθ2
  have hθ' : ‖-(((h * lam : ℝ) : ℂ) * Complex.I)‖ ≤ h * R := by rwa [norm_neg]
  have e2 : ‖z⁻¹ - 1 - (-(((h * lam : ℝ) : ℂ) * Complex.I))‖ ≤ (h * R) ^ 2 := by
    rw [hzi]
    exact (Complex.norm_exp_sub_one_sub_id_le (hθ'.trans hhR)).trans
      ((pow_le_pow_left₀ (norm_nonneg _) hθ' 2))
  have hzi_n : ‖z⁻¹‖ = 1 := by rw [norm_inv, hzn, inv_one]
  have hsm : ‖(s : ℂ) - 1‖ ≤ r := by
    rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  -- diagonal entries
  have d00 : ‖(s : ℂ) * z - 1 - (h : ℂ) * (Complex.I * lam)‖ ≤ h ^ 2 * K ^ 2 + (h * R) ^ 2 := by
    have : (s : ℂ) * z - 1 - (h : ℂ) * (Complex.I * lam) =
        ((s : ℂ) - 1) * z + (z - 1 - ((h * lam : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hzn, mul_one]
    linarith
  have d11 : ‖(s : ℂ) * z⁻¹ - 1 - (h : ℂ) * (-(Complex.I * lam))‖ ≤
      h ^ 2 * K ^ 2 + (h * R) ^ 2 := by
    have : (s : ℂ) * z⁻¹ - 1 - (h : ℂ) * (-(Complex.I * lam)) =
        ((s : ℂ) - 1) * z⁻¹ + (z⁻¹ - 1 - (-(((h * lam : ℝ) : ℂ) * Complex.I))) := by
      push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hzi_n, mul_one]
    linarith
  have o01 : ‖(s : ℂ) * ((h : ℂ) * w) - (h : ℂ) * w‖ ≤ h ^ 2 * K ^ 2 := by
    have : (s : ℂ) * ((h : ℂ) * w) - (h : ℂ) * w = ((s : ℂ) - 1) * ((h : ℂ) * w) := by ring
    rw [this, norm_mul]
    have h3 : ‖(s : ℂ) - 1‖ * ‖(h : ℂ) * w‖ ≤ r * 1 := by
      apply mul_le_mul hsm _ (norm_nonneg _) hr0
      have := hrn.trans (by nlinarith : h * K ≤ 1)
      exact this
    nlinarith
  have o10 : ‖(s : ℂ) * star ((h : ℂ) * w) - (h : ℂ) * star w‖ ≤ h ^ 2 * K ^ 2 := by
    have hst : star ((h : ℂ) * w) = (h : ℂ) * star w := by
      simp [star_mul']
    rw [hst]
    have : (s : ℂ) * ((h : ℂ) * star w) - (h : ℂ) * star w =
        ((s : ℂ) - 1) * ((h : ℂ) * star w) := by ring
    rw [this, norm_mul]
    have hn' : ‖(h : ℂ) * star w‖ ≤ 1 := by
      have : ‖(h : ℂ) * star w‖ = ‖(h : ℂ) * w‖ := by simp [norm_mul]
      rw [this]; exact hrn.trans (by nlinarith)
    have h3 : ‖(s : ℂ) - 1‖ * ‖(h : ℂ) * star w‖ ≤ r * 1 :=
      mul_le_mul hsm hn' (norm_nonneg _) hr0
    nlinarith
  have hA : alTransfer38 ((h : ℂ) * w) z = (s : ℂ) • !![z, (h : ℂ) * w; star ((h : ℂ) * w), z⁻¹] := by
    unfold alTransfer38
    rw [hsc]
  rw [hA]
  have E00 : ((s : ℂ) • !![z, (h : ℂ) * w; star ((h : ℂ) * w), z⁻¹] - 1 -
      (h : ℂ) • !![Complex.I * lam, w; star w, -(Complex.I * lam)]) 0 0 =
      (s : ℂ) * z - 1 - (h : ℂ) * (Complex.I * lam) := by simp
  have E01 : ((s : ℂ) • !![z, (h : ℂ) * w; star ((h : ℂ) * w), z⁻¹] - 1 -
      (h : ℂ) • !![Complex.I * lam, w; star w, -(Complex.I * lam)]) 0 1 =
      (s : ℂ) * ((h : ℂ) * w) - (h : ℂ) * w := by simp
  have E10 : ((s : ℂ) • !![z, (h : ℂ) * w; star ((h : ℂ) * w), z⁻¹] - 1 -
      (h : ℂ) • !![Complex.I * lam, w; star w, -(Complex.I * lam)]) 1 0 =
      (s : ℂ) * star ((h : ℂ) * w) - (h : ℂ) * star w := by simp
  have E11 : ((s : ℂ) • !![z, (h : ℂ) * w; star ((h : ℂ) * w), z⁻¹] - 1 -
      (h : ℂ) • !![Complex.I * lam, w; star w, -(Complex.I * lam)]) 1 1 =
      (s : ℂ) * z⁻¹ - 1 - (h : ℂ) * (-(Complex.I * lam)) := by simp
  unfold alNm38
  rw [E00, E01, E10, E11]
  have c1 : (h * R) ^ 2 = h ^ 2 * R ^ 2 := by ring
  have p1 : 0 ≤ h ^ 2 * R ^ 2 := by positivity
  have p2 : 0 ≤ h ^ 2 * K ^ 2 := by positivity
  apply max_le
  · linarith [d00, o01]
  · linarith [d11, o10]

/-! ### Telescoping estimate for Euler products -/

theorem alEuler_bound38 (L : ℕ) (h c δ : ℝ) (hL : (L : ℝ) * h = 1) (hh : 0 < h) (hc : 0 ≤ c)
    (hδ : 0 ≤ δ) (E Φ A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hE0 : E 0 = Φ 0)
    (hE : ∀ k, E (k + 1) = A k * E k)
    (hA : ∀ k < L, alNm38 (A k) ≤ 1 + h * c)
    (hε : ∀ k < L, alNm38 (A k * Φ k - Φ (k + 1)) ≤ h * δ) :
    alNm38 (E L - Φ L) ≤ Real.exp c * δ := by
  have key : ∀ k ≤ L, alNm38 (E k - Φ k) ≤ k * h * δ * (1 + h * c) ^ k := by
    intro k
    induction k with
    | zero => intro _; simp [hE0, alNm38]
    | succ k ih =>
      intro hk
      have hk' : k < L := hk
      have ih' := ih hk'.le
      have e : E (k + 1) - Φ (k + 1) = A k * (E k - Φ k) + (A k * Φ k - Φ (k + 1)) := by
        rw [hE k]; noncomm_ring
      rw [e]
      have h1 := alNm38_add_le (A k * (E k - Φ k)) (A k * Φ k - Φ (k + 1))
      have h2 := alNm38_mul_le (A k) (E k - Φ k)
      have h3 := hA k hk'
      have h4 := hε k hk'
      have hp : 1 ≤ (1 + h * c) ^ (k + 1) := one_le_pow₀ (by nlinarith [mul_nonneg hh.le hc])
      have hq : 0 ≤ (1 + h * c) ^ k := by positivity
      have hnn := alNm38_nonneg (E k - Φ k)
      have h5 : alNm38 (A k) * alNm38 (E k - Φ k) ≤
          (1 + h * c) * (k * h * δ * (1 + h * c) ^ k) :=
        mul_le_mul h3 ih' hnn (by positivity)
      have h6 : h * δ ≤ h * δ * (1 + h * c) ^ (k + 1) := by
        have := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ h * δ)
        linarith
      have h7 : (1 + h * c) * (k * h * δ * (1 + h * c) ^ k) =
          k * h * δ * (1 + h * c) ^ (k + 1) := by ring
      push_cast
      nlinarith [h1, h2, h4, h5, h6, h7]
  have := key L le_rfl
  refine this.trans ?_
  have h1 : (1 + h * c) ^ L ≤ Real.exp c := by
    calc (1 + h * c) ^ L ≤ (Real.exp (h * c)) ^ L := by
          apply pow_le_pow_left₀ (by nlinarith [mul_nonneg hh.le hc])
          linarith [Real.add_one_le_exp (h * c)]
      _ = Real.exp c := by rw [← Real.exp_nat_mul]; congr 1; nlinarith
  calc (L : ℝ) * h * δ * (1 + h * c) ^ L = δ * (1 + h * c) ^ L := by rw [hL]; ring
    _ ≤ δ * Real.exp c := mul_le_mul_of_nonneg_left h1 hδ
    _ = Real.exp c * δ := mul_comm _ _

/-! ### One-step error of a Volterra fundamental matrix against an Euler step -/

section Volterra

variable (B Φ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)

theorem volterra_diff38
    (hint : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, Φ t i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
      ∫ s in (0 : ℝ)..t, (B s * Φ s) i j)
    (hcont : ∀ i j, ContinuousOn (fun s => (B s * Φ s) i j) (Icc (0 : ℝ) 1))
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ Icc (0 : ℝ) 1) (h₂ : t₂ ∈ Icc (0 : ℝ) 1) (h12 : t₁ ≤ t₂) (i j : Fin 2) :
    Φ t₂ i j - Φ t₁ i j = ∫ s in t₁..t₂, (B s * Φ s) i j := by
  have i01 : IntervalIntegrable (fun s => (B s * Φ s) i j) volume 0 t₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h₁.1]
    exact (hcont i j).mono (Icc_subset_Icc le_rfl h₁.2)
  have i12 : IntervalIntegrable (fun s => (B s * Φ s) i j) volume t₁ t₂ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h12]
    exact (hcont i j).mono (Icc_subset_Icc h₁.1 h₂.2)
  rw [hint t₁ h₁ i j, hint t₂ h₂ i j, ← intervalIntegral.integral_add_adjacent_intervals i01 i12]
  ring

theorem volterra_increment_bound38 (Φb Bb : ℝ)
    (hint : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, Φ t i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
      ∫ s in (0 : ℝ)..t, (B s * Φ s) i j)
    (hcont : ∀ i j, ContinuousOn (fun s => (B s * Φ s) i j) (Icc (0 : ℝ) 1))
    (hΦb : ∀ t ∈ Icc (0 : ℝ) 1, alNm38 (Φ t) ≤ Φb) (hBb : ∀ s ∈ Icc (0 : ℝ) 1, alNm38 (B s) ≤ Bb)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ Icc (0 : ℝ) 1) (h₂ : t₂ ∈ Icc (0 : ℝ) 1) (h12 : t₁ ≤ t₂) :
    alNm38 (Φ t₂ - Φ t₁) ≤ 2 * (Bb * Φb * (t₂ - t₁)) := by
  apply alNm38_le_of_entries
  intro i j
  have e := volterra_diff38 B Φ hint hcont h₁ h₂ h12 i j
  have : (Φ t₂ - Φ t₁) i j = ∫ s in t₁..t₂, (B s * Φ s) i j := by
    rw [Matrix.sub_apply]; exact e
  rw [this]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₁) (b := t₂)
    (f := fun s => (B s * Φ s) i j) (C := Bb * Φb) (by
      intro s hs
      rw [uIoc_of_le h12] at hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨h₁.1.trans hs.1.le, hs.2.trans h₂.2⟩
      refine (alNm38_entry_le _ i j).trans ((alNm38_mul_le _ _).trans ?_)
      exact mul_le_mul (hBb s hs') (hΦb s hs') (alNm38_nonneg _)
        ((alNm38_nonneg _).trans (hBb s hs')))
  rw [abs_of_nonneg (by linarith)] at this
  linarith

theorem volterra_step_error38 (Φb Bb η : ℝ) (hΦb0 : 0 ≤ Φb) (hBb0 : 0 ≤ Bb)
    (hint : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, Φ t i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
      ∫ s in (0 : ℝ)..t, (B s * Φ s) i j)
    (hcont : ∀ i j, ContinuousOn (fun s => (B s * Φ s) i j) (Icc (0 : ℝ) 1))
    (hΦb : ∀ t ∈ Icc (0 : ℝ) 1, alNm38 (Φ t) ≤ Φb) (hBb : ∀ s ∈ Icc (0 : ℝ) 1, alNm38 (B s) ≤ Bb)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ Icc (0 : ℝ) 1) (h₂ : t₂ ∈ Icc (0 : ℝ) 1) (h12 : t₁ ≤ t₂)
    (A G : Matrix (Fin 2) (Fin 2) ℂ) (hη : ∀ s ∈ Icc t₁ t₂, alNm38 (G - B s) ≤ η) :
    alNm38 (A * Φ t₁ - Φ t₂) ≤
      alNm38 (A - 1 - ((t₂ - t₁ : ℝ) : ℂ) • G) * Φb +
        2 * ((t₂ - t₁) * (η * Φb + Bb * (2 * (Bb * Φb * (t₂ - t₁))))) := by
  set X : Matrix (Fin 2) (Fin 2) ℂ := A - 1 - ((t₂ - t₁ : ℝ) : ℂ) • G with hX
  have hsplit : A * Φ t₁ - Φ t₂ = X * Φ t₁ + (A * Φ t₁ - Φ t₂ - X * Φ t₁) := by abel
  set hh : ℝ := t₂ - t₁ with hhd
  have hh0 : 0 ≤ hh := by rw [hhd]; linarith
  have hI : ∀ i j, ‖(A * Φ t₁ - Φ t₂ - X * Φ t₁) i j‖ ≤
      hh * (η * Φb + Bb * (2 * (Bb * Φb * hh))) := by
    intro i j
    have hmat : A * Φ t₁ - Φ t₂ - X * Φ t₁ = (hh : ℂ) • (G * Φ t₁) - (Φ t₂ - Φ t₁) := by
      rw [hX]; noncomm_ring
    have e1 : ((hh : ℂ) • (G * Φ t₁) - (Φ t₂ - Φ t₁)) i j =
        ∫ s in t₁..t₂, ((G * Φ t₁) i j - (B s * Φ s) i j) := by
      have hi : IntervalIntegrable (fun s => (B s * Φ s) i j) volume t₁ t₂ := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le h12]
        exact (hcont i j).mono (Icc_subset_Icc h₁.1 h₂.2)
      rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
        intervalIntegral.integral_const, ← volterra_diff38 B Φ hint hcont h₁ h₂ h12 i j]
      simp [hhd]
    rw [hmat, e1]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₁) (b := t₂)
      (f := fun s => (G * Φ t₁) i j - (B s * Φ s) i j)
      (C := η * Φb + Bb * (2 * (Bb * Φb * hh))) (by
        intro s hs
        rw [uIoc_of_le h12] at hs
        have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨h₁.1.trans hs.1.le, hs.2.trans h₂.2⟩
        have hs'' : s ∈ Icc t₁ t₂ := ⟨hs.1.le, hs.2⟩
        have hid : G * Φ t₁ - B s * Φ s = (G - B s) * Φ t₁ + B s * (Φ t₁ - Φ s) := by
          noncomm_ring
        have hinc := volterra_increment_bound38 B Φ Φb Bb hint hcont hΦb hBb h₁ hs' hs.1.le
        have hneg : alNm38 (Φ t₁ - Φ s) = alNm38 (Φ s - Φ t₁) := by
          rw [← alNm38_neg, neg_sub]
        have hs1 : alNm38 (Φ s - Φ t₁) ≤ 2 * (Bb * Φb * hh) := by
          refine hinc.trans ?_
          have : s - t₁ ≤ hh := by rw [hhd]; linarith [hs.2]
          nlinarith [mul_nonneg hBb0 hΦb0]
        have e : (G * Φ t₁ - B s * Φ s) i j = ((G - B s) * Φ t₁ + B s * (Φ t₁ - Φ s)) i j := by
          rw [hid]
        rw [← Matrix.sub_apply, e]
        refine (alNm38_entry_le _ i j).trans ((alNm38_add_le _ _).trans ?_)
        have m1 := alNm38_mul_le (G - B s) (Φ t₁)
        have m2 := alNm38_mul_le (B s) (Φ t₁ - Φ s)
        have a1 : alNm38 (G - B s) * alNm38 (Φ t₁) ≤ η * Φb :=
          mul_le_mul (hη s hs'') (hΦb t₁ h₁) (alNm38_nonneg _) ((alNm38_nonneg _).trans (hη s hs''))
        have a2 : alNm38 (B s) * alNm38 (Φ t₁ - Φ s) ≤ Bb * (2 * (Bb * Φb * hh)) :=
          mul_le_mul (hBb s hs') (hneg ▸ hs1) (alNm38_nonneg _) hBb0
        linarith)
    rw [abs_of_nonneg hh0] at this
    linarith
  have hY := alNm38_le_of_entries hI
  have hXΦ := alNm38_mul_le X (Φ t₁)
  have hXb : alNm38 X * alNm38 (Φ t₁) ≤ alNm38 X * Φb :=
    mul_le_mul_of_nonneg_left (hΦb t₁ h₁) (alNm38_nonneg _)
  rw [hsplit]
  refine (alNm38_add_le _ _).trans ?_
  linarith

end Volterra

/-! ### Facts about the Dyson fundamental matrix of a continuous potential -/

theorem alDyson_entry_bound38 {U : ℝ → ℂ} {z : ℂ} {R C : ℝ} (hz : ‖z‖ ≤ R) (hR : 0 ≤ R)
    (hC : 0 ≤ C) (hUb : ∀ s ∈ Icc (0 : ℝ) 2, ‖U s‖ ≤ C) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (i j : Fin 2) :
    ‖actualComplexZsDysonTsum U z t i j‖ ≤ Real.exp (2 * (R + C)) := by
  have hs : HasSum (fun n : ℕ => (2 * (R + C)) ^ n / (n.factorial : ℝ))
      (Real.exp (2 * (R + C))) := by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (2 * (R + C))
    rwa [← Real.exp_eq_exp_ℝ] at this
  unfold actualComplexZsDysonTsum
  refine tsum_of_norm_bounded hs (fun n => ?_)
  have := actualComplexZsDysonTerm_entry_factorial_bound U z R C hz hR hUb hC n t
    ⟨ht.1, ht.2.trans (by norm_num)⟩ i j
  refine this.trans ?_
  have h1 : t ^ n ≤ 1 := pow_le_one₀ ht.1 ht.2
  have h2 : 0 ≤ (2 * (R + C)) ^ n / (n.factorial : ℝ) := by positivity
  nlinarith

theorem alDyson_facts38 {U : ℝ → ℂ} (hUc : ContinuousOn U (Icc (0 : ℝ) 2)) {z : ℂ} {R C : ℝ}
    (hz : ‖z‖ ≤ R) (hR : 0 ≤ R) (hC : 0 ≤ C) (hUb : ∀ s ∈ Icc (0 : ℝ) 2, ‖U s‖ ≤ C) :
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, actualComplexZsDysonTsum U z t i j =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i j + ∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex U z s * actualComplexZsDysonTsum U z s) i j) ∧
    (∀ i j, ContinuousOn (fun s => (zsCoefficientComplex U z s * actualComplexZsDysonTsum U z s) i j)
      (Icc (0 : ℝ) 1)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, alNm38 (actualComplexZsDysonTsum U z t) ≤ 2 * Real.exp (2 * (R + C))) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, alNm38 (zsCoefficientComplex U z s) ≤ R + C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht i j
    exact actualComplexZsDysonTsum_integral_equation_of_continuousOn U hUc z R C hz hR hC hUb t
      ⟨ht.1, ht.2.trans (by norm_num)⟩ i j
  · intro i j
    have h2 : ∀ k, ContinuousOn (fun s => zsCoefficientComplex U z s i k) (Icc (0 : ℝ) 1) :=
      fun k => continuousOn_zsCoefficientComplex_entry U z 1 (by norm_num) hUc i k
    have h3 : ∀ k, ContinuousOn (fun s => actualComplexZsDysonTsum U z s k j) (Icc (0 : ℝ) 1) :=
      fun k => (continuousOn_actualComplexZsDysonTsum_entry_of_continuousOn U z hUc k j).mono
        (Icc_subset_Icc le_rfl (by norm_num))
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact ((h2 0).mul (h3 0)).add ((h2 1).mul (h3 1))
  · intro t ht
    have := alNm38_le_of_entries (A := actualComplexZsDysonTsum U z t)
      (b := Real.exp (2 * (R + C))) (fun i j => alDyson_entry_bound38 hz hR hC hUb ht i j)
    exact this
  · intro s hs
    have hs2 : s ∈ Icc (0 : ℝ) 2 := ⟨hs.1, hs.2.trans (by norm_num)⟩
    have := hUb s hs2
    unfold alNm38
    simp only [zsCoefficientComplex, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.head_fin_const, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_star]
    apply max_le <;> linarith

/-! ### Lattice sampling, the lattice gap height, and phase invariance -/

/-- The lattice field `α_j = h f(jh)`, `h = 1/L`, `j ∈ ZMod L` (read through `ZMod.val`). -/
def alSampleField38 (L : ℕ) (f : ℝ → ℂ) : ZMod L → ℂ :=
  fun j => (((1 : ℝ) / L : ℝ) : ℂ) * f ((j.val : ℝ) * ((1 : ℝ) / L))

/-- The lattice gap height `v_h(λ) = arcosh (max 1 |½ tr M(e^{ihλ})|)` with `h = 1/L`
(paper/v2.tex l.2305-2307, via `D:eq:kappa` and `Lh = 1`). -/
def alGapHeight38 (L : ℕ) (f : ℝ → ℂ) (lam : ℝ) : ℝ :=
  Real.arcosh (max 1 ‖Matrix.trace (alMonodromy38 (alSampleField38 L f)
    (Complex.exp ((((1 : ℝ) / L * lam : ℝ) : ℂ) * Complex.I))) / 2‖)

theorem alGapHeight38_eq_kappa {L : ℕ} (hL : L ≠ 0) (f : ℝ → ℂ) (lam : ℝ) :
    alGapHeight38 L f lam = (L : ℝ) * alKappa38 (alSampleField38 L f) ((1 : ℝ) / L * lam) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  unfold alGapHeight38 alKappa38
  rw [← mul_assoc, mul_one_div_cancel hL', one_mul]

theorem alTransfer38_I_mul (a z : ℂ) {d : ℂ} (hd : d * d = Complex.I) :
    alTransfer38 (Complex.I * a) z =
      !![d, 0; 0, d⁻¹] * alTransfer38 a z * !![d⁻¹, 0; 0, d] := by
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hd; exact Complex.I_ne_zero (by simpa using hd.symm)
  have hn : ‖Complex.I * a‖ = ‖a‖ := by simp
  unfold alTransfer38
  rw [hn]
  generalize ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ)⁻¹ = σ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · rw [← hd]; field_simp
  · rw [← hd]; field_simp
    ring_nf
    have hd4 : d ^ 4 = -1 := by
      rw [show d ^ 4 = (d * d) * (d * d) by ring, hd]; simp
    rw [hd4]; ring
  · field_simp

theorem alPartial38_I_mul {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) {d : ℂ} (hd : d * d = Complex.I) :
    ∀ k, alPartial38 (fun j => Complex.I * α j) z k =
      !![d, 0; 0, d⁻¹] * alPartial38 α z k * !![d⁻¹, 0; 0, d] := by
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hd; exact Complex.I_ne_zero (by simpa using hd.symm)
  have hDD : !![d⁻¹, 0; 0, d] * !![d, 0; 0, d⁻¹] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd0]
  intro k
  induction k with
  | zero =>
    simp only [alPartial38]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd0]
  | succ k ih =>
    simp only [alPartial38]
    rw [alTransfer38_I_mul _ _ hd, ih]
    calc _ = !![d, 0; 0, d⁻¹] * alTransfer38 (α (k : ZMod L)) z *
          (!![d⁻¹, 0; 0, d] * !![d, 0; 0, d⁻¹]) * alPartial38 α z k * !![d⁻¹, 0; 0, d] := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hDD, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem trace_alMonodromy38_I_mul {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) :
    Matrix.trace (alMonodromy38 (fun j => Complex.I * α j) z) = Matrix.trace (alMonodromy38 α z) := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (Complex.I) (two_pos)
  have hd' : d * d = Complex.I := by rw [← hd]; ring
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hd'; exact Complex.I_ne_zero (by simpa using hd'.symm)
  have hDD : !![d⁻¹, 0; 0, d] * !![d, 0; 0, d⁻¹] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd0]
  unfold alMonodromy38
  rw [alPartial38_I_mul α z hd', Matrix.trace_mul_comm, ← Matrix.mul_assoc, hDD, Matrix.one_mul]

/-! ### Euler-product comparison of the lattice monodromy with the Dyson fundamental matrix -/

/-- The explicit error bound of the Euler-product comparison. -/
def alCompactBound38 (R C ε ω h : ℝ) : ℝ :=
  Real.exp (R + (C + 1) + 2 * ((C + 1) ^ 2 + R ^ 2)) * (2 * Real.exp (2 * (R + C))) *
    (2 * (ε + ω) + (2 * ((C + 1) ^ 2 + R ^ 2) + 4 * (R + C) ^ 2) * h)

theorem alTrace_compare38 {L : ℕ} (hL : L ≠ 0) {U Uh : ℝ → ℂ} {R C ε ω : ℝ} (hR : 0 ≤ R)
    (hC : 0 ≤ C) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hω : 0 ≤ ω)
    (hUc : ContinuousOn U (Icc (0 : ℝ) 2)) (hUb : ∀ s ∈ Icc (0 : ℝ) 2, ‖U s‖ ≤ C)
    (hUh : ∀ x ∈ Icc (0 : ℝ) 1, ‖Uh x - U x‖ ≤ ε)
    (hmod : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |x - y| ≤ 1 / (L : ℝ) → ‖U x - U y‖ ≤ ω)
    (hsmall : 1 / (L : ℝ) * (R + C + 1) ≤ 1 / 2) {lam : ℝ} (hlam : |lam| ≤ R) :
    ‖Matrix.trace (alMonodromy38 (alSampleField38 L Uh)
        (Complex.exp ((((1 : ℝ) / L * lam : ℝ) : ℂ) * Complex.I))) / 2 -
      Matrix.trace (actualComplexZsDysonTsum U (-(lam : ℂ)) 1) / 2‖ ≤
      alCompactBound38 R C ε ω (1 / (L : ℝ)) := by
  set h : ℝ := 1 / (L : ℝ) with hh
  have hL' : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  have hh0 : 0 < h := by positivity
  have hLh : (L : ℝ) * h = 1 := by rw [hh]; field_simp
  have hh1 : h ≤ 1 := by
    have : 0 ≤ R + C + 1 := by positivity
    nlinarith
  set K : ℝ := C + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set c₂ : ℝ := 2 * (K ^ 2 + R ^ 2) with hc₂
  set Φb : ℝ := 2 * Real.exp (2 * (R + C)) with hΦb
  set Bb : ℝ := R + C with hBb
  have hΦb0 : 0 ≤ Φb := by positivity
  have hBb0 : 0 ≤ Bb := by positivity
  set z : ℂ := Complex.exp ((((1 : ℝ) / L * lam : ℝ) : ℂ) * Complex.I) with hz
  set α : ZMod L → ℂ := alSampleField38 L Uh with hα
  set α' : ZMod L → ℂ := fun j => Complex.I * α j with hα'
  have hzR : ‖-(lam : ℂ)‖ ≤ R := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hlam
  obtain ⟨hint, hcont, hΦ, hB⟩ := alDyson_facts38 hUc hzR hR hC hUb
  set B : ℝ → Matrix (Fin 2) (Fin 2) ℂ := zsCoefficientComplex U (-(lam : ℂ)) with hBdef
  set Φ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := actualComplexZsDysonTsum U (-(lam : ℂ)) with hΦdef
  -- the samples
  set w : ℕ → ℂ := fun k => Complex.I * Uh ((k : ℝ) * h) with hw
  have hmem : ∀ k : ℕ, k < L → (k : ℝ) * h ∈ Icc (0 : ℝ) 1 := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    have : (k : ℝ) ≤ L := by exact_mod_cast hk.le
    nlinarith
  have hmem' : ∀ k : ℕ, k < L → ((k : ℝ) + 1) * h ∈ Icc (0 : ℝ) 1 := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    have : (k : ℝ) + 1 ≤ L := by exact_mod_cast hk
    nlinarith
  have hα'k : ∀ k : ℕ, k < L → α' (k : ZMod L) = (h : ℂ) * w k := by
    intro k hk
    have hv : ((k : ZMod L)).val = k := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
    simp only [hα', hα, alSampleField38, hv, hw, hh]
    push_cast; ring
  have hwK : ∀ k : ℕ, k < L → ‖w k‖ ≤ K := by
    intro k hk
    have hm := hmem k hk
    have h1 := hUh _ hm
    have h2 := hUb _ ⟨hm.1, hm.2.trans (by norm_num)⟩
    have : ‖Uh ((k : ℝ) * h)‖ ≤ C + 1 := by
      calc ‖Uh ((k : ℝ) * h)‖ = ‖(Uh ((k : ℝ) * h) - U ((k : ℝ) * h)) + U ((k : ℝ) * h)‖ := by
            congr 1; ring
        _ ≤ ‖Uh ((k : ℝ) * h) - U ((k : ℝ) * h)‖ + ‖U ((k : ℝ) * h)‖ := norm_add_le _ _
        _ ≤ C + 1 := by linarith
    simp only [hw, norm_mul, Complex.norm_I, one_mul]
    exact this
  -- Euler data
  set E : ℕ → Matrix (Fin 2) (Fin 2) ℂ := fun k => alPartial38 α' z k with hE
  set A : ℕ → Matrix (Fin 2) (Fin 2) ℂ := fun k => alTransfer38 (α' (k : ZMod L)) z with hA
  set Φ' : ℕ → Matrix (Fin 2) (Fin 2) ℂ := fun k => Φ ((k : ℝ) * h) with hΦ'
  set G : ℕ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun k => !![Complex.I * lam, w k; star (w k), -(Complex.I * lam)] with hG
  have hΦ0 : Φ 0 = 1 := by
    ext i j
    rw [hint 0 ⟨le_rfl, by norm_num⟩ i j]; simp
  have hE0 : E 0 = Φ' 0 := by
    simp [hE, hΦ', alPartial38, hΦ0]
  have hEs : ∀ k, E (k + 1) = A k * E k := fun k => rfl
  have hexp : ∀ k, k < L → alNm38 (A k - 1 - (h : ℂ) • G k) ≤ c₂ * h ^ 2 := by
    intro k hk
    have := alTransfer38_expansion (R := R) (K := K) (h := h) (lam := lam) (w := w k) hR hh0
      (by nlinarith [mul_nonneg hh0.le hC]) (by nlinarith) hlam (hwK k hk)
    simp only [hA, hG, hα'k k hk]
    rw [show (h : ℂ) * w k = (h : ℂ) * w k from rfl]
    convert this using 3
  have hAb : ∀ k, k < L → alNm38 (A k) ≤ 1 + h * (R + K + c₂) := by
    intro k hk
    have e : A k = 1 + ((A k - 1 - (h : ℂ) • G k) + (h : ℂ) • G k) := by abel
    have hGn : alNm38 (G k) ≤ R + K := by
      have := hwK k hk
      unfold alNm38
      simp only [hG, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, norm_mul,
        norm_neg, Complex.norm_I, one_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      apply max_le <;> linarith
    rw [e]
    refine (alNm38_add_le _ _).trans ?_
    rw [alNm38_one]
    have h1 := alNm38_add_le (A k - 1 - (h : ℂ) • G k) ((h : ℂ) • G k)
    rw [alNm38_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0] at h1
    have h2 := hexp k hk
    have h3 : h * alNm38 (G k) ≤ h * (R + K) := mul_le_mul_of_nonneg_left hGn hh0.le
    have h4 : c₂ * h ^ 2 ≤ c₂ * h := by
      have : 0 ≤ c₂ := by positivity
      nlinarith [mul_nonneg (mul_nonneg this hh0.le) (sub_nonneg.2 hh1)]
    nlinarith
  have hδ : ∀ k, k < L → alNm38 (A k * Φ' k - Φ' (k + 1)) ≤
      h * (Φb * (2 * (ε + ω) + (c₂ + 4 * Bb ^ 2) * h)) := by
    intro k hk
    have hstep := volterra_step_error38 B Φ Φb Bb (ε + ω) hΦb0 hBb0 hint hcont hΦ hB
      (t₁ := (k : ℝ) * h) (t₂ := ((k : ℝ) + 1) * h) (hmem k hk) (hmem' k hk)
      (by nlinarith) (A k) (G k) (by
        intro s hs
        have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨(hmem k hk).1.trans hs.1, hs.2.trans (hmem' k hk).2⟩
        have hd := hmod _ (hmem k hk) s hs1 (by
          rw [abs_of_nonpos (by linarith [hs.1])]
          nlinarith [hs.2])
        have h1 := hUh _ (hmem k hk)
        have e : G k - B s = !![0, Complex.I * (Uh ((k : ℝ) * h) - U s);
            star (Complex.I * (Uh ((k : ℝ) * h) - U s)), 0] := by
          ext i j; fin_cases i <;> fin_cases j <;>
            simp [hG, hw, hBdef, zsCoefficientComplex] <;> ring
        rw [e]
        unfold alNm38
        have hn : ‖Uh ((k : ℝ) * h) - U s‖ ≤ ε + ω := by
          calc ‖Uh ((k : ℝ) * h) - U s‖
              = ‖(Uh ((k : ℝ) * h) - U ((k : ℝ) * h)) + (U ((k : ℝ) * h) - U s)‖ := by
                congr 1; ring
            _ ≤ ‖Uh ((k : ℝ) * h) - U ((k : ℝ) * h)‖ + ‖U ((k : ℝ) * h) - U s‖ := norm_add_le _ _
            _ ≤ ε + ω := add_le_add h1 hd
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, norm_mul,
          norm_neg, Complex.norm_I, one_mul, norm_star, norm_zero, zero_add, add_zero]
        exact max_le hn hn)
    have hdt : (((k : ℝ) + 1) * h - (k : ℝ) * h) = h := by ring
    rw [hdt] at hstep
    have hc : ((((k : ℝ) + 1) * h - (k : ℝ) * h : ℝ) : ℂ) = (h : ℂ) := by rw [hdt]
    simp only [hΦ']
    push_cast
    have e1 := hexp k hk
    have e2 : alNm38 (A k - 1 - (h : ℂ) • G k) * Φb ≤ c₂ * h ^ 2 * Φb :=
      mul_le_mul_of_nonneg_right e1 hΦb0
    have hB' : Bb = R + C := hBb
    nlinarith [hstep, e2, mul_nonneg hΦb0 hBb0, mul_nonneg hh0.le hΦb0]
  have hcpos : 0 ≤ R + K + c₂ := by positivity
  have hδpos : 0 ≤ Φb * (2 * (ε + ω) + (c₂ + 4 * Bb ^ 2) * h) := by positivity
  have hfin := alEuler_bound38 L h (R + K + c₂) _ hLh hh0 hcpos hδpos E Φ' A hE0 hEs hAb hδ
  have hEL : E L = alMonodromy38 α' z := rfl
  have hΦL : Φ' L = Φ 1 := by simp only [hΦ']; rw [hLh]
  rw [hEL, hΦL] at hfin
  have htr : Matrix.trace (alMonodromy38 α z) = Matrix.trace (alMonodromy38 α' z) :=
    (trace_alMonodromy38_I_mul α z).symm
  rw [htr, ← sub_div, ← Matrix.trace_sub, norm_div, Complex.norm_ofNat]
  have h5 := norm_trace_le_alNm38 (alMonodromy38 α' z - Φ 1)
  unfold alCompactBound38
  have h6 : Real.exp (R + K + c₂) * (Φb * (2 * (ε + ω) + (c₂ + 4 * Bb ^ 2) * h)) =
      Real.exp (R + (C + 1) + 2 * ((C + 1) ^ 2 + R ^ 2)) * (2 * Real.exp (2 * (R + C))) *
        (2 * (ε + ω) + (2 * ((C + 1) ^ 2 + R ^ 2) + 4 * (R + C) ^ 2) * h) := by
    simp only [hK, hc₂, hΦb, hBb]; ring
  rw [← h6]
  linarith

/-! ### Bridge to the E02 half trace and uniform convergence of the traces -/

/-- The E02 half trace of `u` equals half the trace of the Dyson fundamental matrix of any
continuous representative `U` of the cover of `u`. -/
theorem actualHalfTrace_eq_dyson38 (u : PhysicalL2) {U : ℝ → ℂ}
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)] U) (z : ℂ) :
    actualPhysicalUnitHalfTrace32 u z =
      Matrix.trace (actualComplexZsDysonTsum U z 1) / 2 := by
  unfold actualPhysicalUnitHalfTrace32
  rw [actualComplexZsDysonTsum_eq_of_ae_eq _ U z hae 1 ⟨by norm_num, by norm_num⟩]

theorem alStep_tendsto38 :
    Tendsto (fun N : ℕ => (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat.comp
    (tendsto_atTop_mono (fun N => by simp only [id]; omega) tendsto_id)

/-- Half trace of the lattice monodromy at `e^{ihλ}`. -/
def alLatticeHalfTrace38 (L : ℕ) (f : ℝ → ℂ) (lam : ℝ) : ℂ :=
  Matrix.trace (alMonodromy38 (alSampleField38 L f)
    (Complex.exp ((((1 : ℝ) / L * lam : ℝ) : ℂ) * Complex.I))) / 2

theorem alTrace_tendstoUniformlyOn38 (u : PhysicalL2) {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (0 : ℝ) 2))
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)] U)
    {Uh : ℕ → ℝ → ℂ} (hconv : TendstoUniformlyOn Uh U atTop (Icc (0 : ℝ) 1)) (R : ℝ)
    (hR : 0 ≤ R) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ᶠ N : ℕ in atTop, ∀ lam ∈ Icc (-R) R,
      ‖alLatticeHalfTrace38 (2 * N + 1) (Uh N) lam -
        actualPhysicalUnitHalfTrace32 u (-(lam : ℂ))‖ < ε' := by
  obtain ⟨C, hC, hUb⟩ := exists_nonneg_actualPotential_norm_bound U hUc
  set P : ℝ := Real.exp (R + (C + 1) + 2 * ((C + 1) ^ 2 + R ^ 2)) * (2 * Real.exp (2 * (R + C)))
    with hP
  have hP0 : 0 < P := by positivity
  set c₃ : ℝ := 2 * ((C + 1) ^ 2 + R ^ 2) + 4 * (R + C) ^ 2 with hc₃
  have hc₃0 : 0 ≤ c₃ := by positivity
  set δ₀ : ℝ := ε' / (10 * P) with hδ₀
  have hδ₀0 : 0 < δ₀ := by positivity
  have hP5 : P * (5 * δ₀) < ε' := by
    rw [hδ₀]; field_simp; linarith
  -- modulus of continuity
  have hUU : UniformContinuousOn U (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (hUc.mono (Icc_subset_Icc le_rfl (by norm_num)))
  obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.1 hUU δ₀ hδ₀0
  have e1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) < δ :=
    alStep_tendsto38.eventually (gt_mem_nhds hδ)
  have e2 : ∀ᶠ N : ℕ in atTop, c₃ * ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) ≤ δ₀ := by
    have := (alStep_tendsto38.const_mul c₃).eventually (ge_mem_nhds (by simpa using hδ₀0))
    simpa using this
  have e3 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) * (R + C + 1) ≤ 1 / 2 := by
    have := (alStep_tendsto38.mul_const (R + C + 1)).eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) * (R + C + 1) < 1 / 2))
    simpa using this
  have hε₁ : 0 < min δ₀ 1 := lt_min hδ₀0 one_pos
  have e4 : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Icc (0 : ℝ) 1, ‖Uh N x - U x‖ ≤ min δ₀ 1 := by
    have := (Metric.tendstoUniformlyOn_iff.1 hconv) (min δ₀ 1) hε₁
    filter_upwards [this] with N hN x hx
    have := hN x hx
    rw [dist_eq_norm] at this
    rw [norm_sub_rev]; exact this.le
  filter_upwards [e1, e2, e3, e4] with N h1 h2 h3 h4 lam hlam
  have hlam' : |lam| ≤ R := abs_le.2 ⟨(mem_Icc.1 hlam).1, (mem_Icc.1 hlam).2⟩
  have hL : (2 * N + 1 : ℕ) ≠ 0 := by omega
  have hcmp := alTrace_compare38 (L := 2 * N + 1) hL (U := U) (Uh := Uh N) (R := R) (C := C)
    (ε := min δ₀ 1) (ω := δ₀) hR hC (le_min hδ₀0.le zero_le_one) (min_le_right _ _) hδ₀0.le hUc hUb
    h4 (fun x hx y hy hxy => by
      have := (hδU x hx y hy (by rw [Real.dist_eq]; exact lt_of_le_of_lt hxy h1)).le
      rwa [dist_eq_norm] at this)
    h3 hlam'
  have hbd : alCompactBound38 R C (min δ₀ 1) δ₀ (1 / ((2 * N + 1 : ℕ) : ℝ)) < ε' := by
    unfold alCompactBound38
    rw [← hP]
    have : 2 * (min δ₀ 1 + δ₀) + (2 * ((C + 1) ^ 2 + R ^ 2) + 4 * (R + C) ^ 2) *
        (1 / ((2 * N + 1 : ℕ) : ℝ)) ≤ 5 * δ₀ := by
      rw [← hc₃]; have := min_le_left δ₀ 1; linarith
    calc _ ≤ P * (5 * δ₀) := mul_le_mul_of_nonneg_left this hP0.le
      _ < ε' := hP5
  rw [actualHalfTrace_eq_dyson38 u hae]
  exact lt_of_le_of_lt hcmp hbd

/-! ### Final consequences: disk condition, uniform convergence of `v_h`, convergence of the energies -/

theorem abs_sin_sub_self_le38 (x : ℝ) : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by
  have pos : ∀ y : ℝ, 0 < y → |Real.sin y - y| ≤ |y| ^ 3 / 6 := by
    intro y hy
    have h1 := Real.sin_lt hy
    have h2 := Real.sin_gt_sub_cube hy
    rw [abs_of_pos hy, abs_of_nonpos (by linarith)]
    linarith
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have := pos (-x) (by linarith)
    rw [Real.sin_neg, abs_neg] at this
    have e : |Real.sin x - x| = |-Real.sin x - -x| := by rw [← abs_neg]; congr 1; ring
    rw [e]; exact this
  · subst hx; simp
  · exact pos x hx

/-- **Eventual disk condition** (paper/v2.tex l.2282-2283). -/
theorem alDisk_eventually38 {U : ℝ → ℂ} (hUc : ContinuousOn U (Icc (0 : ℝ) 2))
    {Uh : ℕ → ℝ → ℂ} (hconv : TendstoUniformlyOn Uh U atTop (Icc (0 : ℝ) 1)) :
    ∀ᶠ N : ℕ in atTop, IsALField38 (alSampleField38 (2 * N + 1) (Uh N)) := by
  obtain ⟨C, hC, hUb⟩ := exists_nonneg_actualPotential_norm_bound U hUc
  have e3 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) * (C + 1) < 1 := by
    have := (alStep_tendsto38.mul_const (C + 1)).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) * (C + 1) < 1))
    simpa using this
  have e4 : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Icc (0 : ℝ) 1, ‖Uh N x - U x‖ ≤ 1 := by
    have := (Metric.tendstoUniformlyOn_iff.1 hconv) 1 one_pos
    filter_upwards [this] with N hN x hx
    have := hN x hx
    rw [dist_eq_norm] at this
    rw [norm_sub_rev]; exact this.le
  filter_upwards [e3, e4] with N h3 h4 j
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  have hLpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hv : (j.val : ℝ) * ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    have : (j.val : ℝ) + 1 ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast ZMod.val_lt j
    rw [mul_one_div, div_le_one hLpos]; linarith
  have hx := hv
  have h5 := h4 _ hx
  have h6 := hUb _ ⟨hx.1, hx.2.trans (by norm_num)⟩
  unfold alSampleField38
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : ‖Uh N ((j.val : ℝ) * ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ)))‖ ≤ C + 1 := by
    calc _ = ‖(Uh N _ - U _) + U _‖ := by congr 1; ring
      _ ≤ ‖Uh N _ - U _‖ + ‖U _‖ := norm_add_le _ _
      _ ≤ C + 1 := by linarith
  calc _ ≤ (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) * (C + 1) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ < 1 := h3

/-- `v(-λ; u)` is continuous (it is the E02 gap height composed with `λ ↦ -λ`). -/
theorem continuous_reflectedGapHeight38 (u : PhysicalL2) :
    Continuous (fun lam : ℝ => actualGapHeightE02_38 u (-lam)) :=
  (continuous_actualGapHeightE02_38 u).comp continuous_neg

theorem continuous_arcosh_max38 : Continuous (fun x : ℝ => Real.arcosh (max 1 x)) :=
  Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
    (fun x => mem_Ici.2 (le_max_left _ _))

theorem actualGapHeight_reflect38 (u : PhysicalL2) (lam : ℝ) :
    actualGapHeightE02_38 u (-lam) =
      Real.arcosh (max 1 ‖actualPhysicalUnitHalfTrace32 u (-(lam : ℂ))‖) := by
  unfold actualGapHeightE02_38
  push_cast
  rfl

/-- **Uniform convergence on compacts** (paper/v2.tex l.2283-2285): the lattice gap
`v_h` converges to the reflected continuum gap `v(-λ;u)` uniformly on `[-R,R]`. -/
theorem alGapHeight_tendstoUniformlyOn38 (u : PhysicalL2) {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (0 : ℝ) 2))
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)] U)
    {Uh : ℕ → ℝ → ℂ} (hconv : TendstoUniformlyOn Uh U atTop (Icc (0 : ℝ) 1)) (R : ℝ) :
    TendstoUniformlyOn (fun (N : ℕ) (lam : ℝ) => alGapHeight38 (2 * N + 1) (Uh N) lam)
      (fun lam => actualGapHeightE02_38 u (-lam)) atTop (Icc (-R) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set R' : ℝ := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  obtain ⟨C, hC, hUb⟩ := exists_nonneg_actualPotential_norm_bound U hUc
  set M₀ : ℝ := 2 * Real.exp (2 * (R' + C)) with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  -- bound on the continuum half trace
  have hΔ : ∀ lam ∈ Icc (-R) R, ‖actualPhysicalUnitHalfTrace32 u (-(lam : ℂ))‖ ≤ M₀ := by
    intro lam hlam
    have hlamR : ‖-(lam : ℂ)‖ ≤ R' := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor
      · linarith [hlam.1, le_max_left R 0, le_max_right R 0]
      · linarith [hlam.2, le_max_left R 0]
    obtain ⟨-, -, hΦ, -⟩ := alDyson_facts38 hUc hlamR hR'0 hC hUb
    rw [actualHalfTrace_eq_dyson38 u hae, norm_div, Complex.norm_ofNat]
    have := (norm_trace_le_alNm38 (actualComplexZsDysonTsum U (-(lam : ℂ)) 1))
    have h2 := hΦ 1 ⟨by norm_num, le_rfl⟩
    linarith
  have hUCφ : UniformContinuousOn (fun x : ℝ => Real.arcosh (max 1 x)) (Icc (0 : ℝ) (M₀ + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous continuous_arcosh_max38.continuousOn
  obtain ⟨η, hη, hηφ⟩ := Metric.uniformContinuousOn_iff.1 hUCφ ε hε
  have hev := alTrace_tendstoUniformlyOn38 u hUc hae hconv R' hR'0 (min η 1)
    (lt_min hη one_pos)
  filter_upwards [hev] with N hN lam hlam
  have hNl := hN lam ⟨by linarith [hlam.1, le_max_left R 0, le_max_right R 0],
    by linarith [hlam.2, le_max_left R 0]⟩
  have hd := hΔ lam hlam
  set T := alLatticeHalfTrace38 (2 * N + 1) (Uh N) lam with hT
  set D := actualPhysicalUnitHalfTrace32 u (-(lam : ℂ)) with hD
  have h1 : |‖T‖ - ‖D‖| < min η 1 := lt_of_le_of_lt (abs_norm_sub_norm_le _ _) hNl
  have h2 : ‖T‖ ≤ M₀ + 1 := by
    have := (abs_le.1 h1.le).2
    have := min_le_right η 1
    linarith
  rw [actualGapHeight_reflect38]
  have hdist : dist ‖D‖ ‖T‖ < η := by
    rw [Real.dist_eq, abs_sub_comm]; exact lt_of_lt_of_le h1 (min_le_left _ _)
  have := hηφ ‖D‖ ⟨norm_nonneg _, by linarith⟩ ‖T‖ ⟨norm_nonneg _, h2⟩ hdist
  simpa [alGapHeight38, alLatticeHalfTrace38, hT, hD] using this

theorem integral_tendsto_of_unif38 {a b : ℝ} (hab : a ≤ b) {F : ℕ → ℝ → ℝ} {ψ : ℝ → ℝ}
    (hF : ∀ᶠ N : ℕ in atTop, Continuous (F N)) (hψ : Continuous ψ)
    (hu : TendstoUniformlyOn F ψ atTop (Icc a b)) :
    Tendsto (fun N => ∫ x in a..b, F N x) atTop (𝓝 (∫ x in a..b, ψ x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hb : 0 ≤ b - a := by linarith
  set ε₁ : ℝ := ε / (2 * (b - a) + 1) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hu' := (Metric.tendstoUniformlyOn_iff.1 hu) ε₁ hε₁0
  filter_upwards [hF, hu'] with N hN hN'
  rw [dist_eq_norm, ← intervalIntegral.integral_sub (hN.intervalIntegrable _ _)
    (hψ.intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun x => F N x - ψ x) (C := ε₁) (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      have := hN' x ⟨hx.1.le, hx.2⟩
      rw [dist_eq_norm, norm_sub_rev] at this
      exact this.le)
  refine this.trans_lt ?_
  rw [abs_of_nonneg hb, hε₁]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- **Convergence of the spectral energies** (paper/v2.tex l.2285-2292, `D:eq:compactconsistency`),
for a continuous even weight `W`. -/
theorem alCompactEnergy_tendsto38 (u : PhysicalL2) {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (0 : ℝ) 2))
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)] U)
    {Uh : ℕ → ℝ → ℂ} (hconv : TendstoUniformlyOn Uh U atTop (Icc (0 : ℝ) 1))
    {W : ℝ → ℝ} (hW : Continuous W) (hWe : ∀ x, W (-x) = W x) (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun N : ℕ => (2 / Real.pi) * ∫ lam in (-R)..R,
        W (2 * Real.sin ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) * lam) / ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ))) *
          alGapHeight38 (2 * N + 1) (Uh N) lam)
      atTop (𝓝 ((2 / Real.pi) * ∫ lam in (-R)..R, W (2 * lam) * actualGapHeightE02_38 u lam)) := by
  have hrefl : ∫ lam in (-R)..R, W (2 * lam) * actualGapHeightE02_38 u (-lam) =
      ∫ lam in (-R)..R, W (2 * lam) * actualGapHeightE02_38 u lam := by
    have := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun x => W (2 * x) * actualGapHeightE02_38 u x)
    simp only [neg_neg] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    rw [show 2 * -x = -(2 * x) by ring, hWe]
  rw [← hrefl]
  refine Tendsto.const_mul _ ?_
  have hvu := alGapHeight_tendstoUniformlyOn38 u hUc hae hconv R
  have hfield := alDisk_eventually38 hUc hconv
  have hcont : ∀ᶠ N : ℕ in atTop, Continuous (fun lam : ℝ =>
      W (2 * Real.sin ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) * lam) / ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ))) *
        alGapHeight38 (2 * N + 1) (Uh N) lam) := by
    filter_upwards [hfield] with N hN
    haveI : NeZero (2 * N + 1) := ⟨by omega⟩
    have hk := continuous_alKappa38 hN
    have hv : Continuous (fun lam : ℝ => alGapHeight38 (2 * N + 1) (Uh N) lam) := by
      have : (fun lam : ℝ => alGapHeight38 (2 * N + 1) (Uh N) lam) = fun lam =>
          ((2 * N + 1 : ℕ) : ℝ) * alKappa38 (alSampleField38 (2 * N + 1) (Uh N))
            ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) * lam) :=
        funext fun lam => alGapHeight38_eq_kappa (by omega) _ _
      rw [this]
      exact continuous_const.mul (hk.comp (continuous_const.mul continuous_id))
    exact (hW.comp (by fun_prop)).mul hv
  have hψ : Continuous (fun lam : ℝ => W (2 * lam) * actualGapHeightE02_38 u (-lam)) :=
    (hW.comp (continuous_const.mul continuous_id)).mul (continuous_reflectedGapHeight38 u)
  refine integral_tendsto_of_unif38 (by linarith) hcont hψ ?_
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set KK : Set ℝ := Icc (-(2 * R + 1)) (2 * R + 1) with hKK
  have hWU : UniformContinuousOn W KK :=
    isCompact_Icc.uniformContinuousOn_of_continuous hW.continuousOn
  obtain ⟨MW, hMW⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := KK))
  obtain ⟨Mv, hMv⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    (continuous_reflectedGapHeight38 u).continuousOn
  set MW' : ℝ := max MW 0 with hMW'
  set Mv' : ℝ := max Mv 0 with hMv'
  have hMW0 : 0 ≤ MW' := le_max_right _ _
  have hMv0 : 0 ≤ Mv' := le_max_right _ _
  set ε₁ : ℝ := ε / (2 * (Mv' + 1)) with hε₁
  set ε₂ : ℝ := min 1 (ε / (2 * (MW' + 1))) with hε₂
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₂0 : 0 < ε₂ := lt_min one_pos (by positivity)
  obtain ⟨δW, hδW, hδWU⟩ := Metric.uniformContinuousOn_iff.1 hWU ε₁ hε₁0
  have hv2 := (Metric.tendstoUniformlyOn_iff.1 hvu) ε₂ hε₂0
  -- small step
  set θ : ℝ := min δW 1 with hθ
  have hθ0 : 0 < θ := lt_min hδW one_pos
  have hst : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) ^ 2 * (R ^ 3 / 3) < θ := by
    have := (alStep_tendsto38.pow 2).mul_const (R ^ 3 / 3)
    have h := this.eventually (gt_mem_nhds (by simpa using hθ0 : (0 : ℝ) ^ 2 * (R ^ 3 / 3) < θ))
    filter_upwards [h] with N hN
    simpa [div_pow] using hN
  filter_upwards [hv2, hst] with N hN1 hN2 lam hlam
  set h : ℝ := (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) with hhdef
  have hh0 : 0 < h := by positivity
  have hlamabs : |lam| ≤ R := abs_le.2 ⟨(mem_Icc.1 hlam).1, (mem_Icc.1 hlam).2⟩
  -- sine approximation
  have hsin : |2 * Real.sin (h * lam) / h - 2 * lam| ≤ h ^ 2 * (R ^ 3 / 3) := by
    have h1 := abs_sin_sub_self_le38 (h * lam)
    have e : 2 * Real.sin (h * lam) / h - 2 * lam = 2 * (Real.sin (h * lam) - h * lam) / h := by
      field_simp
    rw [e, abs_div, abs_mul, abs_of_pos hh0, abs_two, div_le_iff₀ hh0]
    have h2 : |h * lam| ^ 3 = h ^ 3 * |lam| ^ 3 := by rw [abs_mul, abs_of_pos hh0]; ring
    have h3 : |lam| ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hlamabs 3
    have h4 : 0 ≤ h ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  have hsin' : |2 * Real.sin (h * lam) / h - 2 * lam| < θ :=
    lt_of_le_of_lt hsin (by simpa [hhdef, div_pow] using hN2)
  have hlam2 : |2 * lam| ≤ 2 * R := by rw [abs_mul, abs_two]; linarith
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have hθδ : θ ≤ δW := min_le_left _ _
  have haK : 2 * Real.sin (h * lam) / h ∈ KK := by
    have h4 := abs_le.1 hsin'.le
    have h5 := abs_le.1 hlam2
    rw [hKK]; constructor <;> linarith
  have hbK : 2 * lam ∈ KK := by
    have h5 := abs_le.1 hlam2
    rw [hKK]; constructor <;> linarith
  have hWd := hδWU _ haK _ hbK (by rw [Real.dist_eq]; exact lt_of_lt_of_le hsin' hθδ)
  have hvd : dist (actualGapHeightE02_38 u (-lam)) (alGapHeight38 (2 * N + 1) (Uh N) lam) < ε₂ :=
    hN1 lam hlam
  have hvb : ‖actualGapHeightE02_38 u (-lam)‖ ≤ Mv' := (hMv lam hlam).trans (le_max_left _ _)
  have hWb : ‖W (2 * lam)‖ ≤ MW' := (hMW _ hbK).trans (le_max_left _ _)
  have hvN : |alGapHeight38 (2 * N + 1) (Uh N) lam| ≤ Mv' + 1 := by
    have h1 : |alGapHeight38 (2 * N + 1) (Uh N) lam - actualGapHeightE02_38 u (-lam)| < 1 := by
      rw [← Real.dist_eq, dist_comm]; exact lt_of_lt_of_le hvd (min_le_left _ _)
    have h2 : |actualGapHeightE02_38 u (-lam)| ≤ Mv' := by simpa using hvb
    have := abs_sub_abs_le_abs_sub (alGapHeight38 (2 * N + 1) (Uh N) lam)
      (actualGapHeightE02_38 u (-lam))
    linarith
  rw [Real.dist_eq] at hWd hvd ⊢
  set a := 2 * Real.sin (h * lam) / h
  set vN := alGapHeight38 (2 * N + 1) (Uh N) lam
  set v := actualGapHeightE02_38 u (-lam)
  have e : W (2 * lam) * v - W a * vN = (W (2 * lam) - W a) * vN + W (2 * lam) * (v - vN) := by ring
  have hb1 : |(W (2 * lam) - W a) * vN| ≤ ε₁ * (Mv' + 1) := by
    rw [abs_mul]
    exact mul_le_mul (by rw [abs_sub_comm]; exact hWd.le) hvN (abs_nonneg _) hε₁0.le
  have hb2 : |W (2 * lam) * (v - vN)| < ε / 2 := by
    rw [abs_mul]
    have hWb' : |W (2 * lam)| ≤ MW' := by simpa using hWb
    have h3 : |v - vN| < ε / (2 * (MW' + 1)) := lt_of_lt_of_le hvd (min_le_right _ _)
    calc |W (2 * lam)| * |v - vN| ≤ MW' * |v - vN| :=
          mul_le_mul_of_nonneg_right hWb' (abs_nonneg _)
      _ ≤ MW' * (ε / (2 * (MW' + 1))) := mul_le_mul_of_nonneg_left h3.le hMW0
      _ < ε / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hb1' : ε₁ * (Mv' + 1) = ε / 2 := by rw [hε₁]; field_simp
  rw [e]
  calc |(W (2 * lam) - W a) * vN + W (2 * lam) * (v - vN)|
      ≤ |(W (2 * lam) - W a) * vN| + |W (2 * lam) * (v - vN)| := abs_add_le _ _
    _ < ε := by linarith

/-! ### The `H¹` form of the hypotheses -/

theorem physicalFourier_sub38 (a b : PhysicalL2) (k : ℤ) :
    physicalFourier ((a - b : PhysicalL2) : PhysicalCircle → ℂ) k =
      physicalFourier (a : PhysicalCircle → ℂ) k - physicalFourier (b : PhysicalCircle → ℂ) k := by
  haveI : IsProbabilityMeasure spatialMeasure := by unfold spatialMeasure; infer_instance
  have hint : ∀ c : PhysicalL2, Integrable (fun t => fourier (-k) t * (c : PhysicalCircle → ℂ) t)
      (AddCircle.haarAddCircle : Measure PhysicalCircle) := by
    intro c
    have h1 : Integrable (c : PhysicalCircle → ℂ) (AddCircle.haarAddCircle : Measure PhysicalCircle) :=
      (Lp.memLp c).integrable (by norm_num)
    exact Integrable.bdd_mul (c := 1) h1 (fourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by simp))
  unfold physicalFourier fourierCoeff
  have hae : (fun t => ((a - b : PhysicalL2) : PhysicalCircle → ℂ) t) =ᵐ[spatialMeasure]
      fun t => (a : PhysicalCircle → ℂ) t - (b : PhysicalCircle → ℂ) t := by
    filter_upwards [Lp.coeFn_sub a b] with t ht
    simpa using ht
  have hs := integral_sub (hint a) (hint b)
  simp only [smul_eq_mul]
  rw [← hs]
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  rw [ht]; ring

/-- Squared `H¹` distance of two physical fields through their Fourier coefficients
(weights `⟨k⟩² = 1 + k²`, matching `SobolevSquareSummable 1`). -/
def h1DistSq38 (a b : PhysicalL2) : ℝ :=
  ∑' k : ℤ, Real.rpow (japaneseBracket k) (2 * 1) *
    ‖physicalFourier (a : PhysicalCircle → ℂ) k - physicalFourier (b : PhysicalCircle → ℂ) k‖ ^ 2

theorem sobolevSummable_sub38 {a b : PhysicalL2}
    (ha : SobolevSquareSummable 1 (physicalFourier (a : PhysicalCircle → ℂ)))
    (hb : SobolevSquareSummable 1 (physicalFourier (b : PhysicalCircle → ℂ))) :
    SobolevSquareSummable 1 (physicalFourier ((a - b : PhysicalL2) : PhysicalCircle → ℂ)) := by
  have h := (ha.mul_left 2).add (hb.mul_left 2)
  have hw : ∀ n : ℤ, 0 ≤ Real.rpow (japaneseBracket n) (2 * 1) := fun n => by
    have : 0 < japaneseBracket n := by unfold japaneseBracket; positivity
    exact (Real.rpow_pos_of_pos this _).le
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · rw [physicalFourier_sub38]; exact mul_nonneg (hw n) (sq_nonneg _)
  rw [physicalFourier_sub38]
  have hq : ‖physicalFourier (a : PhysicalCircle → ℂ) n - physicalFourier (b : PhysicalCircle → ℂ) n‖ ^ 2 ≤
      2 * ‖physicalFourier (a : PhysicalCircle → ℂ) n‖ ^ 2 +
        2 * ‖physicalFourier (b : PhysicalCircle → ℂ) n‖ ^ 2 := by
    have h1 := norm_sub_le (physicalFourier (a : PhysicalCircle → ℂ) n)
      (physicalFourier (b : PhysicalCircle → ℂ) n)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖physicalFourier (a : PhysicalCircle → ℂ) n‖ -
      ‖physicalFourier (b : PhysicalCircle → ℂ) n‖)]
  calc _ ≤ Real.rpow (japaneseBracket n) (2 * 1) * (2 * ‖physicalFourier (a : PhysicalCircle → ℂ) n‖ ^ 2 +
        2 * ‖physicalFourier (b : PhysicalCircle → ℂ) n‖ ^ 2) := mul_le_mul_of_nonneg_left hq (hw n)
    _ = _ := by ring

theorem h1DistSq38_eq_norm_sq {a b : PhysicalL2}
    (hsub : SobolevSquareSummable 1 (physicalFourier ((a - b : PhysicalL2) : PhysicalCircle → ℂ))) :
    h1DistSq38 a b = ‖physicalSobolevL2 1 (a - b) hsub‖ ^ 2 := by
  rw [physicalSobolevL2_norm_sq]
  unfold h1DistSq38
  exact tsum_congr (fun n => by rw [physicalFourier_sub38])

theorem physicalH1Continuous_sub38 {a b : PhysicalL2}
    (ha : SobolevSquareSummable 1 (physicalFourier (a : PhysicalCircle → ℂ)))
    (hb : SobolevSquareSummable 1 (physicalFourier (b : PhysicalCircle → ℂ)))
    (hsub : SobolevSquareSummable 1 (physicalFourier ((a - b : PhysicalL2) : PhysicalCircle → ℂ))) :
    physicalH1Continuous (a - b) hsub = physicalH1Continuous a ha - physicalH1Continuous b hb := by
  refine (physicalH1Continuous_hasSum (a - b) hsub).unique ?_
  have := (physicalH1Continuous_hasSum a ha).sub (physicalH1Continuous_hasSum b hb)
  have e : (fun p : ℤ => physicalFourier ((a - b : PhysicalL2) : PhysicalCircle → ℂ) p •
      fourier (T := (1 : ℝ)) p) = fun p => physicalFourier (a : PhysicalCircle → ℂ) p •
      fourier (T := (1 : ℝ)) p - physicalFourier (b : PhysicalCircle → ℂ) p •
      fourier (T := (1 : ℝ)) p := funext (fun p => by rw [physicalFourier_sub38]; exact sub_smul (physicalFourier (a : PhysicalCircle → ℂ) p) (physicalFourier (b : PhysicalCircle → ℂ) p) (fourier (T := (1 : ℝ)) p))
  rw [e]; exact this

theorem h1_cover_ae38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)]
      (fun s : ℝ => physicalH1Continuous u hu (s : PhysicalCircle)) := by
  haveI : IsProbabilityMeasure spatialMeasure := by unfold spatialMeasure; infer_instance
  set F := physicalH1Continuous u hu
  have h0 : (u : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] (F : PhysicalCircle → ℂ) := by
    have := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure F
    rw [physicalH1Continuous_toLp u hu] at this
    exact this
  have h1 := naturalPhysicalCoverL2_ae u
  have h2 := naturalPhysicalCover_preserving.quasiMeasurePreserving.ae_eq_comp h0
  have h : (naturalPhysicalCoverL2 u : SpectralCircle → ℂ)
      =ᵐ[spectralHaar] ((F : PhysicalCircle → ℂ) ∘ naturalPhysicalCover) := h1.trans h2
  have hv : (naturalPhysicalCoverL2 u : SpectralCircle → ℂ)
      =ᵐ[(volume : Measure SpectralCircle)] ((F : PhysicalCircle → ℂ) ∘ naturalPhysicalCover) := by
    rw [NlsGge.Schur.spectral_volume_eq_two_smul]
    exact Measure.ae_smul_measure h (2 : ENNReal)
  have hr := (AddCircle.measurePreserving_mk (2 : ℝ) 0).quasiMeasurePreserving.ae_eq_comp hv
  have h02 : (0 : ℝ) + 2 = 2 := by norm_num
  rw [h02] at hr
  filter_upwards [hr] with s hs
  refine hs.trans ?_
  simp only [Function.comp, naturalPhysicalCover_coe]

/-- The continuous (`H¹`) representative of a physical field, as a function on `ℝ`. -/
def h1Rep38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) : ℝ → ℂ :=
  fun x => physicalH1Continuous u hu (x : PhysicalCircle)

theorem continuous_h1Rep38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Continuous (h1Rep38 u hu) :=
  (physicalH1Continuous u hu).continuous.comp (AddCircle.continuous_mk' _)

theorem h1Rep_tendstoUniformly38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (uN : ℕ → PhysicalL2)
    (huN : ∀ N, SobolevSquareSummable 1 (physicalFourier (uN N)))
    (hconv : Tendsto (fun N => h1DistSq38 (uN N) u) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun N => h1Rep38 (uN N) (huN N)) (h1Rep38 u hu) atTop
      (univ : Set ℝ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set K : ℝ := ‖reciprocalBracketL2‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  set e : ℝ := ε / (K + 1) with he
  have he0 : 0 < e := by positivity
  filter_upwards [hconv.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < e ^ 2))] with N hN x _
  have hsub := sobolevSummable_sub38 (huN N) hu
  have h1 := physicalH1Continuous_sub38 (huN N) hu hsub
  have h2 := physicalH1Continuous_norm_bound (uN N - u) hsub
  have h3 : ‖physicalSobolevL2 1 (uN N - u) hsub‖ < e := by
    rw [h1DistSq38_eq_norm_sq hsub] at hN
    exact lt_of_pow_lt_pow_left₀ 2 he0.le hN
  have h4 : dist (h1Rep38 u hu x) (h1Rep38 (uN N) (huN N) x) ≤
      ‖physicalH1Continuous (uN N - u) hsub‖ := by
    rw [h1, dist_comm, dist_eq_norm]
    unfold h1Rep38
    rw [← ContinuousMap.sub_apply]
    exact ContinuousMap.norm_coe_le_norm _ _
  refine lt_of_le_of_lt h4 (h2.trans_lt ?_)
  calc ‖physicalSobolevL2 1 (uN N - u) hsub‖ * K ≤ e * K :=
        mul_le_mul_of_nonneg_right h3.le hK0
    _ < ε := by
        rw [he, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith


/-- **D:prop:compactconsistency** (paper/v2.tex l.2280-2309).  Let `u_h = uN N ∈ P_N L²`,
`h = (2N+1)⁻¹`, `u_h → u` in `H¹` (the squared `H¹` distance `h1DistSq38 (uN N) u → 0`), and
`α_j = h u_h(jh)` (continuous representatives).  Then (1) the disk condition holds eventually;
(2) the lattice gap `v_h(λ) = arcosh (max 1 |½ tr M(e^{ihλ})|)` converges to the reflected
continuum gap `v(-λ;u)` uniformly on every compact interval `[-R,R]`; (3) for every continuous
even weight `W` and `R ≥ 0`, `(2/π)∫_{-R}^R W(2 sin(hλ)/h) v_h(λ) dλ → (2/π)∫_{-R}^R W(2λ) v(λ;u) dλ`. -/
theorem alCompactConsistency38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (uN : ℕ → PhysicalL2)
    (huN : ∀ N, SobolevSquareSummable 1 (physicalFourier (uN N)))
    (_hPN : ∀ (N : ℕ) (k : ℤ), N < |k| → physicalFourier (uN N) k = 0)
    (hconv : Tendsto (fun N => h1DistSq38 (uN N) u) atTop (𝓝 0)) :
    (∀ᶠ N : ℕ in atTop, IsALField38 (alSampleField38 (2 * N + 1) (h1Rep38 (uN N) (huN N)))) ∧
    (∀ R : ℝ, TendstoUniformlyOn
      (fun (N : ℕ) (lam : ℝ) => alGapHeight38 (2 * N + 1) (h1Rep38 (uN N) (huN N)) lam)
      (fun lam => actualGapHeightE02_38 u (-lam)) atTop (Icc (-R) R)) ∧
    (∀ W : ℝ → ℝ, Continuous W → (∀ x, W (-x) = W x) → ∀ R : ℝ, 0 ≤ R →
      Tendsto (fun N : ℕ => (2 / Real.pi) * ∫ lam in (-R)..R,
          W (2 * Real.sin ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) * lam) /
            ((1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ))) *
            alGapHeight38 (2 * N + 1) (h1Rep38 (uN N) (huN N)) lam)
        atTop (𝓝 ((2 / Real.pi) * ∫ lam in (-R)..R,
          W (2 * lam) * actualGapHeightE02_38 u lam))) := by
  have hUc : ContinuousOn (h1Rep38 u hu) (Icc (0 : ℝ) 2) :=
    (continuous_h1Rep38 u hu).continuousOn
  have hae := h1_cover_ae38 u hu
  have hU := (h1Rep_tendstoUniformly38 u hu uN huN hconv).mono (subset_univ (Icc (0 : ℝ) 1))
  refine ⟨alDisk_eventually38 hUc hU, fun R => alGapHeight_tendstoUniformlyOn38 u hUc hae hU R,
    fun W hW hWe R hR => alCompactEnergy_tendsto38 u hUc hae hU hW hWe R hR⟩

end NlsGge.AblowitzLadik

end
