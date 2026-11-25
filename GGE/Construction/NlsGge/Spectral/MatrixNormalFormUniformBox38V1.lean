import NlsGge.Spectral.ComplexAbsolutelyContinuousAEODEIntegralIdentityV1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations

/-- Complex `2 × 2` matrices (no norm instance is attached). -/
abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- Local maximal-row-sum norm on `2 × 2` complex matrices:
`‖A‖ = max_i (‖A i 0‖ + ‖A i 1‖)`.  This is the operator norm induced by the
`ℓ^∞` norm on `ℂ²`; in particular `‖1‖ = 1`. -/
def rowSumNorm2 (A : Mat2) : ℝ :=
  max (‖A 0 0‖ + ‖A 0 1‖) (‖A 1 0‖ + ‖A 1 1‖)

theorem rowSumNorm2_row_le (A : Mat2) (i : Fin 2) :
    ‖A i 0‖ + ‖A i 1‖ ≤ rowSumNorm2 A := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem rowSumNorm2_le_iff (A : Mat2) (c : ℝ) :
    rowSumNorm2 A ≤ c ↔ ∀ i : Fin 2, ‖A i 0‖ + ‖A i 1‖ ≤ c := by
  unfold rowSumNorm2
  rw [max_le_iff, Fin.forall_fin_two]

theorem rowSumNorm2_nonneg (A : Mat2) : 0 ≤ rowSumNorm2 A :=
  le_trans (add_nonneg (norm_nonneg _) (norm_nonneg _)) (rowSumNorm2_row_le A 0)

theorem rowSumNorm2_entry_le (A : Mat2) (i j : Fin 2) :
    ‖A i j‖ ≤ rowSumNorm2 A := by
  have h := rowSumNorm2_row_le A i
  fin_cases j
  · simp only [Fin.zero_eta]
    linarith [norm_nonneg (A i 1)]
  · simp only [Fin.mk_one]
    linarith [norm_nonneg (A i 0)]

theorem rowSumNorm2_one : rowSumNorm2 (1 : Mat2) = 1 := by
  simp [rowSumNorm2]

theorem rowSumNorm2_add_le (A B : Mat2) :
    rowSumNorm2 (A + B) ≤ rowSumNorm2 A + rowSumNorm2 B := by
  rw [rowSumNorm2_le_iff]
  intro i
  have h1 := rowSumNorm2_row_le A i
  have h2 := rowSumNorm2_row_le B i
  have h3 := norm_add_le (A i 0) (B i 0)
  have h4 := norm_add_le (A i 1) (B i 1)
  simp only [Matrix.add_apply]
  linarith

theorem rowSumNorm2_sub_le (A B : Mat2) :
    rowSumNorm2 (A - B) ≤ rowSumNorm2 A + rowSumNorm2 B := by
  rw [rowSumNorm2_le_iff]
  intro i
  have h1 := rowSumNorm2_row_le A i
  have h2 := rowSumNorm2_row_le B i
  have h3 := norm_sub_le (A i 0) (B i 0)
  have h4 := norm_sub_le (A i 1) (B i 1)
  simp only [Matrix.sub_apply]
  linarith

/-- Submultiplicativity of the local norm. -/
theorem rowSumNorm2_mul_le (A B : Mat2) :
    rowSumNorm2 (A * B) ≤ rowSumNorm2 A * rowSumNorm2 B := by
  rw [rowSumNorm2_le_iff]
  intro i
  have hA := rowSumNorm2_row_le A i
  have hB0 := rowSumNorm2_row_le B 0
  have hB1 := rowSumNorm2_row_le B 1
  have e : ∀ j : Fin 2, ‖(A * B) i j‖ ≤ ‖A i 0‖ * ‖B 0 j‖ + ‖A i 1‖ * ‖B 1 j‖ := by
    intro j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    calc ‖A i 0 * B 0 j + A i 1 * B 1 j‖
        ≤ ‖A i 0 * B 0 j‖ + ‖A i 1 * B 1 j‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  have e0 := e 0
  have e1 := e 1
  have n1 := norm_nonneg (A i 0)
  have n2 := norm_nonneg (A i 1)
  have nB := rowSumNorm2_nonneg B
  have k0 : ‖A i 0‖ * (‖B 0 0‖ + ‖B 0 1‖) ≤ ‖A i 0‖ * rowSumNorm2 B :=
    mul_le_mul_of_nonneg_left hB0 n1
  have k1 : ‖A i 1‖ * (‖B 1 0‖ + ‖B 1 1‖) ≤ ‖A i 1‖ * rowSumNorm2 B :=
    mul_le_mul_of_nonneg_left hB1 n2
  have k2 : (‖A i 0‖ + ‖A i 1‖) * rowSumNorm2 B ≤ rowSumNorm2 A * rowSumNorm2 B :=
    mul_le_mul_of_nonneg_right hA nB
  nlinarith

/-- Entrywise interval integrability on `[0,1]`. -/
def EntryII (F : ℝ → Mat2) : Prop :=
  ∀ i j : Fin 2, IntervalIntegrable (fun s => F s i j) volume 0 1

/-- Entrywise continuity on `[0,1]`. -/
def EntryCont (F : ℝ → Mat2) : Prop :=
  ∀ i j : Fin 2, ContinuousOn (fun s => F s i j) (Set.uIcc (0:ℝ) 1)

theorem EntryII.add {P Q : ℝ → Mat2} (hP : EntryII P) (hQ : EntryII Q) :
    EntryII (fun s => P s + Q s) := by
  intro i j
  simpa only [Matrix.add_apply] using (hP i j).add (hQ i j)

theorem EntryII.mul_cont {P Q : ℝ → Mat2} (hP : EntryII P) (hQ : EntryCont Q) :
    EntryII (fun s => P s * Q s) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hP i 0).mul_continuousOn (hQ 0 j)).add ((hP i 1).mul_continuousOn (hQ 1 j))

theorem EntryCont.mul_II {P Q : ℝ → Mat2} (hP : EntryCont P) (hQ : EntryII Q) :
    EntryII (fun s => P s * Q s) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hQ 0 j).continuousOn_mul (hP i 0)).add ((hQ 1 j).continuousOn_mul (hP i 1))

theorem EntryII.rowSumNorm2 {F : ℝ → Mat2} (hF : EntryII F) :
    IntervalIntegrable (fun s => rowSumNorm2 (F s)) volume 0 1 := by
  unfold NlsGge.SpectralFoundations.rowSumNorm2
  have h0 := ((hF 0 0).norm).add ((hF 0 1).norm)
  have h1 := ((hF 1 0).norm).add ((hF 1 1).norm)
  exact ⟨h0.1.sup h1.1, h0.2.sup h1.2⟩

/-- Entrywise integral of a matrix path over `[0,t]`. -/
def matIntegral (G : ℝ → Mat2) (t : ℝ) : Mat2 :=
  Matrix.of fun i j => ∫ s in (0:ℝ)..t, G s i j

theorem rowSumNorm2_matIntegral_le {G : ℝ → Mat2} (hG : EntryII G) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) {c : ℝ → ℝ}
    (hc : IntervalIntegrable c volume 0 t)
    (hGc : ∀ s ∈ Set.Icc (0:ℝ) t, rowSumNorm2 (G s) ≤ c s) :
    rowSumNorm2 (matIntegral G t) ≤ ∫ s in (0:ℝ)..t, c s := by
  rw [rowSumNorm2_le_iff]
  intro i
  have hsub : Set.uIcc (0:ℝ) t ⊆ Set.uIcc 0 1 :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (by simpa [Set.uIcc_of_le zero_le_one] using ht)
  have hi : ∀ j : Fin 2, IntervalIntegrable (fun s => ‖G s i j‖) volume 0 t :=
    fun j => ((hG i j).mono_set hsub).norm
  have h0 : ‖matIntegral G t i 0‖ ≤ ∫ s in (0:ℝ)..t, ‖G s i 0‖ :=
    intervalIntegral.norm_integral_le_integral_norm ht.1
  have h1 : ‖matIntegral G t i 1‖ ≤ ∫ s in (0:ℝ)..t, ‖G s i 1‖ :=
    intervalIntegral.norm_integral_le_integral_norm ht.1
  have hsum : (∫ s in (0:ℝ)..t, ‖G s i 0‖) + (∫ s in (0:ℝ)..t, ‖G s i 1‖)
      = ∫ s in (0:ℝ)..t, (‖G s i 0‖ + ‖G s i 1‖) :=
    (intervalIntegral.integral_add (hi 0) (hi 1)).symm
  have hmono : ∫ s in (0:ℝ)..t, (‖G s i 0‖ + ‖G s i 1‖) ≤ ∫ s in (0:ℝ)..t, c s := by
    apply intervalIntegral.integral_mono_on ht.1 ((hi 0).add (hi 1)) hc
    intro s hs
    exact le_trans (rowSumNorm2_row_le (G s) i) (hGc s hs)
  linarith

/-- Entrywise absolute continuity of a product of two `2 × 2` matrix paths. -/
theorem absolutelyContinuous_mat2_mul_entry
    {f g : ℝ → Mat2}
    (hf : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => f s i j) 0 1)
    (hg : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => g s i j) 0 1)
    (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => (f s * g s) i j) 0 1 := by
  have h0 : AbsolutelyContinuousOnInterval (fun s => f s i 0 * g s 0 j) 0 1 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! (hf i 0).smul (hg 0 j)
  have h1 : AbsolutelyContinuousOnInterval (fun s => f s i 1 * g s 1 j) 0 1 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! (hf i 1).smul (hg 1 j)
  apply (h0.add h1).congr
  intro s hs
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply]

/-- Entrywise FTC for an AC matrix path with an a.e. derivative `Q`. -/
theorem mat2_entry_eq_initial_add_integral
    {P Q : ℝ → Mat2}
    (hP : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => P s i j) 0 1)
    (hQ : EntryII Q)
    (hder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => P r i j) (Q s i j) s) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ i j : Fin 2,
      P t i j = P 0 i j + ∫ s in (0:ℝ)..t, Q s i j := by
  intro t ht i j
  have huI : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  refine complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
    (hP i j) (hQ i j) ?_ t (by rwa [huI])
  filter_upwards [hder] with s hs hmem
  exact hs (by rwa [huI] at hmem) i j

/-- Generic normal-form identity (no norms): with `D' = M D`, `B' = M + E`, `D 0 = 1`,
`D t - 1 = B t D t - B 0 - ∫₀ᵗ (B M + E) D` entrywise. -/
theorem normalForm_identity
    {D B M E : ℝ → Mat2}
    (hDac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => D s i j) 0 1)
    (hBac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => B s i j) 0 1)
    (hM : EntryII M) (hE : EntryII E)
    (hDder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => D r i j) ((M s * D s) i j) s)
    (hBder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => B r i j) (M s i j + E s i j) s)
    (hD0 : D 0 = 1) :
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      D t - 1 = B t * D t - B 0 - matIntegral (fun s => (B s * M s + E s) * D s) t := by
  have hDc : EntryCont D := fun i j => (hDac i j).continuousOn
  have hBc : EntryCont B := fun i j => (hBac i j).continuousOn
  have hMD : EntryII (fun s => M s * D s) := hM.mul_cont hDc
  have hED : EntryII (fun s => E s * D s) := hE.mul_cont hDc
  have hBMD : EntryII (fun s => B s * (M s * D s)) := hBc.mul_II hMD
  have hG : EntryII (fun s => (B s * M s + E s) * D s) :=
    ((hBc.mul_II hM).add hE).mul_cont hDc
  have hQ : EntryII (fun s => (M s + E s) * D s + B s * (M s * D s)) :=
    ((hM.add hE).mul_cont hDc).add hBMD
  -- FTC for D
  have hD := mat2_entry_eq_initial_add_integral hDac hMD hDder
  -- FTC for B D
  have hBDac := absolutelyContinuous_mat2_mul_entry hBac hDac
  have hBDder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 → ∀ i j : Fin 2,
      HasDerivAt (fun r => (B r * D r) i j)
        (((M s + E s) * D s + B s * (M s * D s)) i j) s := by
    filter_upwards [hDder, hBder] with s hd hb hmem i j
    have h1 := hb hmem
    have h2 := hd hmem
    have key : HasDerivAt (fun r => B r i 0 * D r 0 j + B r i 1 * D r 1 j)
        ((M s i 0 + E s i 0) * D s 0 j + B s i 0 * (M s * D s) 0 j +
          ((M s i 1 + E s i 1) * D s 1 j + B s i 1 * (M s * D s) 1 j)) s :=
      ((h1 i 0).mul (h2 0 j)).add ((h1 i 1).mul (h2 1 j))
    have e : (fun r => (B r * D r) i j) = fun r => B r i 0 * D r 0 j + B r i 1 * D r 1 j := by
      funext r
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e]
    refine key.congr_deriv ?_
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hBD := mat2_entry_eq_initial_add_integral hBDac hQ hBDder
  intro t ht
  ext i j
  have hsub : Set.uIcc (0:ℝ) t ⊆ Set.uIcc 0 1 :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (by simpa [Set.uIcc_of_le zero_le_one] using ht)
  have iMD : IntervalIntegrable (fun s => (M s * D s) i j) volume 0 t :=
    (hMD i j).mono_set hsub
  have iG : IntervalIntegrable (fun s => ((B s * M s + E s) * D s) i j) volume 0 t :=
    (hG i j).mono_set hsub
  have hsplit : ∫ s in (0:ℝ)..t, (((M s + E s) * D s + B s * (M s * D s)) i j)
      = (∫ s in (0:ℝ)..t, (M s * D s) i j)
        + ∫ s in (0:ℝ)..t, ((B s * M s + E s) * D s) i j := by
    rw [← intervalIntegral.integral_add iMD iG]
    congr 1
    funext s
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e1 := hBD t ht i j
  have e2 := hD t ht i j
  rw [hsplit] at e1
  have hD0' : D 0 i j = (1 : Mat2) i j := by rw [hD0]
  simp only [Matrix.sub_apply, matIntegral, Matrix.of_apply]
  have hB0 : (B 0 * D 0) i j = B 0 i j := by rw [hD0, Matrix.mul_one]
  rw [hB0] at e1
  rw [hD0'] at e2
  linear_combination e2 - e1

/-- The `ℝ`-valued integral of the (nonnegative, interval-integrable) majorant is bounded by
`η` as soon as the corresponding `ENNReal` lower integral over `[0,1]` is. -/
theorem integral_le_of_lintegral_le {h : ℝ → ℝ} (hh : IntervalIntegrable h volume 0 1)
    (hnn : ∀ s, 0 ≤ h s) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫⁻ s in Set.Icc (0:ℝ) 1, ENNReal.ofReal (h s) ≤ ENNReal.ofReal η) :
    ∫ s in (0:ℝ)..1, h s ≤ η := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hint : IntegrableOn h (Set.Ioc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hh
  have h1 := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)
  have h2 : ∫⁻ s in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (h s)
      = ∫⁻ s in Set.Icc (0:ℝ) 1, ENNReal.ofReal (h s) :=
    setLIntegral_congr Ioc_ae_eq_Icc
  rw [← h2, ← h1] at hη
  exact (ENNReal.ofReal_le_ofReal_iff hη0).1 hη

/-- **Normal-form integration-by-parts estimate.**  Norm: `rowSumNorm2` (maximal row sum),
submultiplicative with `‖1‖ = 1`.  Hypotheses: `D, B` entrywise absolutely continuous on
`[0,1]`; `D' = M D` and `B' = M + E` a.e. on `[0,1]` (entrywise `HasDerivAt`); `M, E`
entrywise interval integrable; `D 0 = 1`; `‖B t‖ ≤ β` on `[0,1]`; and the lower integral
`∫⁻_{[0,1]} ofReal (‖B M‖ + ‖E‖) ≤ ofReal η`; `0 ≤ β ≤ 1/4`, `0 ≤ η ≤ 1/8`.
Conclusion: for every `t ∈ [0,1]`, `‖D t‖ ≤ 2` and `‖D t - 1‖ ≤ 3 β + 2 η`. -/
theorem normalForm_sub_one_bound
    (D B M E : ℝ → Mat2) (β η : ℝ)
    (hDac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => D s i j) 0 1)
    (hBac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => B s i j) 0 1)
    (hM : ∀ i j : Fin 2, IntervalIntegrable (fun s => M s i j) volume 0 1)
    (hE : ∀ i j : Fin 2, IntervalIntegrable (fun s => E s i j) volume 0 1)
    (hDder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => D r i j) ((M s * D s) i j) s)
    (hBder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => B r i j) (M s i j + E s i j) s)
    (hD0 : D 0 = 1)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (B t) ≤ β)
    (hη : ∫⁻ s in Set.Icc (0:ℝ) 1,
        ENNReal.ofReal (rowSumNorm2 (B s * M s) + rowSumNorm2 (E s)) ≤ ENNReal.ofReal η)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1/4) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/8) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (D t) ≤ 2 ∧ rowSumNorm2 (D t - 1) ≤ 3 * β + 2 * η := by
  have huI : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hid := normalForm_identity hDac hBac hM hE hDder hBder hD0
  have hDc : EntryCont D := fun i j => (hDac i j).continuousOn
  have hBc : EntryCont B := fun i j => (hBac i j).continuousOn
  have hG : EntryII (fun s => (B s * M s + E s) * D s) :=
    ((hBc.mul_II hM).add hE).mul_cont hDc
  -- majorant
  set h : ℝ → ℝ := fun s => rowSumNorm2 (B s * M s) + rowSumNorm2 (E s) with hhdef
  have hhi : IntervalIntegrable h volume 0 1 :=
    (EntryII.rowSumNorm2 (hBc.mul_II hM)).add (EntryII.rowSumNorm2 hE)
  have hhnn : ∀ s, 0 ≤ h s := fun s =>
    add_nonneg (rowSumNorm2_nonneg _) (rowSumNorm2_nonneg _)
  have hint : ∫ s in (0:ℝ)..1, h s ≤ η := integral_le_of_lintegral_le hhi hhnn hη0 hη
  -- supremum of ‖D‖ on [0,1]
  have hDcont : ContinuousOn (fun s => rowSumNorm2 (D s)) (Set.Icc (0:ℝ) 1) := by
    unfold rowSumNorm2
    have hc : ∀ i j : Fin 2, ContinuousOn (fun s => ‖D s i j‖) (Set.Icc (0:ℝ) 1) :=
      fun i j => by rw [← huI]; exact (hDc i j).norm
    exact ContinuousOn.sup ((hc 0 0).add (hc 0 1)) ((hc 1 0).add (hc 1 1))
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (zero_le_one : (0:ℝ) ≤ 1)) hDcont
  set S : ℝ := rowSumNorm2 (D t0) with hS
  have hSnn : 0 ≤ S := rowSumNorm2_nonneg _
  have hDS : ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (D t) ≤ S := fun t ht => hmax ht
  -- the integral term
  have hI : ∀ t ∈ Set.Icc (0:ℝ) 1,
      rowSumNorm2 (matIntegral (fun s => (B s * M s + E s) * D s) t) ≤ η * S := by
    intro t ht
    have hsub : Set.uIcc (0:ℝ) t ⊆ Set.uIcc 0 1 :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [huI]; exact ht)
    have hct : IntervalIntegrable (fun s => h s * S) volume 0 t :=
      (hhi.mono_set hsub).mul_const S
    have h1 := rowSumNorm2_matIntegral_le hG ht hct (by
      intro s hs
      have hs1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1, le_trans hs.2 ht.2⟩
      calc rowSumNorm2 ((B s * M s + E s) * D s)
          ≤ rowSumNorm2 (B s * M s + E s) * rowSumNorm2 (D s) := rowSumNorm2_mul_le _ _
        _ ≤ h s * S := by
          apply mul_le_mul (rowSumNorm2_add_le _ _) (hDS s hs1) (rowSumNorm2_nonneg _)
          exact hhnn s)
    have h2 : ∫ s in (0:ℝ)..t, h s * S = (∫ s in (0:ℝ)..t, h s) * S :=
      intervalIntegral.integral_mul_const S _
    have h3 : ∫ s in (0:ℝ)..t, h s ≤ ∫ s in (0:ℝ)..1, h s :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (ae_of_all _ hhnn) hhi
    rw [h2] at h1
    nlinarith
  -- pointwise estimate
  have hDm1 : ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (D t - 1) ≤ β * S + β + η * S := by
    intro t ht
    have e := hid t ht
    rw [e]
    have a1 : rowSumNorm2 (B t * D t) ≤ β * S :=
      le_trans (rowSumNorm2_mul_le _ _)
        (mul_le_mul (hB t ht) (hDS t ht) (rowSumNorm2_nonneg _) hβ0)
    have a2 : rowSumNorm2 (B 0) ≤ β := hB 0 ⟨le_rfl, zero_le_one⟩
    have a3 := hI t ht
    have b1 := rowSumNorm2_sub_le (B t * D t - B 0)
      (matIntegral (fun s => (B s * M s + E s) * D s) t)
    have b2 := rowSumNorm2_sub_le (B t * D t) (B 0)
    linarith
  have hDnorm : ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (D t) ≤ 1 + (β * S + β + η * S) := by
    intro t ht
    have e : D t = 1 + (D t - 1) := by abel
    have := rowSumNorm2_add_le (1 : Mat2) (D t - 1)
    rw [← e, rowSumNorm2_one] at this
    linarith [hDm1 t ht]
  have hS2 : S ≤ 2 := by
    have h0 := hDnorm t0 ht0
    by_contra hcon
    replace hcon := not_le.1 hcon
    nlinarith [mul_pos (sub_pos.2 hcon) (show 0 < 1 - β - η by linarith)]
  intro t ht
  have hb := hDm1 t ht
  have hbb : (β + η) * S ≤ (β + η) * 2 := mul_le_mul_of_nonneg_left hS2 (by linarith)
  refine ⟨le_trans (hDS t ht) hS2, ?_⟩
  nlinarith

/-- Corollary with the cruder constants `4 β + 8 η`. -/
theorem normalForm_sub_one_bound_four_eight
    (D B M E : ℝ → Mat2) (β η : ℝ)
    (hDac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => D s i j) 0 1)
    (hBac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => B s i j) 0 1)
    (hM : ∀ i j : Fin 2, IntervalIntegrable (fun s => M s i j) volume 0 1)
    (hE : ∀ i j : Fin 2, IntervalIntegrable (fun s => E s i j) volume 0 1)
    (hDder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => D r i j) ((M s * D s) i j) s)
    (hBder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => B r i j) (M s i j + E s i j) s)
    (hD0 : D 0 = 1)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (B t) ≤ β)
    (hη : ∫⁻ s in Set.Icc (0:ℝ) 1,
        ENNReal.ofReal (rowSumNorm2 (B s * M s) + rowSumNorm2 (E s)) ≤ ENNReal.ofReal η)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1/4) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/8) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (D t - 1) ≤ 4 * β + 8 * η := by
  intro t ht
  have := (normalForm_sub_one_bound D B M E β η hDac hBac hM hE hDder hBder hD0 hB hη
    hβ0 hβ hη0 hη1 t ht).2
  linarith

end NlsGge.SpectralFoundations
end
