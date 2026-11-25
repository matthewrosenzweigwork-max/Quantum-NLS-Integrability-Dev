import NlsGge.Spectral.ActualHalfTraceUniformBox38V1
import NlsGge.Spectral.DissipativeNormalFormUniformBox38V1
import NlsGge.Spectral.ActualH1ACRepresentativeUniformBox38V1
import Mathlib.Analysis.Calculus.Deriv.Star
import NlsGge.Spectral.ActualGapsActionsE02_38
import NlsGge.Spectral.ActualOppositeParityExclusionE02_38

/-!
# Uniform box estimate (UB-C2): normalized half-trace defect on the half-strip

For an H¹ potential with `‖u‖_{H¹} ≤ R`, `R ≥ 1`, and `|n| ≥ K R^2` (`K`
absolute), on the closed half-strip `|Re z - nπ| ≤ 1`, `Im z ≥ 0` (ALL heights),
`‖e^{iz} Δh(u,z) - (1 + e^{2iz})/2‖ ≤ C R^2/|n|`.
Proof: dissipative normal form (UB-B2) for `Φ = diag(1,e^{2itz}) D` with
`B = [[0, f/(2z)], [f̄/(2z), 0]]`, `f` the absolutely continuous representative (UB-A).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

theorem uniformBox_dnfLam_eq38 (z : ℂ) :
    dnfLam (2 * Complex.I * z) = uniformBoxLambda38 z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dnfLam, uniformBoxLambda38]

/-- The normal-form transform built from a function `f`. -/
def uniformBoxB38 (f : ℝ → ℂ) (z : ℂ) (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, f s * (2 * z)⁻¹; star (f s) * (2 * z)⁻¹, 0]

/-- Per-representative bound with explicit sizes `A` (sup of `f`) and `a`
(`L¹` norm of `f'`). -/
theorem uniformBox_normalized_bound_of_rep38
    (u : PhysicalL2) (f f' : ℝ → ℂ) (A a : ℝ)
    (hfac : AbsolutelyContinuousOnInterval f 0 1)
    (hf'i : IntervalIntegrable f' volume 0 1)
    (hder : ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt f (f' t) t)
    (hae : f =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] uniformBoxPotential38 u)
    (hfb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f t‖ ≤ A)
    (hf'b : ∫ t in (0 : ℝ)..1, ‖f' t‖ ≤ a)
    (z : ℂ) (hz : 0 ≤ z.im) (hz0 : 0 < ‖z‖)
    (hβ : A / (2 * ‖z‖) ≤ 1 / 4) (hη : (A ^ 2 + a) / (2 * ‖z‖) ≤ 1 / 8) :
    ‖Complex.exp (Complex.I * z) * actualPhysicalUnitHalfTrace32 u z -
        (1 + Complex.exp (2 * Complex.I * z)) / 2‖ ≤
      8 / 3 * (A / (2 * ‖z‖) + (A ^ 2 + a) / (2 * ‖z‖)) := by
  have hzne : z ≠ 0 := norm_pos_iff.mp hz0
  have h2z : (2 * z) ≠ 0 := mul_ne_zero two_ne_zero hzne
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hfb 0 ⟨le_rfl, zero_le_one⟩)
  have ha0 : 0 ≤ a := le_trans (intervalIntegral.integral_nonneg zero_le_one
    (fun t _ => norm_nonneg (f' t))) hf'b
  have hn2z : ‖(2 * z)⁻¹‖ = 1 / (2 * ‖z‖) := by
    rw [norm_inv, norm_mul]; simp
  set μ : ℂ := 2 * Complex.I * z with hμdef
  have hμ : μ.re ≤ 0 := by
    simp [hμdef, Complex.mul_re]; linarith
  set U : ℝ → ℂ := uniformBoxPotential38 u with hU
  set Φ := uniformBoxNormalizedState38 u z with hΦ
  set V : ℝ → Matrix (Fin 2) (Fin 2) ℂ := uniformBoxV38 U with hV
  set B : ℝ → Matrix (Fin 2) (Fin 2) ℂ := uniformBoxB38 f z with hB
  set W : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
    fun s => !![0, f' s * (2 * z)⁻¹; star (f' s) * (2 * z)⁻¹, 0] with hW
  -- a.e. equality of the representatives on `[0,1]`
  have hUf : ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) 1 → U s = f s := by
    have h1 : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) 1 → f s = U s :=
      (ae_restrict_iff' measurableSet_Ioc).mp hae
    have h2 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := dnf_ae_ne 0
    filter_upwards [h1, h2] with s hs1 hs2 hs
    exact (hs1 ⟨lt_of_le_of_ne hs.1 (Ne.symm hs2), hs.2⟩).symm
  have hfc : ContinuousOn f (Set.uIcc (0 : ℝ) 1) := hfac.continuousOn
  have hfi : IntervalIntegrable f volume 0 1 := hfc.intervalIntegrable
  have hsfi : IntervalIntegrable (fun s => star (f s)) volume 0 1 :=
    (continuous_star.comp_continuousOn hfc).intervalIntegrable
  have hUi : IntervalIntegrable U volume 0 1 := by
    refine hfi.congr_ae ?_
    rw [Set.uIoc_of_le zero_le_one]
    exact hae
  have hsUi : IntervalIntegrable (fun s => star (U s)) volume 0 1 := by
    refine hsfi.congr_ae ?_
    rw [Set.uIoc_of_le zero_le_one]
    filter_upwards [hae] with s hs
    simp [hs]
  have hsf'i : IntervalIntegrable (fun s => star (f' s)) volume 0 1 := by
    refine hf'i.mono_fun ?_ ?_
    · exact (hf'i.def'.aestronglyMeasurable).star
    · filter_upwards with s
      simp
  -- hypotheses of the dissipative normal form
  have hΦac := uniformBoxNormalizedState38_ac u z
  have hconst : ContDiff ℝ 1 (fun _ : ℝ => (2 * z)⁻¹) := contDiff_const
  have hBac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => B s i j) 0 1 := by
    have hsfac : AbsolutelyContinuousOnInterval (fun s => star (f s)) 0 1 := by
      have := (Complex.conjLIE.lipschitz).comp_absolutelyContinuousOnInterval hfac
      convert this using 1
      funext s
      rfl
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [hB, uniformBoxB38] using dnf_ac_of_contDiff (contDiff_const (c := (0 : ℂ)))
    · simpa [hB, uniformBoxB38] using dnf_ac_mul hfac (dnf_ac_of_contDiff hconst)
    · simpa [hB, uniformBoxB38] using dnf_ac_mul hsfac (dnf_ac_of_contDiff hconst)
    · simpa [hB, uniformBoxB38] using dnf_ac_of_contDiff (contDiff_const (c := (0 : ℂ)))
  have hVi : ∀ i j : Fin 2, IntervalIntegrable (fun s => V s i j) volume 0 1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp [hV, uniformBoxV38]
    · simpa [hV, uniformBoxV38] using hUi.const_mul Complex.I
    · simpa [hV, uniformBoxV38] using hsUi.const_mul (-Complex.I)
    · simp [hV, uniformBoxV38]
  have hWi : ∀ i j : Fin 2, IntervalIntegrable (fun s => W s i j) volume 0 1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp [hW]
    · simpa [hW] using hf'i.mul_const (2 * z)⁻¹
    · simpa [hW] using hsf'i.mul_const (2 * z)⁻¹
    · simp [hW]
  have hΦder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => Φ r i j) (((dnfLam μ + V s) * Φ s) i j) s := by
    rw [hμdef, uniformBox_dnfLam_eq38]
    exact uniformBoxNormalizedState38_ae_hasDerivAt u z
  have hBder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => B r i j) (W s i j) s := by
    filter_upwards [hder] with s hs hsI i j
    have hsu : s ∈ Set.uIcc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one]
    have h1 := (hs hsu).mul_const (2 * z)⁻¹
    have h2 := ((hs hsu).star).mul_const (2 * z)⁻¹
    fin_cases i <;> fin_cases j
    · simpa [hB, hW, uniformBoxB38] using hasDerivAt_const s (0 : ℂ)
    · simpa [hB, hW, uniformBoxB38] using h1
    · simpa [hB, hW, uniformBoxB38] using h2
    · simpa [hB, hW, uniformBoxB38] using hasDerivAt_const s (0 : ℂ)
  have hcomm : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      dnfLam μ * B s - B s * dnfLam μ + V s = 0 := by
    filter_upwards [hUf] with s hs hsI
    have hUs := hs hsI
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dnfLam, hB, uniformBoxB38, hV, uniformBoxV38, Matrix.mul_apply, Fin.sum_univ_two,
        hμdef, hUs] <;> field_simp <;> ring
  have hBb : ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (B t) ≤ A / (2 * ‖z‖) := by
    intro t ht
    have hft := hfb t ht
    simp only [rowSumNorm2, hB, uniformBoxB38]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, norm_zero, zero_add,
      add_zero, norm_mul, norm_star, hn2z]
    apply max_le <;>
      · rw [mul_one_div]
        exact div_le_div_of_nonneg_right hft (by positivity)
  -- the `L¹` smallness
  set η : ℝ := (A ^ 2 + a) / (2 * ‖z‖) with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hpt : ∀ᵐ s ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      ENNReal.ofReal (rowSumNorm2 (V s * B s - W s)) ≤
        ENNReal.ofReal ((A ^ 2 + ‖f' s‖) / (2 * ‖z‖)) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hUf] with s hs hsI
    apply ENNReal.ofReal_le_ofReal
    have hUs := hs hsI
    have hft := hfb s hsI
    have hUf2 : ‖U s‖ * ‖f s‖ ≤ A ^ 2 := by
      rw [hUs]; nlinarith [norm_nonneg (f s)]
    set c : ℂ := (2 * z)⁻¹ with hc
    have hform : V s * B s - W s =
        !![Complex.I * U s * (star (f s) * c), -(f' s * c);
          -(star (f' s) * c), -Complex.I * star (U s) * (f s * c)] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hV, uniformBoxV38, hB, uniformBoxB38, hW, Matrix.mul_apply, Fin.sum_univ_two, hc]
    rw [hform]
    have hcn : ‖c‖ = 1 / (2 * ‖z‖) := hn2z
    have hc0 : 0 ≤ 1 / (2 * ‖z‖) := by positivity
    simp only [rowSumNorm2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      norm_neg, norm_mul, norm_star, Complex.norm_I, one_mul, hcn]
    have hrhs : (A ^ 2 + ‖f' s‖) / (2 * ‖z‖) = (A ^ 2 + ‖f' s‖) * (1 / (2 * ‖z‖)) := by ring
    have hk := mul_le_mul_of_nonneg_right hUf2 hc0
    apply max_le <;> nlinarith [norm_nonneg (f s), norm_nonneg (U s), norm_nonneg (f' s)]
  have hgi : IntegrableOn (fun s => (A ^ 2 + ‖f' s‖) / (2 * ‖z‖)) (Set.Icc (0:ℝ) 1) := by
    have h1 : IntervalIntegrable (fun s => (A ^ 2 + ‖f' s‖) / (2 * ‖z‖)) volume 0 1 :=
      (intervalIntegrable_const.add hf'i.norm).div_const _
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at h1
    exact h1
  have hηb : ∫⁻ s in Set.Icc (0:ℝ) 1,
      ENNReal.ofReal (rowSumNorm2 (V s * B s - W s)) ≤ ENNReal.ofReal η := by
    refine le_trans (lintegral_mono_ae hpt) ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall
      (fun s => by positivity))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
      hf'i.norm, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, one_mul]
    rw [hηdef]
    gcongr
  have hmain := dissipativeNormalForm_bound μ Φ B V W (A / (2 * ‖z‖)) η hμ hΦac hBac hVi hWi
    hΦder hBder (uniformBoxNormalizedState38_zero u z) hcomm hBb hηb hβ hη0 hη
    1 ⟨zero_le_one, le_rfl⟩
  have e00 : (Φ 1 - dnfExp μ 1) 0 0 = Φ 1 0 0 - 1 := by simp [dnfExp]
  have e11 : (Φ 1 - dnfExp μ 1) 1 1 = Φ 1 1 1 - Complex.exp μ := by simp [dnfExp]
  have h00 := rowSumNorm2_entry_le (Φ 1 - dnfExp μ 1) 0 0
  have h11 := rowSumNorm2_entry_le (Φ 1 - dnfExp μ 1) 1 1
  rw [e00] at h00
  rw [e11] at h11
  rw [uniformBox_normalizedHalfTrace_eq38]
  rw [hμdef] at h11
  rw [norm_div, Complex.norm_two]
  calc ‖Φ 1 0 0 - 1 + (Φ 1 1 1 - Complex.exp (2 * Complex.I * z))‖ / 2
      ≤ (‖Φ 1 0 0 - 1‖ + ‖Φ 1 1 1 - Complex.exp (2 * Complex.I * z)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ ≤ (8 / 3 * (A / (2 * ‖z‖) + η) + 8 / 3 * (A / (2 * ‖z‖) + η)) / 2 := by
        gcongr
        · exact le_trans h00 hmain.1
        · exact le_trans h11 hmain.1
    _ = 8 / 3 * (A / (2 * ‖z‖) + (A ^ 2 + a) / (2 * ‖z‖)) := by rw [hηdef]; ring

/-- The normalized half-strip estimate, uniform in the potential on H¹ balls and in all
heights `Im z ≥ 0`: there are absolute constants `K, C > 0` such that for `R ≥ 1`,
`‖u‖_{H¹} ≤ R`, `|n| ≥ K R^2`, `|Re z - nπ| ≤ 1`, `Im z ≥ 0`:
`‖e^{iz} Δh(u,z) - (1 + e^{2iz})/2‖ ≤ C R^2/|n|`. -/
theorem actualHalfTrace_uniformHalfStrip38 :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ R → ∀ n : ℤ, K * R ^ 2 ≤ |(n : ℝ)| →
        ∀ z : ℂ, |z.re - n * Real.pi| ≤ 1 → 0 ≤ z.im →
          ‖Complex.exp (Complex.I * z) * actualPhysicalUnitHalfTrace32 u z -
              (1 + Complex.exp (2 * Complex.I * z)) / 2‖ ≤ C * R ^ 2 / |(n : ℝ)| := by
  obtain ⟨Ci, C1, hCi, hC1, hrep⟩ := NlsGge.Schur.actualH1ACRepresentativeUniformBox38V1
  set K0 : ℝ := Ci + Ci ^ 2 + C1 with hK0
  have hK0pos : 0 < K0 := by positivity
  refine ⟨2 * K0 + 1, 4 / 3 * K0, by positivity, by positivity, ?_⟩
  intro R hR u hu huR n hn z hzre hzim
  obtain ⟨f, f', hfac, hf'i, hder, hae, hfb, hf'b⟩ := hrep u hu
  set N : ℝ := |(n : ℝ)| with hN
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hRR2 : R ≤ R ^ 2 := by nlinarith
  have hN1 : 1 ≤ N := by nlinarith
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  -- `|z| ≥ 2 |n|`
  have hzN : 2 * N ≤ ‖z‖ := by
    have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h1 : N * Real.pi - 1 ≤ |z.re| := by
      have := abs_sub_abs_le_abs_sub (n * Real.pi) z.re
      rw [abs_sub_comm] at this
      have hnp : |(n : ℝ) * Real.pi| = N * Real.pi := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
      linarith
    nlinarith
  have hz0 : 0 < ‖z‖ := by linarith
  -- the sizes
  set A : ℝ := Ci * ‖physicalSobolevL2 1 u hu‖ with hA
  set a : ℝ := C1 * ‖physicalSobolevL2 1 u hu‖ with ha
  have hAR : A ≤ Ci * R := mul_le_mul_of_nonneg_left huR hCi.le
  have haR : a ≤ C1 * R := mul_le_mul_of_nonneg_left huR hC1.le
  have hA0 : 0 ≤ A := by positivity
  have ha0 : 0 ≤ a := by positivity
  have hden : 0 < 2 * ‖z‖ := by positivity
  have hβ' : A / (2 * ‖z‖) ≤ K0 * R ^ 2 / (4 * N) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have : A * (4 * N) ≤ K0 * R ^ 2 * (2 * ‖z‖) := by
      have h1 : A ≤ K0 * R ^ 2 := by
        have : Ci * R ≤ K0 * R ^ 2 := by
          have : Ci ≤ K0 := by rw [hK0]; nlinarith [sq_nonneg Ci]
          nlinarith
        linarith
      nlinarith
    linarith
  have hη' : (A ^ 2 + a) / (2 * ‖z‖) ≤ K0 * R ^ 2 / (4 * N) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have hA2 : A ^ 2 ≤ Ci ^ 2 * R ^ 2 := by
      have := pow_le_pow_left₀ hA0 hAR 2
      nlinarith
    have h1 : A ^ 2 + a ≤ K0 * R ^ 2 := by
      have : C1 * R ≤ C1 * R ^ 2 := mul_le_mul_of_nonneg_left hRR2 hC1.le
      rw [hK0]; nlinarith [sq_nonneg R]
    have : (A ^ 2 + a) * (4 * N) ≤ K0 * R ^ 2 * (2 * ‖z‖) := by nlinarith
    linarith
  have hsmall : K0 * R ^ 2 / (4 * N) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h := uniformBox_normalized_bound_of_rep38 u f f' A a hfac hf'i hder hae hfb hf'b z hzim
    hz0 (by linarith) (by linarith)
  calc _ ≤ 8 / 3 * (A / (2 * ‖z‖) + (A ^ 2 + a) / (2 * ‖z‖)) := h
    _ ≤ 8 / 3 * (K0 * R ^ 2 / (4 * N) + K0 * R ^ 2 / (4 * N)) := by gcongr
    _ = 4 / 3 * K0 * R ^ 2 / N := by field_simp; ring

/-- The uniform box estimate in E02's interface `ActualHalfTraceBoxE02_38`
(`|Re z - nπ| ≤ 1`, `|Im z| ≤ 1`, all of it, via conjugation for `Im z < 0`). -/
theorem actualHalfTraceBox_uniform38 :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ R → ∀ n : ℤ, K * R ^ 2 ≤ |(n : ℝ)| →
          ActualHalfTraceBoxE02_38 u n (C * R ^ 2 / |(n : ℝ)|) := by
  obtain ⟨K, C, hK, hC, h⟩ := actualHalfTrace_uniformHalfStrip38
  refine ⟨K, Real.exp 1 * C, hK, by positivity, ?_⟩
  intro R hR u hu huR n hn z hzre hzim
  -- reduce to `Im ≥ 0`
  have key : ∀ w : ℂ, |w.re - n * Real.pi| ≤ 1 → 0 ≤ w.im → w.im ≤ 1 →
      ‖actualPhysicalUnitHalfTrace32 u w - Complex.cos w‖ ≤
        Real.exp 1 * C * R ^ 2 / |(n : ℝ)| := by
    intro w hwre hw0 hw1
    have hb := h R hR u hu huR n hn w hwre hw0
    have hid : actualPhysicalUnitHalfTrace32 u w - Complex.cos w =
        Complex.exp (-(Complex.I * w)) *
          (Complex.exp (Complex.I * w) * actualPhysicalUnitHalfTrace32 u w -
            (1 + Complex.exp (2 * Complex.I * w)) / 2) := by
      rw [Complex.cos]
      have h1 : Complex.exp (-(Complex.I * w)) * Complex.exp (Complex.I * w) = 1 := by
        rw [← Complex.exp_add]; simp
      have h2 : Complex.exp (-(Complex.I * w)) * Complex.exp (2 * Complex.I * w) =
          Complex.exp (w * Complex.I) := by
        rw [← Complex.exp_add]; congr 1; ring
      have h3 : Complex.exp (-(Complex.I * w)) = Complex.exp (-w * Complex.I) := by
        congr 1; ring
      linear_combination (-actualPhysicalUnitHalfTrace32 u w) * h1 + (1/2 : ℂ) * h2 +
        (1/2 : ℂ) * h3
    rw [hid, norm_mul]
    have he : ‖Complex.exp (-(Complex.I * w))‖ ≤ Real.exp 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp; linarith
    calc ‖Complex.exp (-(Complex.I * w))‖ * _ ≤ Real.exp 1 * (C * R ^ 2 / |(n : ℝ)|) :=
          mul_le_mul he hb (norm_nonneg _) (by positivity)
      _ = Real.exp 1 * C * R ^ 2 / |(n : ℝ)| := by ring
  rcases le_or_gt 0 z.im with hz0 | hz0
  · exact key z hzre hz0 (le_of_abs_le hzim)
  · have hc := key (starRingEnd ℂ z) (by simpa using hzre) (by simp; linarith)
      (by simp; linarith [neg_abs_le z.im, (abs_le.mp hzim).1])
    rw [actualPhysicalUnitHalfTrace32_conj_E02_38, Complex.cos_conj, ← map_sub,
      Complex.norm_conj] at hc
    exact hc

open TransportBridgeV4 in
/-- Uniform opposite-parity exclusion (B5, uniform form): for `‖u‖_{H¹} ≤ R` and
`|n| ≥ K R^2`, the sector-`(n+1)` source operator for `(u, ū)` has no eigenvalue with
`|Re z - nπ| ≤ 1`. -/
theorem no_oppositeParity_eigenvalue_uniform38 :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ R → ∀ n : ℤ, K * R ^ 2 ≤ |(n : ℝ)| →
        ∀ z : ℂ, |z.re - (n : ℝ) * Real.pi| ≤ 1 →
          ¬ ∃ X : recoveredActualSourceFreeWeightedDomain (n + 1), X.val ≠ 0 ∧
            actualSourcePerturbedDiracPMapAfterAE (n + 1) u (star u) X = z • X.val := by
  obtain ⟨K, C, hK, hC, h⟩ := actualHalfTraceBox_uniform38
  refine ⟨K + 1000 * C, by positivity, ?_⟩
  intro R hR u hu huR n hn z hz
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hnK : K * R ^ 2 ≤ |((-n : ℤ) : ℝ)| := by
    rw [Int.cast_neg, abs_neg]
    nlinarith
  have hbox := h R hR u hu huR (-n) hnK
  have hNpos : 0 < |((-n : ℤ) : ℝ)| := lt_of_lt_of_le (by positivity) hnK
  have hδ : C * R ^ 2 / |((-n : ℤ) : ℝ)| ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]
    rw [Int.cast_neg, abs_neg]
    nlinarith
  exact no_oppositeParity_eigenvalue_E02_38 u n _ hδ hbox z hz

end NlsGge.SpectralFoundations
end
