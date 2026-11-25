import Mathlib
import QuantumNLS.RiccatiModeAnalytic
import QuantumNLS.RiccatiSectorBounds
import QuantumNLS.RiccatiC1
import QuantumNLS.RiccatiUniformK

/-!
# R-3FEAD88B: the printed local output (`LocalOutput`) for a smooth base

`riccati_main_full` constructs a `LocalOutput L f M a S δ K hL ha` from a base `base` with
`physRep L a (lowT L a S base) = f`. The radii are `βV = ‖base‖ + 1` (the open set `V`),
`B = ‖base‖ + 3` (expansion radius), `βu = B + 1 + Dbig` (uniqueness radius), `C = 4 βu`, and `R`
from `RiccatiSectorBounds.exists_R`. The derivative halves come from the Cauchy estimate
`RiccatiC1.norm_fderiv_le_of_ball` with radius `1`, applied to the uniform sup bounds of the
frozen `value_remainder` and `log_value`. Analyticity comes from `RiccatiCoeffAnalytic` and
`RiccatiModeAnalytic`.

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex

namespace QuantumNLS.RiccatiMainFull

open QuantumNLS.SmoothScalarMomentsPrerequisite QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiGlobal QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiCoeffAnalytic QuantumNLS.RiccatiModeAnalytic
open QuantumNLS.RiccatiSectorBounds QuantumNLS.RiccatiUniformK QuantumNLS.RiccatiC1

/-- A point of the closed radius-`1` ball around `p` has norms at most `‖p.i‖ + 1`. -/
theorem ball_norm_le {p q : Ell2 × Ell2} (h : dist q p ≤ 1) :
    ‖q.1‖ ≤ ‖p.1‖ + 1 ∧ ‖q.2‖ ≤ ‖p.2‖ + 1 := by
  rw [Prod.dist_eq] at h
  have h1 : dist q.1 p.1 ≤ 1 := le_trans (le_max_left _ _) h
  have h2 : dist q.2 p.2 ≤ 1 := le_trans (le_max_right _ _) h
  rw [dist_eq_norm] at h1 h2
  constructor
  · calc ‖q.1‖ = ‖(q.1 - p.1) + p.1‖ := by rw [sub_add_cancel]
      _ ≤ ‖q.1 - p.1‖ + ‖p.1‖ := norm_add_le _ _
      _ ≤ ‖p.1‖ + 1 := by linarith
  · calc ‖q.2‖ = ‖(q.2 - p.2) + p.2‖ := by rw [sub_add_cancel]
      _ ≤ ‖q.2 - p.2‖ + ‖p.2‖ := norm_add_le _ _
      _ ≤ ‖p.2‖ + 1 := by linarith

/-- Cauchy estimate in operator norm: a uniform sup bound on the radius-`1` ball gives the
operator-norm bound on the derivative. -/
theorem deriv_opnorm_le {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {F : E → G} {p : E} {c Kc : ℝ} (hKc : 0 ≤ Kc)
    (hdiff : ∀ q : E, dist q p ≤ 1 → DifferentiableAt ℂ F q)
    (hbd : ∀ q : E, dist q p ≤ 1 → ‖F q‖ ≤ c) (hc : c ≤ Kc) :
    ‖fderiv ℂ F p‖ ≤ Kc := by
  refine ContinuousLinearMap.opNorm_le_bound _ hKc (fun d => ?_)
  have h := QuantumNLS.RiccatiC1.norm_fderiv_le_of_ball (F := F) (p₀ := p) (ρ := 1) (C := c)
    one_pos hdiff hbd d
  rw [div_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg d))

/-- The mode sum `∑_{n=1}^M modeCoef(lowT p.2)(coeffs p n) z^{-n}` is analytic in `p`. -/
theorem modeSum_analyticAt (L : ℝ) [Fact (0 < L)] {a S : ℝ} {M : ℕ} (hL : 0 < L)
    (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (z : ℂ) (p0 : Ell2 × Ell2) :
    AnalyticAt ℂ (fun p : Ell2 × Ell2 => ∑ n ∈ Finset.Icc 1 M,
      modeCoef L a (lowT L a S p.2) (coeffs L a S κ hL ha (derivativeExtension L) p n)
        * (z⁻¹) ^ n) p0 := by
  have haS' : a ≤ S := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlowan : AnalyticAt ℂ (fun p : Ell2 × Ell2 => lowT L a S p.2) p0 :=
    analyticAt_lowT_comp (L := L) (p := a) (q := S) haS'
      (g := ⇑(ContinuousLinearMap.snd ℂ Ell2 Ell2))
      ((ContinuousLinearMap.snd ℂ Ell2 Ell2).analyticAt p0)
  apply Finset.analyticAt_fun_sum
  intro n hn
  rw [Finset.mem_Icc] at hn
  exact (modeCoef_analyticAt hL ha hlowan
    (coeffs_analyticAt L hL ha haS hM κ (derivativeExtension L)
      (fun y => derivativeExtension_spec L y) n hn.1 hn.2 p0)).mul
    (analyticAt_const : AnalyticAt ℂ (fun _ : Ell2 × Ell2 => (z⁻¹) ^ n) p0)

theorem riccati_main_full (L : ℝ) [Fact (0 < L)] {M : ℕ} {a S δ : ℝ} {K : Set ℝ} {f : ℝ → ℂ}
    (hL : 0 < L) (ha : 1 / 2 < a) (hM : 1 ≤ M) (haS : a + (M : ℝ) + 1 ≤ S) (hδ : 0 < δ)
    (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) (base : Ell2)
    (hbase : physRep L a (lowT L a S base) = f) :
    Nonempty (LocalOutput L f M a S δ K hL ha) := by
  have haS' : a ≤ S := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨k, hkpos, hkK⟩ := QuantumNLS.RiccatiUniformK.exists_abs_bound hK
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = ‖base‖ + 3 := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hB_def]; linarith [norm_nonneg base]
  obtain ⟨Dbig, hDbig⟩ : ∃ D : ℝ, D = |remC L a S M (k / L) B δ| + |logC L a S M k B δ| :=
    ⟨_, rfl⟩
  have hDbig0 : 0 ≤ Dbig := by
    rw [hDbig]
    linarith [abs_nonneg (remC L a S M (k / L) B δ), abs_nonneg (logC L a S M k B δ)]
  obtain ⟨βu, hβu_def⟩ : ∃ βu : ℝ, βu = B + 1 + Dbig := ⟨_, rfl⟩
  have hβu : 0 < βu := by rw [hβu_def]; linarith
  have hBβ : B < βu := by rw [hβu_def]; linarith
  obtain ⟨R, hRpos, h1, h9, hJ', hX, hrem, hlog⟩ :=
    exists_R L a S δ k B βu M hL hδ
  -- the constants are bounded by `4 βu` on `K`
  have hremC : ∀ κ ∈ K, remC L a S M (κ / L) B δ ≤ 4 * βu := by
    intro κ hκ
    have hκk : |κ| ≤ k := hkK κ hκ
    have hab' : |κ / L| ≤ |k / L| := by
      rw [abs_div, abs_div, abs_of_pos hL]
      exact div_le_div_of_nonneg_right (by rw [abs_of_pos hkpos]; exact hκk) hL.le
    have hmono := remC_mono L a S M (κ / L) (k / L) B δ hB.le hδ hab'
    have h2 := le_abs_self (remC L a S M (k / L) B δ)
    have h3 := abs_nonneg (logC L a S M k B δ)
    linarith [hDbig, hβu_def]
  have hlogC : ∀ κ ∈ K, logC L a S M κ B δ ≤ 4 * βu := by
    intro κ hκ
    have hκk : |κ| ≤ k := hkK κ hκ
    have habs : |κ| ≤ |k| := by rw [abs_of_pos hkpos]; exact hκk
    have hmono := logC_mono L a S M κ k B δ ha0 hL hB.le hδ habs
    have h2 := le_abs_self (logC L a S M k B δ)
    have h3 := abs_nonneg (remC L a S M (k / L) B δ)
    linarith [hDbig, hβu_def]
  -- the open set `V`
  obtain ⟨V, hV⟩ : ∃ V : Set (Ell2 × Ell2),
      V = {p | ‖p.1‖ < ‖base‖ + 1 ∧ ‖p.2‖ < ‖base‖ + 1} := ⟨_, rfl⟩
  have hVmem : ∀ p : Ell2 × Ell2, p ∈ V ↔ ‖p.1‖ < ‖base‖ + 1 ∧ ‖p.2‖ < ‖base‖ + 1 := by
    intro p; rw [hV]; rfl
  have hVB : ∀ p ∈ V, ‖p.1‖ < B ∧ ‖p.2‖ < B := by
    intro p hp
    obtain ⟨h1', h2'⟩ := (hVmem p).1 hp
    constructor <;> linarith [hB_def]
  have hVβu : ∀ p ∈ V, ‖p.1‖ < βu ∧ ‖p.2‖ < βu := by
    intro p hp
    obtain ⟨h1', h2'⟩ := hVB p hp
    constructor <;> linarith
  have hVo : IsOpen V := by
    rw [hV]
    exact (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
  have hbmem : (base, jEll base) ∈ V := by
    rw [hVmem]
    constructor
    · show ‖base‖ < ‖base‖ + 1
      linarith
    · show ‖jEll base‖ < ‖base‖ + 1
      rw [norm_jEll]
      linarith
  -- sector facts for `κ ∈ K`
  have hsec_of : ∀ κ ∈ K, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im →
      0 < z.im ∧ 8 + 1 / 4 ≤ L * z.im
        ∧ 16 * |κ / L| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2
        ∧ κ * (L * ((physK L a * B) * (physK L a * (2 * B / z.im)))) ≤ 1 / 8
        ∧ remR L a S M (κ / L) B δ ≤ ‖z‖ ∧ logR L a S M κ B δ ≤ ‖z‖ := by
    intro κ hκ z hRz hsec
    exact sector_facts L a S δ k B βu R κ M z hL ha hδ hkpos
      (Set.mem_Ioi.mp (hKpos hκ)) (hkK κ hκ) hB h1 h9 hJ' hX hrem hlog hRz hsec
  refine ⟨base, hbase, V, hVo, hbmem, R, hRpos, 4 * βu, by linarith, fun κ z p =>
    rfG hL ha S (κ / L) βu hβu z p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- fixed
    intro κ hκ z hRz hsec hz p hp
    obtain ⟨-, -, hκb, -, -, -⟩ := hsec_of κ hκ z hRz hsec
    obtain ⟨hp1, hp2⟩ := hVβu p hp
    exact (rfG_spec hL ha (S := S) hβu hz hκb hp1 hp2).1
  · -- small
    intro κ hκ z hRz hsec p hp
    obtain ⟨hz, -, hκb, -, -, -⟩ := hsec_of κ hκ z hRz hsec
    obtain ⟨hp1, hp2⟩ := hVB p hp
    obtain ⟨hv1, hv2⟩ := (hVmem p).1 hp
    have hr := (rfG_small_radius (S := S) hL ha hβu hz hκb hB hBβ hp1.le hp2.le).2
    have hle : 2 * B / z.im ≤ 4 * βu / z.im :=
      div_le_div_of_nonneg_right (by linarith) hz.le
    exact hr.trans hle
  · -- unique_small
    intro κ hκ z hRz hsec hz p hp q hq hfix
    obtain ⟨-, -, hκb, -, -, -⟩ := hsec_of κ hκ z hRz hsec
    obtain ⟨hp1, hp2⟩ := hVβu p hp
    exact (rfG_spec hL ha (S := S) hβu hz hκb hp1 hp2).2.2 q hq hfix
  · -- holomorphic
    intro κ hκ z hRz hsec
    obtain ⟨hz, -, hκb, -, -, -⟩ := hsec_of κ hκ z hRz hsec
    intro p hp
    obtain ⟨hp1, hp2⟩ := hVβu p hp
    exact rfG_analyticOnNhd hL ha haS' hβu hz hκb p ⟨hp1, hp2⟩
  · -- r_remainder_C1
    intro κ hκ z hRz hsec
    obtain ⟨hz, -, hκb, -, hremb, -⟩ := hsec_of κ hκ z hRz hsec
    have hA : AnalyticOnNhd ℂ (fun p : Ell2 × Ell2 =>
        rfG hL ha S (κ / L) βu hβu z p - rMsum (coeffs L a S κ hL ha (derivativeExtension L) p)
          (z⁻¹) M) V := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hVβu p hp
      have hr : AnalyticAt ℂ (fun q : Ell2 × Ell2 => rfG hL ha S (κ / L) βu hβu z q) p :=
        rfG_analyticOnNhd hL ha haS' hβu hz hκb p ⟨hp1, hp2⟩
      exact hr.sub (rMsum_coeffs_analyticAt L hL ha haS hM κ (derivativeExtension L)
        (fun y => derivativeExtension_spec L y) (z⁻¹) p)
    exact hA.contDiffOn_of_completeSpace
  · -- r_remainder
    intro κ hκ z hRz hsec p hp
    obtain ⟨hz, -, hκb, -, hremb, -⟩ := hsec_of κ hκ z hRz hsec
    have hw : 0 ≤ (‖z‖ ^ (M + 1))⁻¹ := inv_nonneg.mpr (pow_nonneg (norm_nonneg z) _)
    have hsup : ∀ q : Ell2 × Ell2, dist q p ≤ 1 →
        ‖rfG hL ha S (κ / L) βu hβu z q - rMsum (coeffs L a S κ hL ha (derivativeExtension L) q)
          (z⁻¹) M‖ ≤ remC L a S M (κ / L) B δ * (‖z‖ ^ (M + 1))⁻¹ := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := ball_norm_le (p := p) hq
      obtain ⟨hp1, hp2⟩ := hVB p hp
      obtain ⟨hv1, hv2⟩ := (hVmem p).1 hp
      exact QuantumNLS.RiccatiValueBounds.value_remainder hL ha haS hM κ hB hBβ hβu
        (derivativeExtension L) (fun y => derivativeExtension_spec L y) δ hδ hz hsec hremb hκb
        (p := q) (by linarith [hv1, hB_def]) (by linarith [hv2, hB_def])
    have hdiff : ∀ q : Ell2 × Ell2, dist q p ≤ 1 →
        DifferentiableAt ℂ (fun q : Ell2 × Ell2 => rfG hL ha S (κ / L) βu hβu z q
          - rMsum (coeffs L a S κ hL ha (derivativeExtension L) q) (z⁻¹) M) q := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := ball_norm_le (p := p) hq
      obtain ⟨hp1, hp2⟩ := hVB p hp
      obtain ⟨hv1, hv2⟩ := (hVmem p).1 hp
      have hr : AnalyticAt ℂ (fun q : Ell2 × Ell2 => rfG hL ha S (κ / L) βu hβu z q) q :=
        rfG_analyticOnNhd hL ha haS' hβu hz hκb q ⟨by linarith [hq1, hv1, hB_def],
          by linarith [hq2, hv2, hB_def]⟩
      exact (hr.sub (rMsum_coeffs_analyticAt L hL ha haS hM κ (derivativeExtension L)
        (fun y => derivativeExtension_spec L y) (z⁻¹) q)).differentiableAt
    constructor
    · exact (hsup p (by rw [dist_self]; norm_num)).trans
        (mul_le_mul_of_nonneg_right (hremC κ hκ) hw)
    · exact deriv_opnorm_le (c := remC L a S M (κ / L) B δ * (‖z‖ ^ (M + 1))⁻¹)
        (Kc := 4 * βu * (‖z‖ ^ (M + 1))⁻¹) (mul_nonneg (by linarith) hw) hdiff hsup
        (mul_le_mul_of_nonneg_right (hremC κ hκ) hw)
  · -- trace_near_one
    intro κ hκ z hRz hsec p hp
    obtain ⟨hz, hLIm, hκb, hJb, -, hlogb⟩ := hsec_of κ hκ z hRz hsec
    obtain ⟨hp1, hp2⟩ := hVB p hp
    obtain ⟨hv1, hv2⟩ := (hVmem p).1 hp
    exact QuantumNLS.RiccatiValueBounds.trace_near_one_bound hL ha haS hM κ
      (Set.mem_Ioi.mp (hKpos hκ)) hB hBβ hβu (derivativeExtension L)
      (fun y => derivativeExtension_spec L y) δ hδ hz hsec hlogb hκb hJb hLIm hp1.le hp2.le
  · -- log_remainder_C1
    intro κ hκ z hRz hsec
    obtain ⟨hz, hLIm, hκb, hJb, -, hlogb⟩ := hsec_of κ hκ z hRz hsec
    have hA : AnalyticOnNhd ℂ (fun p : Ell2 × Ell2 => logTrace L a S κ ha z p
        - Complex.I * (κ : ℂ) * ∑ n ∈ Finset.Icc 1 M,
          modeCoef L a (lowT L a S p.2) (coeffs L a S κ hL ha (derivativeExtension L) p n)
            * (z⁻¹) ^ n) V := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hVB p hp
      obtain ⟨hv1, hv2⟩ := (hVmem p).1 hp
      have hlogA := logTrace_analyticAt L hL ha haS hM (Set.mem_Ioi.mp (hKpos hκ)) hB hBβ hβu
        (derivativeExtension L) (fun y => derivativeExtension_spec L y) hδ hz hsec hlogb hκb
        hJb hLIm (p0 := p) hp1 hp2
      exact hlogA.sub ((analyticAt_const : AnalyticAt ℂ
        (fun _ : Ell2 × Ell2 => Complex.I * (κ : ℂ)) p).mul (modeSum_analyticAt L hL ha haS hM κ z p))
    exact hA.contDiffOn_of_completeSpace
  · -- log_remainder
    intro κ hκ z hRz hsec p hp
    obtain ⟨hz, hLIm, hκb, hJb, -, hlogb⟩ := hsec_of κ hκ z hRz hsec
    have hw : 0 ≤ (‖z‖ ^ (M + 1))⁻¹ := inv_nonneg.mpr (pow_nonneg (norm_nonneg z) _)
    have hsup : ∀ q : Ell2 × Ell2, dist q p ≤ 1 →
        ‖logTrace L a S κ ha z q - Complex.I * (κ : ℂ) * ∑ n ∈ Finset.Icc 1 M,
          modeCoef L a (lowT L a S q.2) (coeffs L a S κ hL ha (derivativeExtension L) q n)
            * (z⁻¹) ^ n‖ ≤ logC L a S M κ B δ * (‖z‖ ^ (M + 1))⁻¹ := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := ball_norm_le (p := p) hq
      obtain ⟨hp1, hp2⟩ := hVB p hp
      obtain ⟨hv1, hv2⟩ := (hVmem p).1 hp
      exact (QuantumNLS.RiccatiValueBounds.log_value hL ha haS hM κ
        (Set.mem_Ioi.mp (hKpos hκ)) hB hBβ hβu (derivativeExtension L)
        (fun y => derivativeExtension_spec L y) δ hδ hz hsec hlogb hκb hJb
        (p := q) (by linarith [hq1, hv1, hB_def]) (by linarith [hq2, hv2, hB_def])).2
    have hdiff : ∀ q : Ell2 × Ell2, dist q p ≤ 1 →
        DifferentiableAt ℂ (fun q : Ell2 × Ell2 => logTrace L a S κ ha z q
          - Complex.I * (κ : ℂ) * ∑ n ∈ Finset.Icc 1 M,
            modeCoef L a (lowT L a S q.2) (coeffs L a S κ hL ha (derivativeExtension L) q n)
              * (z⁻¹) ^ n) q := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := ball_norm_le (p := p) hq
      obtain ⟨hp1, hp2⟩ := hVB p hp
      obtain ⟨hv1, hv2⟩ := (hVmem p).1 hp
      have hlogA := logTrace_analyticAt L hL ha haS hM (Set.mem_Ioi.mp (hKpos hκ)) hB hBβ hβu
        (derivativeExtension L) (fun y => derivativeExtension_spec L y) hδ hz hsec hlogb hκb
        hJb hLIm (p0 := q) (by linarith [hq1, hv1, hB_def]) (by linarith [hq2, hv2, hB_def])
      exact (hlogA.sub ((analyticAt_const : AnalyticAt ℂ
        (fun _ : Ell2 × Ell2 => Complex.I * (κ : ℂ)) q).mul
          (modeSum_analyticAt L hL ha haS hM κ z q))).differentiableAt
    constructor
    · exact (hsup p (by rw [dist_self]; norm_num)).trans
        (mul_le_mul_of_nonneg_right (hlogC κ hκ) (inv_nonneg.mpr (pow_nonneg (norm_nonneg z) _)))
    · exact deriv_opnorm_le (c := logC L a S M κ B δ * (‖z‖ ^ (M + 1))⁻¹)
        (Kc := 4 * βu * (‖z‖ ^ (M + 1))⁻¹) (mul_nonneg (by linarith) hw) hdiff hsup
        (mul_le_mul_of_nonneg_right (hlogC κ hκ) hw)
  · -- real_C1
    intro κ hκ z hRz hsec
    obtain ⟨hz, hLIm, hκb, hJb, -, hlogb⟩ := hsec_of κ hκ z hRz hsec
    have hA : AnalyticOnNhd ℂ (fun p : Ell2 × Ell2 => logTrace L a S κ ha z p) V := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hVB p hp
      obtain ⟨hv1, hv2⟩ := (hVmem p).1 hp
      exact logTrace_analyticAt L hL ha haS hM (Set.mem_Ioi.mp (hKpos hκ)) hB hBβ hβu
        (derivativeExtension L) (fun y => derivativeExtension_spec L y) hδ hz hsec hlogb hκb
        hJb hLIm (p0 := p) hp1 hp2
    have hC : ContDiffOn ℂ 1 (fun p : Ell2 × Ell2 => logTrace L a S κ ha z p) V :=
      hA.contDiffOn_of_completeSpace
    have hR' : ContDiffOn ℝ 1 (fun p : Ell2 × Ell2 => logTrace L a S κ ha z p) V :=
      hC.restrict_scalars ℝ
    have hφ : ContDiff ℝ 1 (fun q : Ell2 => (q, jR q)) :=
      contDiff_id.prodMk jR.contDiff
    exact hR'.comp hφ.contDiffOn (fun q hq => hq)

end QuantumNLS.RiccatiMainFull
