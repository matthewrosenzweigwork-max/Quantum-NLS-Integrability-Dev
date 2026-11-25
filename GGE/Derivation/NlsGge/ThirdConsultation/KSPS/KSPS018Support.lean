import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS018Host
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.KSPS.KSPS006

/- KSPS-018 SUPPORT01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS018Support.lean.
   Part A: bridge from the KSPS Picard terms to the landed G1-004 terms `potentialVolterraTerm38`, hence analyticity
   of lam -> fundamental phi x lam on all of C (genuine differentiability BEFORE any derivative bound).
   Part B: Cauchy estimates for the first two derivatives of an entire matrix function. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38
open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS018Support

/-! ### Part A: analyticity in the spectral parameter -/

theorem E_eq_freeZs (lam : ℂ) (x : ℝ) :
    NlsGge.ThirdConsultation.KSPSVolterra.E lam x =
      NlsGge.SpectralFoundations.freeZsFundamentalComplex lam x := by
  rw [← NlsGge.GK38.freeE_eq]
  rfl

theorem R_mul_phi (p : PotPair) (s : ℝ) :
    NlsGge.ThirdConsultation.KSPSVolterra.R * NlsGge.ThirdConsultation.KSPSVolterra.phi p s =
      NlsGge.Atomic.Volterra.rawPotCoeff38 (potRepFst38 p) (potRepSnd38 p) s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NlsGge.ThirdConsultation.KSPSVolterra.R, NlsGge.ThirdConsultation.KSPSVolterra.phi,
      NlsGge.Atomic.Volterra.rawPotCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

theorem term_eq_volterra (p : PotPair) (z : ℂ) :
    ∀ (k : ℕ) (x : ℝ), NlsGge.ThirdConsultation.KSPSVolterra.term k x z p =
      NlsGge.Atomic.Volterra.potentialVolterraTerm38 p z k x := by
  intro k
  induction k with
  | zero =>
    intro x
    simp only [NlsGge.ThirdConsultation.KSPSVolterra.term, NlsGge.Atomic.Volterra.potentialVolterraTerm38,
      NlsGge.Atomic.Volterra.freeKernelVolterraTerm38]
    exact E_eq_freeZs z x
  | succ k ih =>
    intro x
    ext i j
    simp only [NlsGge.ThirdConsultation.KSPSVolterra.term, NlsGge.ThirdConsultation.KSPSVolterra.integrateMatrix,
      NlsGge.Atomic.Volterra.potentialVolterraTerm38, NlsGge.Atomic.Volterra.freeKernelVolterraTerm38]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have h1 := ih s
    simp only [NlsGge.Atomic.Volterra.potentialVolterraTerm38] at h1
    rw [h1, mul_assoc (NlsGge.ThirdConsultation.KSPSVolterra.E z (x - s)), R_mul_phi, E_eq_freeZs]

theorem fundamental_eq_tsum (φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1) {x : ℝ} (hx : 0 ≤ x) (lam : ℂ) :
    NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x lam =
      ∑' n : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38
        (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ) lam n x := by
  have hS := (NlsGge.Atomic.G1004GenT.summable_termsT
    (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ) lam hx).hasSum
  ext i j
  have hent : Continuous (Matrix.entryLinearMap ℂ ℂ i j : NlsGge.GK38.PairMat38 →ₗ[ℂ] ℂ) :=
    LinearMap.continuous_of_finiteDimensional _
  have h1 := hS.map (Matrix.entryLinearMap ℂ ℂ i j : NlsGge.GK38.PairMat38 →ₗ[ℂ] ℂ) hent
  have h2 : (∑' n : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38
        (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ) lam n x) i j =
      ∑' n : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38
        (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ) lam n x i j := h1.tsum_eq.symm
  rw [h2]
  show ∑' k : ℕ, NlsGge.ThirdConsultation.KSPSVolterra.term k x lam
    (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ) i j = _
  exact tsum_congr fun k => by rw [term_eq_volterra]

theorem analyticOnNhd_fundamental (φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1) {x : ℝ} (hx : 0 ≤ x) :
    AnalyticOnNhd ℂ (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l) Set.univ := by
  have hfun : (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l) =
      (fun p : ℂ × PotPair => ∑' n : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38 p.2 p.1 n x) ∘
        (fun l : ℂ => (l, NlsGge.ThirdConsultation.KSPSVolterra.toPair φ)) :=
    funext fun l => fundamental_eq_tsum φ hx l
  rw [hfun]
  intro l hl
  have hin : AnalyticAt ℂ (fun l : ℂ => (l, NlsGge.ThirdConsultation.KSPSVolterra.toPair φ)) l :=
    AnalyticAt.prod analyticAt_id analyticAt_const
  exact AnalyticAt.comp
    (g := fun p : ℂ × PotPair => ∑' n : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38 p.2 p.1 n x)
    (f := fun l : ℂ => (l, NlsGge.ThirdConsultation.KSPSVolterra.toPair φ))
    (NlsGge.Atomic.G1004GenT.analytic_all x hx (l, NlsGge.ThirdConsultation.KSPSVolterra.toPair φ)
      (Set.mem_univ _)) hin

theorem analyticOnNhd_freePropagator (x : ℝ) :
    AnalyticOnNhd ℂ (fun l : ℂ => NlsGge.ThirdConsultation.KSPS.freePropagator x l) Set.univ := by
  intro l hl
  refine NlsGge.Atomic.G1004GenT.analyticAt_of_entries fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [NlsGge.ThirdConsultation.KSPS.freePropagator] <;> fun_prop


/-! ### Part B: Cauchy estimates for the first two derivatives -/

theorem cauchy_deriv_le {f : ℂ → Matrix (Fin 2) (Fin 2) ℂ} (hf : Differentiable ℂ f) (c : ℂ) {r K : ℝ}
    (hr : 0 < r) (hK : ∀ z ∈ Metric.sphere c r, ‖f z‖ ≤ K) : ‖deriv f c‖ ≤ K / r :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hf.diffContOnCl hK

theorem norm_iteratedDeriv_le_two (g : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (hg : Differentiable ℂ g) (c : ℂ)
    {K : ℝ} (hK : ∀ z : ℂ, ‖z - c‖ ≤ 1 → ‖g z‖ ≤ K) (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedDeriv j g c‖ ≤ 2 ^ j * K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK c (by simp))
  have hgA : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hd1 : Differentiable ℂ (deriv g) := fun z => (hgA.deriv z (Set.mem_univ _)).differentiableAt
  have h1 : ∀ ν : ℂ, ‖ν - c‖ ≤ 1 / 2 → ‖deriv g ν‖ ≤ 2 * K := by
    intro ν hν
    have := cauchy_deriv_le hg ν (r := 1 / 2) (K := K) (by norm_num) (fun z hz => by
      refine hK z ?_
      have hz' : ‖z - ν‖ = 1 / 2 := by rw [← dist_eq_norm]; exact hz
      calc ‖z - c‖ = ‖(z - ν) + (ν - c)‖ := by congr 1; ring
        _ ≤ ‖z - ν‖ + ‖ν - c‖ := norm_add_le _ _
        _ ≤ 1 := by rw [hz']; linarith)
    calc ‖deriv g ν‖ ≤ K / (1 / 2) := this
      _ = 2 * K := by ring
  interval_cases j
  · simpa using (le_refl _ : ‖g c‖ ≤ ‖g c‖) |>.trans (hK c (by simp))
  · have := cauchy_deriv_le hg c (r := 1) (K := K) one_pos (fun z hz => hK z (by
      rw [← dist_eq_norm]; exact hz.le))
    rw [iteratedDeriv_one]
    calc ‖deriv g c‖ ≤ K / 1 := this
      _ ≤ 2 ^ 1 * K := by norm_num; linarith
  · have := cauchy_deriv_le hd1 c (r := 1 / 2) (K := 2 * K) (by norm_num) (fun z hz => h1 z (by
      rw [← dist_eq_norm]; exact hz.le))
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    calc ‖deriv (deriv g) c‖ ≤ 2 * K / (1 / 2) := this
      _ = 2 ^ 2 * K := by ring

/-! ### Part C: the case j = 0 on a complex disc (inputs of the Cauchy estimates) -/

open NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

theorem embed_norm_le (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    ‖physicalSobolevEmbed 1 u‖ ≤ ‖iotaCLM‖ * ‖u‖ := by
  set M : ℝ := ‖iotaCLM‖ * ‖u‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hae := sobolevPointValue_ae 1 u
  have h1 : ‖physicalSobolevEmbed 1 u‖ ^ 2 = ∫ t in (0 : ℝ)..1, ‖sobolevPointValue 1 u t‖ ^ 2 := by
    rw [← integral_sq_coverRep38_one]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with t ht _
    rw [ht]
  have h2 : ∫ t in (0 : ℝ)..1, ‖sobolevPointValue 1 u t‖ ^ 2 ≤ M ^ 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := M ^ 2)
      (f := fun t => ‖sobolevPointValue 1 u t‖ ^ 2) (fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (NlsGge.ThirdConsultation.KSPS003Support2.pv_sup u t) 2)
    have h3 := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    simpa using h3
  have h4 : ‖physicalSobolevEmbed 1 u‖ ^ 2 ≤ M ^ 2 := h1 ▸ h2
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg (physicalSobolevEmbed 1 u)]

theorem l2Norm_le (φ : SobolevC 1) : l2Norm φ ≤ ‖iotaCLM‖ * sobolevNorm 1 φ := by
  have hι := ContinuousLinearMap.opNorm_nonneg iotaCLM
  have h1 := embed_norm_le φ.1
  have h2 := embed_norm_le φ.2
  have e : ‖iotaCLM‖ * sobolevNorm 1 φ =
      Real.sqrt ((‖iotaCLM‖ * ‖φ.1‖) ^ 2 + (‖iotaCLM‖ * ‖φ.2‖) ^ 2) := by
    unfold sobolevNorm
    rw [show (‖iotaCLM‖ * ‖φ.1‖) ^ 2 + (‖iotaCLM‖ * ‖φ.2‖) ^ 2 =
        ‖iotaCLM‖ ^ 2 * (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hι]
  rw [e]
  exact Real.sqrt_le_sqrt (add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2)
    (pow_le_pow_left₀ (norm_nonneg _) h2 2))

theorem norm_fst_le (φ : SobolevC 1) : ‖φ.1‖ ≤ sobolevNorm 1 φ := by
  unfold sobolevNorm
  calc ‖φ.1‖ = Real.sqrt (‖φ.1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖φ.2‖])

theorem norm_snd_le (φ : SobolevC 1) : ‖φ.2‖ ≤ sobolevNorm 1 φ := by
  unfold sobolevNorm
  calc ‖φ.2‖ = Real.sqrt (‖φ.2‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖φ.1‖])

theorem sobolevNorm_nonneg (φ : SobolevC 1) : 0 ≤ sobolevNorm 1 φ := Real.sqrt_nonneg _

theorem osc_bound (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (ν : ℂ) :
    ‖ν‖ * ‖∫ t in (0 : ℝ)..x, Complex.exp (ν * (t : ℂ)) * coverRep38 (physicalSobolevEmbed 1 u) t‖ ≤
      Real.exp |ν.re| * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖) := by
  have hid := NlsGge.ThirdConsultation.KSPS002Support.ibp_scalar u hx ν
  rw [← norm_mul, hid]
  have hA : 1 ≤ Real.exp |ν.re| := Real.one_le_exp (abs_nonneg _)
  have hexp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Complex.exp (ν * (t : ℂ))‖ ≤ Real.exp |ν.re| := by
    intro t ht
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    have : (ν * (t : ℂ)).re = ν.re * t := by simp
    rw [this]
    calc ν.re * t ≤ |ν.re| * t := mul_le_mul_of_nonneg_right (le_abs_self _) ht.1
      _ ≤ |ν.re| := mul_le_of_le_one_right (abs_nonneg _) ht.2
  have hι := ContinuousLinearMap.opNorm_nonneg iotaCLM
  have hD := ContinuousLinearMap.opNorm_nonneg derivCLM
  have hu0 := norm_nonneg u
  have hpx := NlsGge.ThirdConsultation.KSPS003Support2.pv_sup u x
  have hp0 := NlsGge.ThirdConsultation.KSPS003Support2.pv_sup u 0
  have hk : IntervalIntegrable (coverRep38 (physicalSobolevDerivative38 1 u)) volume 0 x :=
    (intervalIntegrable_coverRep38_one (physicalSobolevDerivative38 1 u)).mono_set (by
      rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le (by norm_num)]
      exact Set.Icc_subset_Icc le_rfl hx.2)
  have hint : ‖∫ t in (0 : ℝ)..x, Complex.exp (ν * (t : ℂ)) *
      coverRep38 (physicalSobolevDerivative38 1 u) t‖ ≤ Real.exp |ν.re| * (‖derivCLM‖ * ‖u‖) := by
    refine (NlsGge.ThirdConsultation.KSPS003Support.norm_int_mul_le hx.1
      (fun t ht => hexp t ⟨ht.1, ht.2.trans hx.2⟩) hk).trans ?_
    exact mul_le_mul_of_nonneg_left
      ((NlsGge.ThirdConsultation.KSPS003Support.int_norm_mono
        (intervalIntegrable_coverRep38_one (physicalSobolevDerivative38 1 u)) hx).trans
        (NlsGge.ThirdConsultation.KSPS003Support2.deriv_L1 u)) (Real.exp_pos _).le
  have hexx := hexp x hx
  have t1 : ‖Complex.exp (ν * (x : ℂ)) * sobolevPointValue 1 u x‖ ≤
      Real.exp |ν.re| * (‖iotaCLM‖ * ‖u‖) := by
    rw [norm_mul]
    exact mul_le_mul hexx hpx (norm_nonneg _) (Real.exp_pos _).le
  have hs1 := norm_sub_le (Complex.exp (ν * (x : ℂ)) * sobolevPointValue 1 u x -
      sobolevPointValue 1 u 0) (∫ t in (0 : ℝ)..x, Complex.exp (ν * (t : ℂ)) *
        coverRep38 (physicalSobolevDerivative38 1 u) t)
  have hs2 := norm_sub_le (Complex.exp (ν * (x : ℂ)) * sobolevPointValue 1 u x)
      (sobolevPointValue 1 u 0)
  nlinarith [mul_nonneg hι hu0, mul_nonneg hD hu0, mul_nonneg (mul_nonneg hι hu0) (sub_nonneg.2 hA)]

theorem norm_exp_neg_le (lam : ℂ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖Complex.exp (-(Complex.I * lam * (x : ℂ)))‖ ≤ Real.exp |lam.im| := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (-(Complex.I * lam * (x : ℂ))).re = lam.im * x := by simp
  rw [this]
  calc lam.im * x ≤ |lam.im| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx.1
    _ ≤ |lam.im| := mul_le_of_le_one_right (abs_nonneg _) hx.2

theorem norm_exp_pos_le (lam : ℂ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖Complex.exp (Complex.I * lam * (x : ℂ))‖ ≤ Real.exp |lam.im| := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (Complex.I * lam * (x : ℂ)).re = -(lam.im * x) := by simp
  rw [this]
  calc -(lam.im * x) = (-lam.im) * x := by ring
    _ ≤ |lam.im| * x := mul_le_mul_of_nonneg_right (neg_le_abs _) hx.1
    _ ≤ |lam.im| := mul_le_of_le_one_right (abs_nonneg _) hx.2

theorem M1_entry_le (φ : SobolevC 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {lam : ℂ} (hlam : lam ≠ 0)
    (i j : Fin 2) :
    ‖volterraTerm 1 x lam φ i j‖ ≤
      Real.exp (3 * |lam.im|) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * sobolevNorm 1 φ) / (2 * ‖lam‖) := by
  have hι := ContinuousLinearMap.opNorm_nonneg iotaCLM
  have hD := ContinuousLinearMap.opNorm_nonneg derivCLM
  have hs0 := sobolevNorm_nonneg φ
  have hL : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hRHS : 0 ≤ Real.exp (3 * |lam.im|) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * sobolevNorm 1 φ) / (2 * ‖lam‖) := by
    positivity
  have hn2 : ‖(2 : ℂ) * Complex.I * lam‖ = 2 * ‖lam‖ := by simp
  have hexpe : Real.exp |lam.im| * Real.exp (2 * |lam.im|) = Real.exp (3 * |lam.im|) := by
    rw [← Real.exp_add]; congr 1; ring
  fin_cases i <;> fin_cases j
  · simpa [NlsGge.ThirdConsultation.KSPS002Support.term1_00] using hRHS
  · -- (0,1)
    show ‖volterraTerm 1 x lam φ 0 1‖ ≤ _
    rw [NlsGge.ThirdConsultation.KSPS002Support.term1_01]
    have hos := osc_bound φ.1 hx ((2 : ℂ) * Complex.I * lam)
    have hre : |((2 : ℂ) * Complex.I * lam).re| = 2 * |lam.im| := by simp [abs_mul]
    rw [hre, hn2] at hos
    have hint : ‖∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 φ.1) t‖ ≤
        Real.exp (2 * |lam.im|) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖φ.1‖) / (2 * ‖lam‖) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hK : 0 ≤ 2 * ‖iotaCLM‖ + ‖derivCLM‖ := by positivity
    calc ‖Complex.I * Complex.exp (-(Complex.I * lam * (x : ℂ))) *
          ∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.1) t‖
        = ‖Complex.exp (-(Complex.I * lam * (x : ℂ)))‖ *
          ‖∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.1) t‖ := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
      _ ≤ Real.exp |lam.im| * (Real.exp (2 * |lam.im|) *
            ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * sobolevNorm 1 φ) / (2 * ‖lam‖)) := by
          refine mul_le_mul (norm_exp_neg_le lam hx) (hint.trans ?_) (norm_nonneg _) (Real.exp_pos _).le
          gcongr
          exact norm_fst_le φ
      _ = _ := by rw [← hexpe]; ring
  · -- (1,0)
    show ‖volterraTerm 1 x lam φ 1 0‖ ≤ _
    rw [NlsGge.ThirdConsultation.KSPS002Support.term1_10]
    have hos := osc_bound φ.2 hx (-((2 : ℂ) * Complex.I * lam))
    have hre : |(-((2 : ℂ) * Complex.I * lam)).re| = 2 * |lam.im| := by simp [abs_mul]
    rw [hre, norm_neg, hn2] at hos
    have hint : ‖∫ t in (0 : ℝ)..x, Complex.exp ((-(2 * Complex.I * lam)) * (t : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 φ.2) t‖ ≤
        Real.exp (2 * |lam.im|) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖φ.2‖) / (2 * ‖lam‖) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hK : 0 ≤ 2 * ‖iotaCLM‖ + ‖derivCLM‖ := by positivity
    calc ‖-Complex.I * Complex.exp (Complex.I * lam * (x : ℂ)) *
          ∫ t in (0 : ℝ)..x, Complex.exp ((-(2 * Complex.I * lam)) * (t : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.2) t‖
        = ‖Complex.exp (Complex.I * lam * (x : ℂ))‖ *
          ‖∫ t in (0 : ℝ)..x, Complex.exp ((-(2 * Complex.I * lam)) * (t : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ.2) t‖ := by
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
      _ ≤ Real.exp |lam.im| * (Real.exp (2 * |lam.im|) *
            ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * sobolevNorm 1 φ) / (2 * ‖lam‖)) := by
          refine mul_le_mul (norm_exp_pos_le lam hx) (hint.trans ?_) (norm_nonneg _) (Real.exp_pos _).le
          gcongr
          exact norm_snd_le φ
      _ = _ := by rw [← hexpe]; ring
  · simpa [NlsGge.ThirdConsultation.KSPS002Support.term1_11] using hRHS

theorem norm_R_le : ‖NlsGge.ThirdConsultation.KSPSVolterra.R‖ ≤ 2 := by
  have := NlsGge.ThirdConsultation.KSPS005Support.opNorm_le_two
    NlsGge.ThirdConsultation.KSPSVolterra.R (B := 1) (fun i j => by
      fin_cases i <;> fin_cases j <;> simp [NlsGge.ThirdConsultation.KSPSVolterra.R])
  linarith

theorem norm_freePropagator_le (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (lam : ℂ) :
    ‖freePropagator x lam‖ ≤ 2 * Real.exp |lam.im| := by
  refine NlsGge.ThirdConsultation.KSPS005Support.opNorm_le_two _ (fun i j => ?_)
  have h := NlsGge.GK38.norm_freeE_entry_le lam x i j
  have hx' : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
  refine h.trans (Real.exp_le_exp.2 ?_)
  exact mul_le_of_le_one_right (abs_nonneg _) hx'

theorem erq_le (φ : SobolevC 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {lam : ℂ} (hlam : lam ≠ 0) :
    ‖(2 * lam)⁻¹ • (freePropagator x lam * NlsGge.ThirdConsultation.KSPSVolterra.R *
        NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ x)‖ ≤
      (2 * Real.exp |lam.im| * 2 * (‖iotaCLM‖ * sobolevNorm 1 φ) ^ 2) / (2 * ‖lam‖) := by
  have hι := ContinuousLinearMap.opNorm_nonneg iotaCLM
  have hs0 := sobolevNorm_nonneg φ
  have hL : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  rw [NlsGge.ThirdConsultation.KSPS003Support2.integratedQuadratic_eq, Matrix.mul_smul, Matrix.mul_one,
    norm_smul, norm_smul]
  set c : ℂ := ∫ t in (0 : ℝ)..x, coverRep38 (physicalSobolevEmbed 1 φ.1) t *
        coverRep38 (physicalSobolevEmbed 1 φ.2) t with hc
  have hu := sobolevPointValue_ae 1 φ.1
  have hv := sobolevPointValue_ae 1 φ.2
  have hc' : c = ∫ t in (0 : ℝ)..x, sobolevPointValue 1 φ.1 t * sobolevPointValue 1 φ.2 t := by
    rw [hc]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hu, hv] with t ht1 ht2 _
    rw [ht1, ht2]
  have hcn : ‖c‖ ≤ (‖iotaCLM‖ * sobolevNorm 1 φ) ^ 2 := by
    rw [hc']
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x)
      (C := (‖iotaCLM‖ * sobolevNorm 1 φ) ^ 2)
      (f := fun t => sobolevPointValue 1 φ.1 t * sobolevPointValue 1 φ.2 t) (fun t _ => by
        rw [norm_mul, sq]
        exact mul_le_mul
          ((NlsGge.ThirdConsultation.KSPS003Support2.pv_sup φ.1 t).trans
            (mul_le_mul_of_nonneg_left (norm_fst_le φ) hι))
          ((NlsGge.ThirdConsultation.KSPS003Support2.pv_sup φ.2 t).trans
            (mul_le_mul_of_nonneg_left (norm_snd_le φ) hι)) (norm_nonneg _) (by positivity))
    refine h.trans ?_
    have : |x - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hx.1]; exact hx.2
    exact mul_le_of_le_one_right (by positivity) this
  have hER : ‖freePropagator x lam * NlsGge.ThirdConsultation.KSPSVolterra.R‖ ≤
      2 * Real.exp |lam.im| * 2 :=
    (norm_mul_le _ _).trans (mul_le_mul (norm_freePropagator_le x hx lam) norm_R_le (norm_nonneg _)
      (by positivity))
  have hinv : ‖(2 * lam)⁻¹‖ = (2 * ‖lam‖)⁻¹ := by simp
  rw [hinv, div_eq_inv_mul]
  have hpos : 0 ≤ (2 * ‖lam‖)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul hcn hER (norm_nonneg _) (by positivity)) hpos
    |>.trans_eq (by ring)

theorem j0_bound (B Λim : ℝ) (hB : 0 ≤ B) (hΛ : 0 ≤ Λim) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B → ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      ∀ mu : ℂ, 1 ≤ ‖mu‖ → |mu.im| ≤ Λim →
        ‖NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x mu - freePropagator x mu‖ ≤ C0 / ‖mu‖ := by
  obtain ⟨C5, hC5, h5⟩ := fundamental_two_term_remainder_uniform
  have hι := ContinuousLinearMap.opNorm_nonneg iotaCLM
  have hD := ContinuousLinearMap.opNorm_nonneg derivCLM
  set K : ℝ := 2 * ‖iotaCLM‖ + ‖derivCLM‖ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C5 * Real.exp (Λim + ‖iotaCLM‖ * B) * B ^ 2 * (1 + B) +
      Real.exp (3 * Λim) * (K * B) + 2 * Real.exp Λim * (‖iotaCLM‖ * B) ^ 2, by positivity, ?_⟩
  intro φ hφ x hx mu hmu him
  have hs0 := sobolevNorm_nonneg φ
  set s : ℝ := sobolevNorm 1 φ with hs
  have hL : 0 < ‖mu‖ := lt_of_lt_of_le one_pos hmu
  have hmu0 : mu ≠ 0 := norm_pos_iff.mp hL
  have hdec : NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x mu - freePropagator x mu =
      fundamentalRemainder φ x mu + volterraTerm 1 x mu φ +
        (2 * mu)⁻¹ • (freePropagator x mu * NlsGge.ThirdConsultation.KSPSVolterra.R *
          NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ x) := by
    unfold fundamentalRemainder
    abel
  rw [hdec]
  -- the three pieces
  have him' : |mu.im| * x ≤ Λim :=
    (mul_le_of_le_one_right (abs_nonneg _) hx.2).trans him
  have hl2 : l2Norm φ ≤ ‖iotaCLM‖ * B :=
    (l2Norm_le φ).trans (mul_le_mul_of_nonneg_left hφ hι)
  have hT1 : ‖fundamentalRemainder φ x mu‖ ≤
      (C5 * Real.exp (Λim + ‖iotaCLM‖ * B) * B ^ 2 * (1 + B)) / ‖mu‖ := by
    have h := h5 φ x hx mu hmu0
    refine h.trans ?_
    have hexp : Real.exp (|mu.im| * x + l2Norm φ) ≤ Real.exp (Λim + ‖iotaCLM‖ * B) :=
      Real.exp_le_exp.2 (add_le_add him' hl2)
    have e1 : C5 * Real.exp (|mu.im| * x + l2Norm φ) * s ^ 2 * (1 + s) / ‖mu‖ ^ 2 ≤
        C5 * Real.exp (Λim + ‖iotaCLM‖ * B) * B ^ 2 * (1 + B) / ‖mu‖ ^ 2 := by
      gcongr
    refine e1.trans ?_
    refine div_le_div_of_nonneg_left (by positivity) hL ?_
    nlinarith
  have hT2 : ‖volterraTerm 1 x mu φ‖ ≤ Real.exp (3 * Λim) * (K * B) / ‖mu‖ := by
    have h := NlsGge.ThirdConsultation.KSPS005Support.opNorm_le_two (volterraTerm 1 x mu φ)
      (B := Real.exp (3 * |mu.im|) * (K * s) / (2 * ‖mu‖)) (fun i j => M1_entry_le φ hx hmu0 i j)
    refine h.trans ?_
    have e1 : Real.exp (3 * |mu.im|) ≤ Real.exp (3 * Λim) := Real.exp_le_exp.2 (by linarith)
    have e2 : 2 * (Real.exp (3 * |mu.im|) * (K * s) / (2 * ‖mu‖)) =
        Real.exp (3 * |mu.im|) * (K * s) / ‖mu‖ := by field_simp
    rw [e2]
    gcongr
  have hT3 : ‖(2 * mu)⁻¹ • (freePropagator x mu * NlsGge.ThirdConsultation.KSPSVolterra.R *
        NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ x)‖ ≤
      2 * Real.exp Λim * (‖iotaCLM‖ * B) ^ 2 / ‖mu‖ := by
    refine (erq_le φ hx hmu0).trans ?_
    have e1 : Real.exp |mu.im| ≤ Real.exp Λim := Real.exp_le_exp.2 him
    have e2 : 2 * Real.exp |mu.im| * 2 * (‖iotaCLM‖ * s) ^ 2 / (2 * ‖mu‖) =
        2 * Real.exp |mu.im| * (‖iotaCLM‖ * s) ^ 2 / ‖mu‖ := by field_simp
    rw [e2]
    gcongr
  have hsum : ‖fundamentalRemainder φ x mu + volterraTerm 1 x mu φ +
      (2 * mu)⁻¹ • (freePropagator x mu * NlsGge.ThirdConsultation.KSPSVolterra.R *
        NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ x)‖ ≤
      (C5 * Real.exp (Λim + ‖iotaCLM‖ * B) * B ^ 2 * (1 + B)) / ‖mu‖ +
        Real.exp (3 * Λim) * (K * B) / ‖mu‖ + 2 * Real.exp Λim * (‖iotaCLM‖ * B) ^ 2 / ‖mu‖ :=
    by
    have a1 := norm_add_le (fundamentalRemainder φ x mu + volterraTerm 1 x mu φ)
      ((2 * mu)⁻¹ • (freePropagator x mu * NlsGge.ThirdConsultation.KSPSVolterra.R *
        NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ x))
    have a2 := norm_add_le (fundamentalRemainder φ x mu) (volterraTerm 1 x mu φ)
    linarith
  refine hsum.trans (le_of_eq ?_)
  ring

/-! ### Part D: the Cauchy step for `M - E` and the pointwise statement -/

theorem differentiable_error (φ : SobolevC 1) {x : ℝ} (hx : 0 ≤ x) :
    Differentiable ℂ (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l -
      freePropagator x l) := by
  have h1 := analyticOnNhd_fundamental φ hx
  have h2 := analyticOnNhd_freePropagator x
  intro l
  exact ((h1 l (Set.mem_univ _)).differentiableAt).sub ((h2 l (Set.mem_univ _)).differentiableAt)

theorem iteratedDeriv_sub_eq (φ : SobolevC 1) {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (lam : ℂ) :
    iteratedDeriv n (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l) lam -
      iteratedDeriv n (fun l : ℂ => freePropagator x l) lam =
    iteratedDeriv n (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l -
      freePropagator x l) lam := by
  have h1 : ContDiffAt ℂ n (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l) lam :=
    ((analyticOnNhd_fundamental φ hx) lam (Set.mem_univ _)).contDiffAt
  have h2 : ContDiffAt ℂ n (fun l : ℂ => freePropagator x l) lam :=
    ((analyticOnNhd_freePropagator x) lam (Set.mem_univ _)).contDiffAt
  exact (iteratedDeriv_sub h1 h2).symm

/-- The pointwise (in `x`) form of KSPS-018, with genuine differentiability (analyticity in `lam` on all
of `C`, for `M` and `E`) and the printed quantifier order. -/
theorem spectral_derivative_rough_pointwise (j : Fin 3) (B Λim : ℝ) (hB : 0 ≤ B) (hΛ : 0 ≤ Λim) :
    ∃ C Lam : ℝ, 0 ≤ C ∧ 0 < Lam ∧ ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
      ∀ lam : ℂ, Lam ≤ ‖lam‖ → |lam.im| ≤ Λim → ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        ‖iteratedDeriv (j : ℕ) (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l) lam -
          iteratedDeriv (j : ℕ) (fun l : ℂ => freePropagator x l) lam‖ ≤ C / ‖lam‖ := by
  obtain ⟨C0, hC0, h0⟩ := j0_bound B (Λim + 1) hB (by linarith)
  refine ⟨8 * C0, 2, by positivity, by norm_num, ?_⟩
  intro φ hφ lam hlam him x hx
  have hL : 0 < ‖lam‖ := by linarith
  rw [iteratedDeriv_sub_eq φ hx.1]
  have hball : ∀ z : ℂ, ‖z - lam‖ ≤ 1 →
      ‖NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x z - freePropagator x z‖ ≤
        2 * C0 / ‖lam‖ := by
    intro z hz
    have hzn : ‖lam‖ - 1 ≤ ‖z‖ := by
      have := norm_sub_norm_le lam z
      rw [norm_sub_rev] at this
      linarith
    have hz1 : ‖lam‖ / 2 ≤ ‖z‖ := by linarith
    have hz2 : 1 ≤ ‖z‖ := by linarith
    have hzim : |z.im| ≤ Λim + 1 := by
      have : |z.im - lam.im| ≤ 1 := by
        calc |z.im - lam.im| = |(z - lam).im| := by simp
          _ ≤ ‖z - lam‖ := Complex.abs_im_le_norm _
          _ ≤ 1 := hz
      have h3 := abs_sub_abs_le_abs_sub z.im lam.im
      linarith
    refine (h0 φ hφ x hx z hz2 hzim).trans ?_
    rw [div_le_div_iff₀ (by linarith) hL]
    nlinarith
  have hK := norm_iteratedDeriv_le_two _ (differentiable_error φ hx.1) lam hball (j : ℕ)
    (by have := j.2; omega)
  refine hK.trans ?_
  have h2j : (2 : ℝ) ^ (j : ℕ) ≤ 4 := by
    have : (j : ℕ) ≤ 2 := by have := j.2; omega
    calc (2 : ℝ) ^ (j : ℕ) ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) this
      _ = 4 := by norm_num
  have hnn : 0 ≤ 2 * C0 / ‖lam‖ := by positivity
  calc (2 : ℝ) ^ (j : ℕ) * (2 * C0 / ‖lam‖) ≤ 4 * (2 * C0 / ‖lam‖) :=
        mul_le_mul_of_nonneg_right h2j hnn
    _ = 8 * C0 / ‖lam‖ := by ring

end NlsGge.ThirdConsultation.KSPS018Support
