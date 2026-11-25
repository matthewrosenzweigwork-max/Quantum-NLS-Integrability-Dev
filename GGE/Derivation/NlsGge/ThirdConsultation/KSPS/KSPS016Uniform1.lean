import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS016Support
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU3
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU4

/- KSPS016U1 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS016Uniform1.lean. Pro round-15 SUPPORT (never a packet).
   Ball-uniform TAIL form of KSPS-016 (h757's U2, tail-restricted as h760 found necessary):
   * endpointCoefficientBound_mono / Sb_le / threshold_mono: the KSPS-014 numerical constants are monotone in the
     radius (csSup_le_csSup with KSPS014Support1.endpoint_coefficient_set_bounded);
   * anti_rhs_le / dir_rhs_le / sum_sq_le_seven: pure real algebra for the landed per-index bounds;
   * boundary_tail_of: ∃ N0 C before φ, ξ, F with Σ_F (w^{N+1}|antitraceError|)² ≤ C and the same for dirichletError,
     for sobolevNorm N φ ≤ B₀, |n| ≥ N0. Route: the landed per-index KSPS016W.tail_bounds (pointwise, explicit), with the
     e-sequences w·(endpoint − leading) exactly as in the KSPS-011/012 head proofs, KSPS-013/014 heads, Sb ≤ S(B₀),
     ‖I_{N+1}‖ ≤ CI (KSPSU3), Fourier: |hat D^N φ_i| ≤ (2π)^N w^N |hat φ_i| and KSPSU4.weighted_fourier_le.
     The four tail finite-sum families (KSPS-011 master b = false/true, KSPS-012 diagonal lower/upper) enter as explicit
     hypotheses of exactly the landed KSPSWKB.endpoint_remainder_tail_U body (instantiated at φ' = KSPSU1.toOne) and of
     the KSPS012Q4 diag tail bodies; they are discharged in the glue module KSPSAntitraceUniform (lane memory split). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS016U
open NlsGge.ThirdConsultation.KSPSWKB

/-! ### Monotonicity of the KSPS-014 numerical constants in the radius -/

theorem endpointCoefficientBound_mono (N k : ℕ) (hk : 1 ≤ k ∧ k ≤ N) {B B' : ℝ} (h : B ≤ B') :
    NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k ≤
      NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B' k := by
  unfold NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound
  refine csSup_le_csSup (endpoint_coefficient_set_bounded N k hk B')
    ⟨0, Set.mem_union_left _ (Set.mem_singleton _)⟩ ?_
  rintro r (hr | ⟨φ, b, hφ, rfl⟩)
  · exact Set.mem_union_left _ hr
  · exact Set.mem_union_right _ ⟨φ, b, hφ.trans (max_le_max h le_rfl), rfl⟩

theorem Sb_le {N : ℕ} (φ : SobolevC N) {B₀ : ℝ} (hφ : sobolevNorm N φ ≤ B₀) :
    NlsGge.ThirdConsultation.KSPS016W.Sb φ ≤
      ∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k := by
  unfold NlsGge.ThirdConsultation.KSPS016W.Sb
  exact Finset.sum_le_sum (fun k hk => endpointCoefficientBound_mono N k (Finset.mem_Icc.mp hk) hφ)

theorem threshold_mono (N : ℕ) {B B' : ℝ} (h : B ≤ B') :
    NlsGge.ThirdConsultation.KSPSVolterra.threshold N B ≤
      NlsGge.ThirdConsultation.KSPSVolterra.threshold N B' := by
  unfold NlsGge.ThirdConsultation.KSPSVolterra.threshold
  have := Finset.sum_le_sum (fun k (hk : k ∈ Finset.Icc 1 N) =>
    endpointCoefficientBound_mono N k (Finset.mem_Icc.mp hk) h)
  linarith

/-! ### Pure algebra -/

theorem anti_rhs_le (A0 S0 CI Sb I f1 f2 v e1 e2 eL eU K : ℝ) (hSb0 : 0 ≤ Sb) (hSb : Sb ≤ S0)
    (hI0 : 0 ≤ I) (hI : I ≤ CI) (hA0 : 0 ≤ A0)
    (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) (hv : 0 ≤ v) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (heL : 0 ≤ eL) (heU : 0 ≤ eU)
    (hK : K = A0 + 2 * S0 ^ 2 + 2 + 2 * S0 + 4 * CI * S0 + 4 * CI * S0 ^ 2) :
    (A0 + 2 * Sb ^ 2) * (f1 + f2) + 2 * (eU + eL + Sb * ((I * v + e1) + (I * v + e2))) ≤
      K * (f1 + f2 + v + e1 + e2 + eL + eU) := by
  have hS00 : 0 ≤ S0 := hSb0.trans hSb
  have hCI0 : 0 ≤ CI := hI0.trans hI
  have hSb2 : Sb ^ 2 ≤ S0 ^ 2 := pow_le_pow_left₀ hSb0 hSb 2
  have hSI : Sb * I ≤ S0 * CI := mul_le_mul hSb hI hI0 hS00
  have c1 : A0 + 2 * Sb ^ 2 ≤ K := by nlinarith
  have c2 : (2 : ℝ) ≤ K := by nlinarith
  have c3 : 2 * Sb ≤ K := by nlinarith
  have c4 : 4 * (Sb * I) ≤ K := by nlinarith
  have p1 := mul_le_mul_of_nonneg_right c1 hf1
  have p2 := mul_le_mul_of_nonneg_right c1 hf2
  have p3 := mul_le_mul_of_nonneg_right c2 heU
  have p4 := mul_le_mul_of_nonneg_right c2 heL
  have p5 := mul_le_mul_of_nonneg_right c3 he1
  have p6 := mul_le_mul_of_nonneg_right c3 he2
  have p7 := mul_le_mul_of_nonneg_right c4 hv
  nlinarith [p1, p2, p3, p4, p5, p6, p7]

theorem dir_rhs_le (A0 S0 CI Sb I f1 f2 v e1 e2 eL eU K : ℝ) (hSb0 : 0 ≤ Sb) (hSb : Sb ≤ S0)
    (hI0 : 0 ≤ I) (hI : I ≤ CI) (hA0 : 0 ≤ A0)
    (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) (hv : 0 ≤ v) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (heL : 0 ≤ eL) (heU : 0 ≤ eU)
    (hK : K = A0 + 2 * S0 ^ 2 + 2 + 2 * S0 + 4 * CI * S0 + 4 * CI * S0 ^ 2) :
    (A0 + 2 * Sb ^ 2) * (f1 + f2) + 2 * I * (2 * Sb ^ 2) * v +
      2 * (e2 + e1 + eL + eU + Sb * ((I * v + e1) + (f2 + eL) + (f1 + eU) + (I * v + e2))) ≤
      K * (f1 + f2 + v + e1 + e2 + eL + eU) := by
  have hS00 : 0 ≤ S0 := hSb0.trans hSb
  have hCI0 : 0 ≤ CI := hI0.trans hI
  have hSb2 : Sb ^ 2 ≤ S0 ^ 2 := pow_le_pow_left₀ hSb0 hSb 2
  have hSI : Sb * I ≤ S0 * CI := mul_le_mul hSb hI hI0 hS00
  have hSSI : I * Sb ^ 2 ≤ CI * S0 ^ 2 := mul_le_mul hI hSb2 (sq_nonneg _) hCI0
  have c1 : A0 + 2 * Sb ^ 2 + 2 * Sb ≤ K := by nlinarith
  have c2 : 2 + 2 * Sb ≤ K := by nlinarith
  have c4 : 4 * (I * Sb ^ 2) + 4 * (Sb * I) ≤ K := by nlinarith
  have p1 := mul_le_mul_of_nonneg_right c1 hf1
  have p2 := mul_le_mul_of_nonneg_right c1 hf2
  have p3 := mul_le_mul_of_nonneg_right c2 heU
  have p4 := mul_le_mul_of_nonneg_right c2 heL
  have p5 := mul_le_mul_of_nonneg_right c2 he1
  have p6 := mul_le_mul_of_nonneg_right c2 he2
  have p7 := mul_le_mul_of_nonneg_right c4 hv
  nlinarith [p1, p2, p3, p4, p5, p6, p7]

theorem sq_add7_le (a b c d e f g : ℝ) :
    (a + b + c + d + e + f + g) ^ 2 ≤ 7 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e), sq_nonneg (a - f),
    sq_nonneg (a - g), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (b - f),
    sq_nonneg (b - g), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (c - f), sq_nonneg (c - g),
    sq_nonneg (d - e), sq_nonneg (d - f), sq_nonneg (d - g), sq_nonneg (e - f), sq_nonneg (e - g),
    sq_nonneg (f - g)]

theorem sum_sq_le_seven {ι : Type*} (F : Finset ι) (x t1 t2 t3 t4 t5 t6 t7 : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ n ∈ F, 0 ≤ x n ∧ x n ≤ K * (t1 n + t2 n + t3 n + t4 n + t5 n + t6 n + t7 n))
    (T1 T2 T3 T4 T5 T6 T7 : ℝ)
    (h1 : ∑ n ∈ F, t1 n ^ 2 ≤ T1) (h2 : ∑ n ∈ F, t2 n ^ 2 ≤ T2) (h3 : ∑ n ∈ F, t3 n ^ 2 ≤ T3)
    (h4 : ∑ n ∈ F, t4 n ^ 2 ≤ T4) (h5 : ∑ n ∈ F, t5 n ^ 2 ≤ T5) (h6 : ∑ n ∈ F, t6 n ^ 2 ≤ T6)
    (h7 : ∑ n ∈ F, t7 n ^ 2 ≤ T7) :
    ∑ n ∈ F, x n ^ 2 ≤ K ^ 2 * (7 * (T1 + T2 + T3 + T4 + T5 + T6 + T7)) := by
  have hp : ∀ n ∈ F, x n ^ 2 ≤
      K ^ 2 * (7 * (t1 n ^ 2 + t2 n ^ 2 + t3 n ^ 2 + t4 n ^ 2 + t5 n ^ 2 + t6 n ^ 2 + t7 n ^ 2)) := by
    intro n hn
    obtain ⟨h0, hle⟩ := h n hn
    calc x n ^ 2 ≤ (K * (t1 n + t2 n + t3 n + t4 n + t5 n + t6 n + t7 n)) ^ 2 := pow_le_pow_left₀ h0 hle 2
      _ = K ^ 2 * (t1 n + t2 n + t3 n + t4 n + t5 n + t6 n + t7 n) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sq_add7_le _ _ _ _ _ _ _) (sq_nonneg K)
  refine (Finset.sum_le_sum hp).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
  linarith

/-! ### Fourier comparison -/

theorem abs_le_w (n : ℤ) : |(n : ℝ)| ≤ indexWeight n := by
  unfold indexWeight
  exact Real.abs_le_sqrt (by linarith)

theorem deriv_fourier_le {N : ℕ} (φ : SobolevC N) (n : ℤ) (hν1 : 1 ≤ |(n : ℝ)|) :
    ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ≤
        (2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ∧
    ‖physicalFourier (iteratedDerivative N φ.2) n‖ ≤
        (2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) := by
  obtain ⟨hDF1, hDF2, -, -⟩ := NlsGge.ThirdConsultation.KSPS016W.fourier_facts φ n hν1
  have hpn : ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N‖ = (2 * Real.pi * |(n : ℝ)|) ^ N := by
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast, mul_one]
  have hle : (2 * Real.pi * |(n : ℝ)|) ^ N ≤ (2 * Real.pi) ^ N * indexWeight n ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left (abs_le_w n) (by positivity)) N
  have hsNn : ‖(-1 : ℂ) ^ N‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
  constructor
  · rw [hDF1, norm_mul, norm_mul, hpn, hsNn, one_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  · rw [hDF2, norm_mul, hpn, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

theorem fourier_sums_le {N : ℕ} (φ : SobolevC N) {B₀ : ℝ} (hφ : sobolevNorm N φ ≤ B₀) (F : Finset ℤ) :
    ∑ n ∈ F, ((2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖)) ^ 2 ≤
        ((2 * Real.pi) ^ N) ^ 2 * B₀ ^ 2 ∧
    ∑ n ∈ F, ((2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖)) ^ 2 ≤
        ((2 * Real.pi) ^ N) ^ 2 * B₀ ^ 2 := by
  have hW := NlsGge.ThirdConsultation.KSPSU4.weighted_fourier_le N φ F
  have hs0 : 0 ≤ sobolevNorm N φ := by unfold sobolevNorm; exact Real.sqrt_nonneg _
  have hB2 : sobolevNorm N φ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hs0 hφ 2
  have h1 : 0 ≤ ∑ n ∈ F, (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ n ∈ F, (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have e1 : ∑ n ∈ F, ((2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖)) ^ 2 =
      ((2 * Real.pi) ^ N) ^ 2 * ∑ n ∈ F, (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  have e2 : ∑ n ∈ F, ((2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖)) ^ 2 =
      ((2 * Real.pi) ^ N) ^ 2 * ∑ n ∈ F, (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [e1, e2]
  have hP : 0 ≤ ((2 * Real.pi) ^ N) ^ 2 := sq_nonneg _
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith) hP
  · exact mul_le_mul_of_nonneg_left (by linarith) hP

/-! ### The uniform tail estimate -/

theorem boundary_tail_of (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (a : ℝ) (ha : 0 ≤ a)
    (NL : ℕ) (CL : ℝ) (hCL : 0 ≤ CL)
    (hL : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (NL : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ false ⟨xi n, hz⟩ 1 (if false then 0 else 1)) -
          (if false then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if false then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if false then φ.1 else φ.2))
              ((if false then (-1 : ℤ) else 1) * n))‖ ^ 2 ≤ CL)
    (NU : ℕ) (CU : ℝ) (hCU : 0 ≤ CU)
    (hU : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (NU : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ true ⟨xi n, hz⟩ 1 (if true then 0 else 1)) -
          (if true then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if true then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if true then φ.1 else φ.2))
              ((if true then (-1 : ℤ) else 1) * n))‖ ^ 2 ≤ CU)
    (N1 : ℕ) (C1 : ℝ) (hC1 : 0 ≤ C1)
    (h1 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N1 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalLower N φ xi n -
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1))‖ ^ 2 ≤ C1)
    (N2 : ℕ) (C2 : ℝ) (hC2 : 0 ≤ C2)
    (h2 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N2 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalUpper N φ xi n -
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))‖ ^ 2 ≤ C2) :
    ∃ (N0 : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N0 : ℤ) ≤ |n|) →
        (∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖KSPSWKB.antitraceError N φ xi n‖) ^ 2 ≤ C) ∧
        (∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ xi n‖) ^ 2 ≤ C) := by
  obtain ⟨CI, hCI0, hIb⟩ := NlsGge.ThirdConsultation.KSPSU3.integralRiccatiLeft_uniform N hN B₀ hB₀
  obtain ⟨S0, hS0⟩ : ∃ S0 : ℝ, S0 = ∑ k ∈ Finset.Icc 1 N,
      NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B₀ k := ⟨_, rfl⟩
  have hS00 : 0 ≤ S0 := by
    rw [hS0]
    exact Finset.sum_nonneg (fun k hk => endpointCoefficientBound_nonneg N B₀ k hk)
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = 2 * ((N : ℝ) * 2 ^ N * (2 * a)) := ⟨_, rfl⟩
  have hA00 : 0 ≤ A0 := by rw [hA0]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = A0 + 2 * S0 ^ 2 + 2 + 2 * S0 + 4 * CI * S0 + 4 * CI * S0 ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨Sv, hSv⟩ : ∃ Sv : ℝ, Sv = ∑' n : ℤ, (1 / indexWeight n) ^ 2 := ⟨_, rfl⟩
  have hSv0 : 0 ≤ Sv := by rw [hSv]; exact tsum_nonneg (fun n => sq_nonneg _)
  obtain ⟨P2, hP2⟩ : ∃ P2 : ℝ, P2 = ((2 * Real.pi) ^ N) ^ 2 * B₀ ^ 2 := ⟨_, rfl⟩
  have hP20 : 0 ≤ P2 := by rw [hP2]; positivity
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, N0 = max (max (max NL NU) (max N1 N2))
      (⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀⌉₊ + 1) := ⟨_, rfl⟩
  have hNL : NL ≤ N0 := by rw [hN0]; exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hNU : NU ≤ N0 := by rw [hN0]; exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hN1 : N1 ≤ N0 := by rw [hN0]; exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hN2 : N2 ≤ N0 := by rw [hN0]; exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hNT : ⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀⌉₊ + 1 ≤ N0 := by
    rw [hN0]; exact le_max_right _ _
  refine ⟨N0, K ^ 2 * (7 * (P2 + P2 + Sv + C1 + C2 + CL + CU)), by positivity,
    fun φ hφ xi hxi F hF => ?_⟩
  have hFL : ∀ n ∈ F, (NL : ℤ) ≤ |n| := fun n hn => le_trans (Nat.cast_le.mpr hNL) (hF n hn)
  have hFU : ∀ n ∈ F, (NU : ℤ) ≤ |n| := fun n hn => le_trans (Nat.cast_le.mpr hNU) (hF n hn)
  have hF1 : ∀ n ∈ F, (N1 : ℤ) ≤ |n| := fun n hn => le_trans (Nat.cast_le.mpr hN1) (hF n hn)
  have hF2 : ∀ n ∈ F, (N2 : ℤ) ≤ |n| := fun n hn => le_trans (Nat.cast_le.mpr hN2) (hF n hn)
  have hFT : ∀ n ∈ F, ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ)
      ≤ |n| := by
    intro n hn
    have hc : ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ ≤
        ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀⌉₊ := Nat.ceil_mono (threshold_mono N hφ)
    have h' : ⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 ≤ N0 := by
      omega
    exact le_trans (Nat.cast_le.mpr h') (hF n hn)
  -- the four remainder sequences, as in the KSPS-011 / KSPS-012 head proofs
  have hw : ∀ n : ℤ, (indexWeight n : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (lt_of_lt_of_le one_pos (NlsGge.ThirdConsultation.KSPS015W.one_le_w n)).ne'
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  obtain ⟨eL, hLs, hLe⟩ : ∃ e : ℤ → ℂ,
      (∀ F : Finset ℤ, (∀ n ∈ F, (NL : ℤ) ≤ |n|) → ∑ n ∈ F, ‖e n‖ ^ 2 ≤ CL) ∧
      ∀ n : ℤ, e n = (indexWeight n : ℂ) *
        (NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n -
          Complex.I * (-1 : ℂ) ^ n * (-1 : ℂ) *
            NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.2) n) :=
    ⟨_, hL φ hφ xi hxi, fun n => by simp [NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower]⟩
  obtain ⟨eU, hUs, hUe⟩ : ∃ e : ℤ → ℂ,
      (∀ F : Finset ℤ, (∀ n ∈ F, (NU : ℤ) ≤ |n|) → ∑ n ∈ F, ‖e n‖ ^ 2 ≤ CU) ∧
      ∀ n : ℤ, e n = (indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ true ⟨xi n, hz⟩ 1 0) -
          (-Complex.I) * (-1 : ℂ) ^ n * (-1 : ℂ) ^ (N + 1) *
            NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.1) (-n)) :=
    ⟨_, hU φ hφ xi hxi, fun n => by simp⟩
  set e1 : ℤ → ℂ := fun n => (indexWeight n : ℂ) *
      (NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n -
        (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)) with he1
  set e2 : ℤ → ℂ := fun n => (indexWeight n : ℂ) *
      (NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n -
        (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)) with he2
  set eUp : ℤ → ℂ := fun n => (-1 : ℂ) ^ N * eU n with heUp
  have h11 : ∀ n : ℤ,
      NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
        Complex.I * ((-1 : ℂ) ^ (n + 1)) *
          NlsGge.Pilot.physicalFourier
            (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
          eL n / indexValue n ∧
      NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
        Complex.I * ((-1 : ℂ) ^ n) *
          NlsGge.Pilot.physicalFourier
            (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
          eUp n / indexValue n := by
    intro n
    refine ⟨?_, ?_⟩
    · rw [hLe n, zpow_add_one₀ hm1]
      unfold indexValue
      field_simp [hw n]
      ring
    · have hpow : (-1 : ℂ) ^ N * (-1 : ℂ) ^ (N + 1) = -1 := by
        rw [pow_succ, ← mul_assoc, ← mul_pow]; simp
      unfold NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper indexValue
      rw [heUp]
      beta_reduce
      rw [hUe n]
      have hcancel : ∀ y z : ℂ, y * ((indexWeight n : ℂ) * z) / (indexWeight n : ℂ) = y * z :=
        fun y z => by field_simp [hw n]
      rw [hcancel]
      by_cases hz : xi n = 0
      · simp only [dif_pos hz]
        linear_combination (-(Complex.I * (-1 : ℂ) ^ n *
          NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.1) (-n))) * hpow
      · simp only [dif_neg hz]
        linear_combination (-(Complex.I * (-1 : ℂ) ^ n *
          NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.1) (-n))) * hpow
  have h12 : ∀ n : ℤ,
      NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ) := by
    intro n
    refine ⟨?_, ?_⟩
    · show _ = _ + (indexWeight n : ℂ) * _ / (indexWeight n : ℂ)
      rw [mul_div_cancel_left₀ _ (hw n)]
      ring
    · show _ = _ + (indexWeight n : ℂ) * _ / (indexWeight n : ℂ)
      rw [mul_div_cancel_left₀ _ (hw n)]
      ring
  have h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k :=
    fun k hk => integrated_riccati_vanishing N k φ hk
  have h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N (sobolevNorm N φ) lam.1 →
      monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam :=
    fun lam hlam => (WKB_monodromy_entries N (sobolevNorm N φ) φ lam le_rfl hlam).2
  have hSb := Sb_le φ hφ
  rw [← hS0] at hSb
  have hSb0 := NlsGge.ThirdConsultation.KSPS016W.Sb_nonneg φ
  have hI := hIb φ hφ (N + 1) (by omega) le_rfl
  have hUpn : ∀ n : ℤ, ‖eUp n‖ = ‖eU n‖ := fun n => by
    rw [heUp]; beta_reduce
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  -- per-index bounds
  have hpt : ∀ n ∈ F,
      (0 ≤ indexWeight n ^ (N + 1) * ‖KSPSWKB.antitraceError N φ xi n‖ ∧
        indexWeight n ^ (N + 1) * ‖KSPSWKB.antitraceError N φ xi n‖ ≤
          K * ((2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) +
            (2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) +
            1 / indexWeight n + ‖e1 n‖ + ‖e2 n‖ + ‖eL n‖ + ‖eU n‖)) ∧
      (0 ≤ indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ xi n‖ ∧
        indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ xi n‖ ≤
          K * ((2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) +
            (2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) +
            1 / indexWeight n + ‖e1 n‖ + ‖e2 n‖ + ‖eL n‖ + ‖eU n‖)) := by
    intro n hn
    have hnT := hFT n hn
    have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos (NlsGge.ThirdConsultation.KSPS015W.one_le_w n)
    obtain ⟨hν1, -⟩ := NlsGge.ThirdConsultation.KSPS016W.tail_nat a _ n hnT
    obtain ⟨hD1, hD2⟩ := deriv_fourier_le φ n hν1
    have tb := NlsGge.ThirdConsultation.KSPS016W.tail_bounds N φ xi a ha hxi eL eUp e1 e2 n
      (h11 n) (h12 n) h13 h14 hnT
    rw [hUpn n] at tb
    rw [← hA0] at tb
    have hv : 0 ≤ 1 / indexWeight n := by positivity
    have hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ K * x := fun x hx => mul_nonneg hK0 hx
    have hmono : K * (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
          ‖physicalFourier (iteratedDerivative N φ.2) n‖ + 1 / indexWeight n + ‖e1 n‖ + ‖e2 n‖ +
          ‖eL n‖ + ‖eU n‖) ≤
        K * ((2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) +
          (2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) +
          1 / indexWeight n + ‖e1 n‖ + ‖e2 n‖ + ‖eL n‖ + ‖eU n‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    have hA := anti_rhs_le A0 S0 CI (NlsGge.ThirdConsultation.KSPS016W.Sb φ)
      ‖integralRiccatiLeft φ (N + 1)‖ ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖
      ‖physicalFourier (iteratedDerivative N φ.2) n‖ (1 / indexWeight n) ‖e1 n‖ ‖e2 n‖ ‖eL n‖ ‖eU n‖ K
      hSb0 hSb (norm_nonneg _) hI hA00 (norm_nonneg _) (norm_nonneg _) hv (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) hK
    have hD := dir_rhs_le A0 S0 CI (NlsGge.ThirdConsultation.KSPS016W.Sb φ)
      ‖integralRiccatiLeft φ (N + 1)‖ ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖
      ‖physicalFourier (iteratedDerivative N φ.2) n‖ (1 / indexWeight n) ‖e1 n‖ ‖e2 n‖ ‖eL n‖ ‖eU n‖ K
      hSb0 hSb (norm_nonneg _) hI hA00 (norm_nonneg _) (norm_nonneg _) hv (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) hK
    refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
    · exact (tb.1.trans hA).trans hmono
    · exact (tb.2.trans hD).trans hmono
  obtain ⟨hFo1, hFo2⟩ := fourier_sums_le φ hφ F
  rw [← hP2] at hFo1 hFo2
  have hsv : ∑ n ∈ F, (1 / indexWeight n) ^ 2 ≤ Sv := by
    rw [hSv]
    exact NlsGge.ThirdConsultation.KSPS016W.sq_summable_inv_w.sum_le_tsum F (fun n _ => sq_nonneg _)
  have hs1 : ∑ n ∈ F, ‖e1 n‖ ^ 2 ≤ C1 := h1 φ hφ xi hxi F hF1
  have hs2 : ∑ n ∈ F, ‖e2 n‖ ^ 2 ≤ C2 := h2 φ hφ xi hxi F hF2
  refine ⟨?_, ?_⟩
  · exact sum_sq_le_seven F _ _ _ _ _ _ _ _ K hK0 (fun n hn => (hpt n hn).1) _ _ _ _ _ _ _
      hFo1 hFo2 hsv hs1 hs2 (hLs F hFL) (hUs F hFU)
  · exact sum_sq_le_seven F _ _ _ _ _ _ _ _ K hK0 (fun n hn => (hpt n hn).2) _ _ _ _ _ _ _
      hFo1 hFo2 hsv hs1 hs2 (hLs F hFL) (hUs F hFU)

end NlsGge.ThirdConsultation.KSPS016U
