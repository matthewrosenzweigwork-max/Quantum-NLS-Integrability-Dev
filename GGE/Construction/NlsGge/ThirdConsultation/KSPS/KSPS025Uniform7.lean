import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform5
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU4

                                                                                 
                                                                                                                    
                                                                                                                      
                                                                                                                  
                                                                
                                                                                                                  
                                                                                                                   
                                                                                                 
                                                                                                                     
                                                                                                                 
                                                                                                                     
                                                                                                         
                                                                                                                
                                                                                                    
                                                                                                                 
                                                                                                  
                                                                                               
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS025U7
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W
open NlsGge.ThirdConsultation.KSPS024W NlsGge.ThirdConsultation.KSPS025W

/-! ### Pure lemmas -/

theorem sum_sq_le_sq_sum (F : Finset ℤ) (x : ℤ → ℝ) (h0 : ∀ n ∈ F, 0 ≤ x n) :
    ∑ n ∈ F, x n ^ 2 ≤ (∑ n ∈ F, x n) ^ 2 := by
  have hS : ∀ n ∈ F, x n ^ 2 ≤ x n * ∑ m ∈ F, x m := by
    intro n hn
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum h0 hn) (h0 n hn)
  refine (Finset.sum_le_sum hS).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, pow_two]

theorem sq_add4_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

theorem sq_add2_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

theorem abs_le_w (n : ℤ) : |(n : ℝ)| ≤ indexWeight n := by
  unfold indexWeight
  exact Real.le_sqrt_of_sq_le (by rw [sq_abs]; linarith)

theorem w_le_of_natAbs (n : ℤ) (M : ℕ) (hn : n.natAbs ≤ M) : indexWeight n ≤ 1 + M := by
  unfold indexWeight
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : |(n : ℝ)| ≤ M := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast hn
  have h2 := sq_abs (n : ℝ)
  have h3 : |(n : ℝ)| ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h4 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

/-- Weighted Fourier coefficients of the N-th derivative. -/
theorem fourier_iter_le (N : ℕ) (φ : SobolevC N) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|) :
    ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ≤
        (2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ∧
    ‖physicalFourier (iteratedDerivative N φ.2) n‖ ≤
        (2 * Real.pi) ^ N * (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) := by
  obtain ⟨e1, e2, -, -⟩ := NlsGge.ThirdConsultation.KSPS016W.fourier_facts φ n hn
  have hb : ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N‖ ≤ (2 * Real.pi) ^ N * indexWeight n ^ N := by
    rw [norm_pow, ← mul_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      Complex.norm_intCast, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
    exact mul_le_mul_of_nonneg_left (abs_le_w n) (by positivity)
  constructor
  · rw [e1, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc _ ≤ (2 * Real.pi) ^ N * indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := by ring
  · rw [e2, norm_mul]
    calc _ ≤ (2 * Real.pi) ^ N * indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := by ring

/-- Finite-sum bound of the KSPS-025 bounding sequence `tP` from finite entry-error sums. -/
theorem tP_sum_le (N : ℕ) (φ : SobolevC N) (F : Finset ℤ) (hF1 : ∀ n ∈ F, 1 ≤ |(n : ℝ)|)
    (CE L : ℝ) (hL : ‖integralRiccatiLeft φ (N + 1)‖ ≤ L)
    (hE : ∀ (upper : Bool) (i j : Fin 2),
      ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ upper i j n‖) ^ 2 ≤ CE) :
    ∑ n ∈ F, tP N φ n ^ 2 ≤
      4 * (64 * CE + (2 * Real.pi) ^ (2 * N) * sobolevNorm N φ ^ 2 +
        4 * L ^ 2 * ∑' n : ℤ, (1 / indexWeight n) ^ 2) := by
  set e : Bool → Fin 2 → Fin 2 → ℤ → ℝ := fun b i j n =>
    indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ b i j n‖ with he
  set A : ℤ → ℝ := fun n => indexWeight n ^ (N + 1) * (Eent N φ true n + Eent N φ false n) with hA
  set F1 : ℤ → ℝ := fun n => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ with hF1d
  set F2 : ℤ → ℝ := fun n => ‖physicalFourier (iteratedDerivative N φ.2) n‖ with hF2d
  set Dd : ℤ → ℝ := fun n => 2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) with hDd
  have htP : ∀ n, tP N φ n = A n + F1 n + F2 n + Dd n := fun n => rfl
  -- the entry part
  have hAe : ∀ n, A n = (e true 0 0 n + e true 0 1 n + e true 1 0 n + e true 1 1 n) +
      (e false 0 0 n + e false 0 1 n + e false 1 0 n + e false 1 1 n) := by
    intro n; simp only [hA, he, Eent]; ring
  have hA2 : ∀ n, A n ^ 2 ≤ 8 * (e true 0 0 n ^ 2 + e true 0 1 n ^ 2 + e true 1 0 n ^ 2 + e true 1 1 n ^ 2 +
      (e false 0 0 n ^ 2 + e false 0 1 n ^ 2 + e false 1 0 n ^ 2 + e false 1 1 n ^ 2)) := by
    intro n
    rw [hAe]
    have h1 := sq_add2_le (e true 0 0 n + e true 0 1 n + e true 1 0 n + e true 1 1 n)
      (e false 0 0 n + e false 0 1 n + e false 1 0 n + e false 1 1 n)
    have h2 := sq_add4_le (e true 0 0 n) (e true 0 1 n) (e true 1 0 n) (e true 1 1 n)
    have h3 := sq_add4_le (e false 0 0 n) (e false 0 1 n) (e false 1 0 n) (e false 1 1 n)
    linarith
  have hAs : ∑ n ∈ F, A n ^ 2 ≤ 64 * CE := by
    refine (Finset.sum_le_sum (fun n _ => hA2 n)).trans ?_
    rw [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib]
    have := hE true 0 0; have := hE true 0 1; have := hE true 1 0; have := hE true 1 1
    have := hE false 0 0; have := hE false 0 1; have := hE false 1 0; have := hE false 1 1
    simp only [he] at *
    linarith
  -- the Fourier part
  have hFF : ∑ n ∈ F, (F1 n ^ 2 + F2 n ^ 2) ≤ (2 * Real.pi) ^ (2 * N) * sobolevNorm N φ ^ 2 := by
    have hp : ∀ n ∈ F, F1 n ^ 2 + F2 n ^ 2 ≤ (2 * Real.pi) ^ (2 * N) *
        ((indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖) ^ 2 +
         (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖) ^ 2) := by
      intro n hn
      obtain ⟨g1, g2⟩ := fourier_iter_le N φ n (hF1 n hn)
      have k1 := pow_le_pow_left₀ (norm_nonneg _) g1 2
      have k2 := pow_le_pow_left₀ (norm_nonneg _) g2 2
      have e2 : (2 * Real.pi) ^ (2 * N) = ((2 * Real.pi) ^ N) ^ 2 := by rw [← pow_mul]; ring_nf
      rw [e2]
      simp only [hF1d, hF2d]
      rw [mul_pow] at k1 k2
      nlinarith
    refine (Finset.sum_le_sum hp).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (NlsGge.ThirdConsultation.KSPSU4.weighted_fourier_le N φ F)
      (by positivity)
  -- the integral part
  have hDs : ∑ n ∈ F, Dd n ^ 2 ≤ 4 * L ^ 2 * ∑' n : ℤ, (1 / indexWeight n) ^ 2 := by
    have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
    have hp : ∀ n ∈ F, Dd n ^ 2 ≤ 4 * L ^ 2 * (1 / indexWeight n) ^ 2 := by
      intro n _
      simp only [hDd]
      have h1 : ‖integralRiccatiLeft φ (N + 1)‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hL 2
      nlinarith [sq_nonneg (1 / indexWeight n)]
    refine (Finset.sum_le_sum hp).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (NlsGge.ThirdConsultation.KSPS016W.sq_summable_inv_w.sum_le_tsum F (fun n _ => sq_nonneg _))
      (by positivity)
  have hsplit : ∀ n ∈ F, tP N φ n ^ 2 ≤ 4 * (A n ^ 2 + (F1 n ^ 2 + F2 n ^ 2) + Dd n ^ 2) := by
    intro n _
    rw [htP]
    have := sq_add4_le (A n) (F1 n) (F2 n) (Dd n)
    linarith
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith

/-! ### The conditional assembly -/

theorem midpoint_spectral_expansion_uniform_of
    (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (hloc0 : ∃ a : ℝ, 0 ≤ a ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ n : ℤ,
      ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n ∧
      ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (h540 : ∃ (M : ℕ) (C : ℝ), 0 < C ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ a : ℤ → ℂ,
      (∀ n : ℤ, (M : ℤ) ≤ |n| →
        criticalEigenvalue φ n - (periodicPlus φ n + periodicMinus φ n) / 2 =
          (periodicPlus φ n - periodicMinus φ n) ^ 2 * a n) ∧
      (∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) → ∑ n ∈ F, ‖a n‖ ^ 2 ≤ C))
    (hsp0 : ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ n : ℤ,
      ‖spectralPolynomial φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (h26 : ∃ (M : ℕ) (CE : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      (∀ (upper : Bool) (i j : Fin 2) (F : Finset ℤ), (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ upper i j n‖) ^ 2 ≤ CE) ∧
      ∃ hplus hminus : ℤ → ℂ, ∀ n : ℤ, (M : ℤ) ≤ |n| →
        KSPSWKB.endpointQuadraticFormula N φ n hplus hminus)
    (h24 : ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2 ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖)^2) ≤ C^2 := by
  obtain ⟨a, ha, hloc⟩ := hloc0
  obtain ⟨M54, C54, hC54, h54⟩ := h540
  obtain ⟨D, hD, hspoly⟩ := hsp0
  obtain ⟨L, hL0, hLb⟩ := NlsGge.ThirdConsultation.KSPS025U5.riccati_consts_uniform N hN B₀ hB₀
  obtain ⟨M26, CE, h26b⟩ := h26
  obtain ⟨M24, C24, h24b⟩ := h24
  set S : ℝ := ∑' n : ℤ, (1 / indexWeight n) ^ 2 with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun n => sq_nonneg _)
  set CA : ℝ := 1 + C54 with hCA
  set M : ℕ := ⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N B₀⌉₊ +
    ⌈2 * NlsGge.ThirdConsultation.KSPS025U5.SbB N B₀⌉₊ + ⌈2 * (a + L)⌉₊ + ⌈2 * L⌉₊ +
    M26 + M24 + M54 + 1 with hM
  set T : ℝ := 4 * (64 * |CE| + (2 * Real.pi) ^ (2 * N) * B₀ ^ 2 + 4 * L ^ 2 * S) with hT
  set K : ℝ := (1 + (M : ℝ)) ^ (N + 1) * (a + D) with hK
  set Ctot : ℝ := 2 * ((1600 * CA) ^ 2 * T ^ 2 + |C24|) +
    ((Finset.Icc (-(M : ℤ)) M).card : ℝ) * K ^ 2 with hCtot
  have hCtot0 : 0 ≤ Ctot := by positivity
  refine ⟨Real.sqrt Ctot, Real.sqrt_nonneg _, fun φ hφ => ?_⟩
  -- per-φ data
  obtain ⟨hEs, hplus, hminus, hqf⟩ := h26b φ hφ
  obtain ⟨A, hAid, hAsum⟩ := h54 φ hφ
  obtain ⟨hJ, hLp, -, hIN⟩ := hLb φ hφ
  have hsN0 : 0 ≤ sobolevNorm N φ := Real.sqrt_nonneg _
  -- the pointwise bound at every label
  set x : ℤ → ℝ := fun n => indexWeight n ^ (N + 1) * ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖ with hx
  have hx0 : ∀ n, 0 ≤ x n := fun n =>
    mul_nonneg (pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _) (norm_nonneg _)
  have hlow : ∀ n : ℤ, ¬ ((M : ℤ) ≤ |n|) → x n ≤ K := by
    intro n hn
    have hnM : n.natAbs ≤ M := by
      have h1 : |n| < (M : ℤ) := lt_of_not_ge hn
      have h2 := Int.natCast_natAbs n
      omega
    have hw1 := KSPS015W.one_le_w n
    have hw0 : 0 < indexWeight n := by linarith
    have hwM : indexWeight n ≤ 1 + M := w_le_of_natAbs n M hnM
    obtain ⟨hp, hm⟩ := hloc φ hφ n
    have haw : a / indexWeight n ≤ a := div_le_self ha hw1
    have hmid : ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a := by
      have e : NlsGge.ThirdConsultation.KSPS.midpoint φ n - (n : ℂ) * (Real.pi : ℂ) =
          ((periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)) + (periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ))) / 2 := by
        unfold NlsGge.ThirdConsultation.KSPS.midpoint; ring
      rw [e, norm_div, Complex.norm_ofNat]
      have := norm_add_le (periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ))
        (periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ))
      linarith
    have hdiff : ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖ ≤ a + D := by
      have e : NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n =
          (NlsGge.ThirdConsultation.KSPS.midpoint φ n - (n : ℂ) * (Real.pi : ℂ)) - (spectralPolynomial φ n - (n : ℂ) * (Real.pi : ℂ)) := by ring
      rw [e]
      have := norm_sub_le (NlsGge.ThirdConsultation.KSPS.midpoint φ n - (n : ℂ) * (Real.pi : ℂ))
        (spectralPolynomial φ n - (n : ℂ) * (Real.pi : ℂ))
      have := hspoly φ hφ n
      linarith
    have hwp : indexWeight n ^ (N + 1) ≤ (1 + (M : ℝ)) ^ (N + 1) := pow_le_pow_left₀ hw0.le hwM _
    exact mul_le_mul hwp hdiff (norm_nonneg _) (by positivity)
  have htail : ∀ n : ℤ, (M : ℤ) ≤ |n| →
      x n ≤ CA * (40 * tP N φ n) ^ 2 +
        indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖ := by
    intro n hn
    have hnR : (M : ℝ) ≤ |(n : ℝ)| := by
      have := (Int.cast_le (R := ℝ)).2 hn
      rwa [Int.cast_abs, Int.cast_natCast] at this
    have hcast : ∀ m : ℕ, m ≤ M → ((m : ℕ) : ℤ) ≤ |n| := fun m hm =>
      le_trans (by exact_mod_cast hm) hn
    have hthr := Nat.ceil_mono (NlsGge.ThirdConsultation.KSPS025U5.threshold_le N B₀ φ hφ)
    have hSb := Nat.ceil_mono (show 2 * NlsGge.ThirdConsultation.KSPS016W.Sb φ ≤
      2 * NlsGge.ThirdConsultation.KSPS025U5.SbB N B₀ by
        linarith [NlsGge.ThirdConsultation.KSPS025U5.Sb_le N B₀ φ hφ])
    have h1 := hcast (⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)
      (by omega)
    have h2 := hcast (⌈a⌉₊ + ⌈2 * NlsGge.ThirdConsultation.KSPS016W.Sb φ⌉₊ + 1) (by omega)
    have hM1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
      linarith
    have hc1 : 2 * (a + L) ≤ (M : ℝ) := by
      have := Nat.le_ceil (2 * (a + L))
      have : ((⌈2 * (a + L)⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show ⌈2 * (a + L)⌉₊ ≤ M by omega)
      linarith
    have hc2 : 2 * L ≤ (M : ℝ) := by
      have := Nat.le_ceil (2 * L)
      have : ((⌈2 * L⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show ⌈2 * L⌉₊ ≤ M by omega)
      linarith
    have h4 : 2 * (a + Jsum φ) ≤ indexWeight n := by
      have := abs_le_w n
      linarith
    have hL : 2 * NlsGge.ThirdConsultation.KSPS024W.Lp φ ≤ |(n : ℝ)| ^ 2 := by
      have : |(n : ℝ)| ≤ |(n : ℝ)| ^ 2 := by nlinarith
      linarith
    have hq := hqf n (hcast M26 (by omega))
    have hid := hAid n (hcast M54 (by omega))
    have hAb : ‖A n‖ ≤ CA := by
      have h := hAsum {n} (fun m hm => by rw [Finset.mem_singleton.1 hm]; exact hcast M54 (by omega))
      rw [Finset.sum_singleton] at h
      nlinarith [sq_nonneg (‖A n‖ - 1)]
    have ht := NlsGge.ThirdConsultation.KSPS025U5.tail025_U N hN φ a ha (fun m => (hloc φ hφ m).1)
      (fun m => (hloc φ hφ m).2) hplus hminus n (A n) CA hAb hid h1 h2 h4 hL hq
    have e : NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n =
        (NlsGge.ThirdConsultation.KSPS.midpoint φ n - criticalEigenvalue φ n) + (criticalEigenvalue φ n - spectralPolynomial φ n) := by ring
    have hw0 : 0 ≤ indexWeight n ^ (N + 1) :=
      pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _
    have h9 := mul_le_mul_of_nonneg_left (norm_add_le
      (NlsGge.ThirdConsultation.KSPS.midpoint φ n - criticalEigenvalue φ n) (criticalEigenvalue φ n - spectralPolynomial φ n)) hw0
    rw [mul_add] at h9
    simp only [hx]
    rw [e]
    linarith
  -- finite sums
  have hsum : ∀ F : Finset ℤ, ∑ n ∈ F, x n ^ 2 ≤ Ctot := by
    intro F
    rw [← Finset.sum_filter_add_sum_filter_not F (fun n : ℤ => (M : ℤ) ≤ |n|)]
    set Ft := F.filter (fun n : ℤ => (M : ℤ) ≤ |n|) with hFt
    set Fl := F.filter (fun n : ℤ => ¬ ((M : ℤ) ≤ |n|)) with hFl
    have hFtM : ∀ n ∈ Ft, (M : ℤ) ≤ |n| := fun n hn => (Finset.mem_filter.1 hn).2
    -- tail
    have hT1 : ∑ n ∈ Ft, tP N φ n ^ 2 ≤ T := by
      have hF1 : ∀ n ∈ Ft, 1 ≤ |(n : ℝ)| := by
        intro n hn
        have h := hFtM n hn
        have : (1 : ℤ) ≤ |n| := le_trans (by exact_mod_cast (show 1 ≤ M by omega)) h
        have := (Int.cast_le (R := ℝ)).2 this
        rwa [Int.cast_abs, Int.cast_one] at this
      have hE : ∀ (upper : Bool) (i j : Fin 2),
          ∑ n ∈ Ft, (indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ upper i j n‖) ^ 2 ≤ |CE| :=
        fun u i j => (hEs u i j Ft (fun n hn => le_trans (by exact_mod_cast (show M26 ≤ M by omega))
          (hFtM n hn))).trans (le_abs_self _)
      have h := tP_sum_le N φ Ft hF1 |CE| L hIN hE
      have hB2 : sobolevNorm N φ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hsN0 hφ 2
      have hpi0 : 0 ≤ (2 * Real.pi) ^ (2 * N) := by positivity
      have := mul_le_mul_of_nonneg_left hB2 hpi0
      rw [hT]
      linarith
    have htP0 : ∀ n, 0 ≤ tP N φ n := by
      intro n
      unfold tP Eent
      have hw0 : 0 ≤ indexWeight n := le_trans zero_le_one (KSPS015W.one_le_w n)
      positivity
    have hT4 : ∑ n ∈ Ft, (tP N φ n ^ 2) ^ 2 ≤ T ^ 2 := by
      refine (sum_sq_le_sq_sum Ft (fun n => tP N φ n ^ 2) (fun n _ => sq_nonneg _)).trans ?_
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun n _ => sq_nonneg _)) hT1 2
    have hY : ∑ n ∈ Ft, (indexWeight n ^ (N + 1) *
        ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2 ≤ |C24| :=
      (h24b φ hφ Ft (fun n hn => le_trans (by exact_mod_cast (show M24 ≤ M by omega)) (hFtM n hn))).trans
        (le_abs_self _)
    have hCA0 : 0 ≤ CA := by rw [hCA]; linarith
    have hpt : ∀ n ∈ Ft, x n ^ 2 ≤ 2 * ((1600 * CA) ^ 2 * (tP N φ n ^ 2) ^ 2 +
        (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2) := by
      intro n hn
      have h := htail n (hFtM n hn)
      have h2 := pow_le_pow_left₀ (hx0 n) h 2
      have e : CA * (40 * tP N φ n) ^ 2 = 1600 * CA * tP N φ n ^ 2 := by ring
      rw [e] at h2
      have h3 := sq_add2_le (1600 * CA * tP N φ n ^ 2)
        (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖)
      have e2 : (1600 * CA * tP N φ n ^ 2) ^ 2 = (1600 * CA) ^ 2 * (tP N φ n ^ 2) ^ 2 := by ring
      rw [e2] at h3
      linarith
    have hTail : ∑ n ∈ Ft, x n ^ 2 ≤ 2 * ((1600 * CA) ^ 2 * T ^ 2 + |C24|) := by
      refine (Finset.sum_le_sum hpt).trans ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      have := mul_le_mul_of_nonneg_left hT4 (sq_nonneg (1600 * CA))
      linarith
    -- low labels
    have hLow : ∑ n ∈ Fl, x n ^ 2 ≤ ((Finset.Icc (-(M : ℤ)) M).card : ℝ) * K ^ 2 := by
      have hsub : Fl ⊆ Finset.Icc (-(M : ℤ)) M := by
        intro n hn
        have h := (Finset.mem_filter.1 hn).2
        rw [Finset.mem_Icc]
        constructor <;> cases abs_cases n <;> omega
      have hK0 : 0 ≤ K := by rw [hK]; positivity
      have hp : ∀ n ∈ Fl, x n ^ 2 ≤ K ^ 2 := fun n hn =>
        pow_le_pow_left₀ (hx0 n) (hlow n (Finset.mem_filter.1 hn).2) 2
      refine (Finset.sum_le_sum hp).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (sq_nonneg _)
    rw [hCtot]
    linarith
  refine ⟨?_, fun F => ?_⟩
  · rw [wl2_iff]
    exact summable_of_sum_le (fun n => sq_nonneg _) hsum
  · rw [Real.sq_sqrt hCtot0]
    exact hsum F

end
end NlsGge.ThirdConsultation.KSPS025U7
