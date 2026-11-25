import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS026Host
import NlsGge.ThirdConsultation.KSPS.KSPS016Support
import NlsGge.ThirdConsultation.KSPS.KSPS026Support1

/- KSPS-026 SUPPORT3 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS026Support3.lean.
   KSPS-026 step 2 (KSPS026_MAP01.md): the eight entry errors endpointEntryError N φ upper i j are weighted l2 of
   order N+1, by the KSPS-016 tail algebra (proof development KSPS016Support: rem_formulas, phase_q, fourier_facts):
   with s = (-1)^n, ε = (2 i ξ)^-N, w = indexWeight n, on the tail
     E00 = s ε e1/w,  E11 = s ε e2/w,
     E01 = i hatφ1(-n) (ε p - 1) + s ε (-1)^N eU/w,  E10 = -i hatφ2(n) (ε p - 1) + s ε eL/w   (p = (2 π i n)^N),
   and w^(N+1)|E| is dominated by |e1|, |e2|, A |hat(D^N φ1)(-n)| + |eU|, A |hat(D^N φ2)(n)| + |eL|.
   The KSPS-011/012/013 head conclusions for the sample sequence xi (= periodicPlus φ or periodicMinus φ) enter as
   explicit hypotheses of exactly their landed types; the zero-filled lam = 0 case lies in the finite exceptional set.
   Also: the bridge WeightedL2Error (N+1) e <-> KSPS026W.WL2 indexWeight (N+1) e. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS026W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS015W NlsGge.ThirdConsultation.KSPS016W

/-! ### Bridges -/

theorem rpow_two_mul (N : ℕ) (n : ℤ) :
    indexWeight n ^ (2 * ((N + 1 : ℕ) : ℝ)) = (indexWeight n ^ (N + 1)) ^ 2 := by
  rw [show (2 * ((N + 1 : ℕ) : ℝ)) = ((2 * (N + 1) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  ring

theorem weightedL2Error_iff (N : ℕ) (e : ℤ → ℂ) :
    WeightedL2Error ((N + 1 : ℕ) : ℝ) e ↔ WL2 indexWeight (N + 1) e := by
  unfold WeightedL2Error WL2
  have h : (fun n : ℤ => indexWeight n ^ (2 * ((N + 1 : ℕ) : ℝ)) * ‖e n‖ ^ 2) =
      (fun n : ℤ => (indexWeight n ^ (N + 1) * ‖e n‖) ^ 2) := by
    funext n
    rw [rpow_two_mul, mul_pow]
  rw [h]

theorem one_le_indexWeight' : ∀ n : ℤ, 1 ≤ indexWeight n := one_le_w

/-! ### Pure algebra and estimates of the entry errors -/

theorem sign_cases (n : ℤ) : (-1 : ℂ) ^ n = 1 ∨ (-1 : ℂ) ^ n = -1 := by
  rcases Int.even_or_odd n with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem diag00_alg (N : ℕ) (s Z IL e w : ℂ) (hs : s = 1 ∨ s = -1) (hZ : Z ≠ 0) :
    s * (Z ^ N)⁻¹ * (s / Z * IL + e / w) - IL / Z ^ (N + 1) = s * (Z ^ N)⁻¹ * (e / w) := by
  rcases hs with rfl | rfl <;> · rw [pow_succ]; field_simp; ring

theorem diag11_alg (N : ℕ) (s Z IL e w : ℂ) (hs : s = 1 ∨ s = -1) (hZ : Z ≠ 0) :
    s * (Z ^ N)⁻¹ * (s * (-1) / Z * IL + e / w) - -IL / Z ^ (N + 1) = s * (Z ^ N)⁻¹ * (e / w) := by
  rcases hs with rfl | rfl <;> · rw [pow_succ]; field_simp; ring

theorem off01_alg (s ε p G sN eU w r : ℂ) (hs : s = 1 ∨ s = -1)
    (hr : r = Complex.I * s * p * G + sN * eU / w) :
    s * ε * r - Complex.I * G = Complex.I * G * (ε * p - 1) + s * ε * (sN * eU / w) := by
  subst hr
  rcases hs with rfl | rfl <;> ring

theorem off10_alg (s ε p G eL w r : ℂ) (hs : s = 1 ∨ s = -1)
    (hr : r = -(Complex.I * s * p * G) + eL / w) :
    s * ε * r - -Complex.I * G = -Complex.I * G * (ε * p - 1) + s * ε * (eL / w) := by
  subst hr
  rcases hs with rfl | rfl <;> ring

theorem rem_part_bound (N : ℕ) (w X : ℝ) (s ε c e : ℂ) (hw : 0 < w) (hwX : w ≤ 2 * X)
    (hs : ‖s‖ = 1) (hc : ‖c‖ = 1) (hε : ‖ε‖ = ((2 * X) ^ N)⁻¹) :
    w ^ (N + 1) * ‖s * ε * (c * e / (w : ℂ))‖ ≤ ‖e‖ := by
  have h2X : 0 < 2 * X := by linarith
  have hr0 : 0 ≤ w / (2 * X) := div_nonneg hw.le h2X.le
  have hr1 : w / (2 * X) ≤ 1 := by rw [div_le_one h2X]; exact hwX
  have hrN : (w / (2 * X)) ^ N ≤ 1 := pow_le_one₀ hr0 hr1
  have e1 : w ^ (N + 1) * ‖s * ε * (c * e / (w : ℂ))‖ = (w / (2 * X)) ^ N * ‖e‖ := by
    rw [norm_mul, norm_mul, norm_div, norm_mul, hs, hc, hε, Complex.norm_real, Real.norm_of_nonneg hw.le,
      div_pow]
    field_simp
    ring
  rw [e1]
  have := mul_le_mul_of_nonneg_right hrN (norm_nonneg e)
  linarith

theorem lead_part_bound (N : ℕ) (w A F : ℝ) (κ G q : ℂ) (hw : 1 ≤ w) (hA : 0 ≤ A) (hκ : ‖κ‖ = 1)
    (hq : ‖q - 1‖ ≤ A / (w * w)) (hG : w ^ N * ‖G‖ ≤ F) :
    w ^ (N + 1) * ‖κ * G * (q - 1)‖ ≤ A * F := by
  have hw0 : 0 < w := by linarith
  have hF : 0 ≤ F := le_trans (mul_nonneg (pow_nonneg hw0.le N) (norm_nonneg G)) hG
  have e1 : w ^ (N + 1) * ‖κ * G * (q - 1)‖ = (w ^ N * ‖G‖) * (w * ‖q - 1‖) := by
    rw [norm_mul, norm_mul, hκ, pow_succ]; ring
  rw [e1]
  have h1 : w * ‖q - 1‖ ≤ A := by
    have := mul_le_mul_of_nonneg_left hq hw0.le
    have e2 : w * (A / (w * w)) = A / w := by field_simp
    rw [e2] at this
    exact this.trans (div_le_self hA hw)
  exact (mul_le_mul hG h1 (mul_nonneg hw0.le (norm_nonneg _)) hF).trans (le_of_eq (mul_comm F A))

/-! ### Entry values -/

theorem sec_apply {N : ℕ} (φ : SobolevC N) (n : ℤ) (lam : {z : ℂ // z ≠ 0}) (i j : Fin 2) :
    KSPSWKB.scaledEndpointCorrection N φ n lam i j =
      (-1 : ℂ) ^ n * ((2 * Complex.I * lam.1) ^ N)⁻¹ *
        (if j = 0 then rf φ lam i else rt φ lam i) := by
  unfold KSPSWKB.scaledEndpointCorrection rf rt
  congr 1

theorem entryError_eq {N : ℕ} (φ : SobolevC N) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (i j : Fin 2) (n : ℤ) (hz : xi n ≠ 0) :
    KSPSWKB.endpointEntryError N φ upper i j n =
      KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ i j -
        (!![integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1),
            Complex.I * physicalFourier (toPotPair φ).1 (-n);
            -Complex.I * physicalFourier (toPotPair φ).2 n,
            -integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  unfold KSPSWKB.endpointEntryError
  have h := hxe n
  revert h
  generalize (if upper then periodicPlus φ n else periodicMinus φ n) = l
  intro h
  subst h
  simp only [dif_neg hz]

/-! ### Per-index tail bound -/

theorem entry_tail_bound
    (N : ℕ) (φ : SobolevC N) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (eL eU e1 e2 : ℤ → ℂ) (n : ℤ)
    (h11n : NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
          Complex.I * ((-1 : ℂ) ^ (n + 1)) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
            eL n / indexValue n ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
          Complex.I * ((-1 : ℂ) ^ n) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
            eU n / indexValue n)
    (h12n : NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ))
    (hLR : integralRiccatiLeft φ (N + 1) = integralRiccatiRight φ (N + 1))
    (hn : ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (i j : Fin 2) :
    indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ upper i j n‖ ≤
      ‖e1 n‖ + ‖e2 n‖ + ((N : ℝ) * 2 ^ N * (2 * a)) *
        (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
          ‖physicalFourier (iteratedDerivative N φ.2) n‖) + (‖eU n‖ + ‖eL n‖) := by
  obtain ⟨hX1, hXT, hwX⟩ := tail_facts a _ ha xi hxi n hn
  obtain ⟨hν1, hνa⟩ := tail_nat a _ n hn
  have hz : xi n ≠ 0 := by
    intro h; rw [h, norm_zero] at hX1; norm_num at hX1
  have hw1 := one_le_w n
  have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos hw1
  have hq := phase_q N a ha xi hxi n hν1 hνa hz hwX
  obtain ⟨hDF1, hDF2, hG1, hG2⟩ := fourier_facts φ n hν1
  obtain ⟨hrf0, hrt1, hrt0', hrf1'⟩ := rem_formulas N φ xi n hz eL eU e1 e2 h11n h12n hLR
  have hs := sign_cases n
  have hsg : ‖(-1 : ℂ) ^ n‖ = 1 := by rw [norm_zpow, norm_neg, norm_one, one_zpow]
  have hsN : ‖(-1 : ℂ) ^ N‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
  have hsNN : ((-1 : ℂ) ^ N) * ((-1 : ℂ) ^ N) = 1 := by rw [← mul_pow]; norm_num
  have hrt0 : rt φ ⟨xi n, hz⟩ 0 = Complex.I * (-1 : ℂ) ^ n * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
      physicalFourier (toPotPair φ).1 (-n) + (-1 : ℂ) ^ N * eU n / (indexWeight n : ℂ) := by
    rw [hDF1] at hrt0'
    linear_combination (-1 : ℂ) ^ N * hrt0' - (rt φ ⟨xi n, hz⟩ 0 - Complex.I * (-1 : ℂ) ^ n *
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N * physicalFourier (toPotPair φ).1 (-n)) * hsNN
  have hrf1 : rf φ ⟨xi n, hz⟩ 1 = -(Complex.I * (-1 : ℂ) ^ n * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
      physicalFourier (toPotPair φ).2 n) + eL n / (indexWeight n : ℂ) := by
    rw [hrf1', hDF2]
    ring
  have hε : ‖((2 * Complex.I * xi n) ^ N)⁻¹‖ = ((2 * ‖xi n‖) ^ N)⁻¹ := by
    rw [norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hZ : 2 * Complex.I * xi n ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hz
  have hA0 : (0 : ℝ) ≤ (N : ℝ) * 2 ^ N * (2 * a) := by positivity
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hmI : ‖-Complex.I‖ = 1 := by rw [norm_neg, Complex.norm_I]
  have h1 : (1 : ℂ) * eL n = eL n := one_mul _
  have n1 := norm_nonneg (e1 n)
  have n2 := norm_nonneg (e2 n)
  have n3 := norm_nonneg (eU n)
  have n4 := norm_nonneg (eL n)
  have n5 := norm_nonneg (physicalFourier (iteratedDerivative N φ.1) (-n))
  have n6 := norm_nonneg (physicalFourier (iteratedDerivative N φ.2) n)
  have hAF5 := mul_nonneg hA0 n5
  have hAF6 := mul_nonneg hA0 n6
  rw [entryError_eq φ upper xi hxe i j n hz, sec_apply]
  fin_cases i <;> fin_cases j
  · -- (0,0)
    simp only [Fin.zero_eta, Fin.isValue, if_true, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hrf0, diag00_alg N _ _ _ _ _ hs hZ]
    have := rem_part_bound N (indexWeight n) ‖xi n‖ ((-1 : ℂ) ^ n) ((2 * Complex.I * xi n) ^ N)⁻¹ 1 (e1 n)
      hw0 hwX hsg norm_one hε
    rw [one_mul] at this
    linarith
  · -- (0,1)
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, one_ne_zero, if_false, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [off01_alg _ _ _ _ _ _ _ _ hs hrt0]
    have b1 := lead_part_bound N (indexWeight n) ((N : ℝ) * 2 ^ N * (2 * a))
      ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ Complex.I (physicalFourier (toPotPair φ).1 (-n))
      (((2 * Complex.I * xi n) ^ N)⁻¹ * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N) hw1 hA0 hI hq hG1
    have b2 := rem_part_bound N (indexWeight n) ‖xi n‖ ((-1 : ℂ) ^ n) ((2 * Complex.I * xi n) ^ N)⁻¹
      ((-1 : ℂ) ^ N) (eU n) hw0 hwX hsg hsN hε
    have tri := norm_add_le (Complex.I * physicalFourier (toPotPair φ).1 (-n) *
        (((2 * Complex.I * xi n) ^ N)⁻¹ * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N - 1))
      ((-1 : ℂ) ^ n * ((2 * Complex.I * xi n) ^ N)⁻¹ * ((-1 : ℂ) ^ N * eU n / (indexWeight n : ℂ)))
    have h3 := mul_le_mul_of_nonneg_left tri (pow_nonneg hw0.le (N + 1))
    rw [mul_add] at h3
    nlinarith
  · -- (1,0)
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, if_true, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [off10_alg _ _ _ _ _ _ _ hs hrf1]
    have b1 := lead_part_bound N (indexWeight n) ((N : ℝ) * 2 ^ N * (2 * a))
      ‖physicalFourier (iteratedDerivative N φ.2) n‖ (-Complex.I) (physicalFourier (toPotPair φ).2 n)
      (((2 * Complex.I * xi n) ^ N)⁻¹ * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N) hw1 hA0 hmI hq hG2
    have b2 := rem_part_bound N (indexWeight n) ‖xi n‖ ((-1 : ℂ) ^ n) ((2 * Complex.I * xi n) ^ N)⁻¹
      1 (eL n) hw0 hwX hsg norm_one hε
    rw [h1] at b2
    have tri := norm_add_le (-Complex.I * physicalFourier (toPotPair φ).2 n *
        (((2 * Complex.I * xi n) ^ N)⁻¹ * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N - 1))
      ((-1 : ℂ) ^ n * ((2 * Complex.I * xi n) ^ N)⁻¹ * (eL n / (indexWeight n : ℂ)))
    have h3 := mul_le_mul_of_nonneg_left tri (pow_nonneg hw0.le (N + 1))
    rw [mul_add] at h3
    nlinarith
  · -- (1,1)
    simp only [Fin.isValue, Fin.mk_one, one_ne_zero, if_false, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hrt1, diag11_alg N _ _ _ _ _ hs hZ]
    have := rem_part_bound N (indexWeight n) ‖xi n‖ ((-1 : ℂ) ^ n) ((2 * Complex.I * xi n) ^ N)⁻¹ 1 (e2 n)
      hw0 hwX hsg norm_one hε
    rw [one_mul] at this
    linarith

/-! ### The eight weighted l2 estimates (conditional on the KSPS-011/012/013 head conclusions for xi) -/

theorem entry_errors_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (h11 : ∃ eLower eUpper : ℤ → ℂ,
      SquareSummable eLower ∧ SquareSummable eUpper ∧
      ∀ n : ℤ,
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
          Complex.I * ((-1 : ℂ) ^ (n + 1)) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
            eLower n / indexValue n ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
          Complex.I * ((-1 : ℂ) ^ n) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
            eUpper n / indexValue n)
    (h12 : ∃ e1 e2 : ℤ → ℂ,
      SquareSummable e1 ∧ SquareSummable e2 ∧
      ∀ n : ℤ,
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ))
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (i j : Fin 2) :
    WeightedL2Error ((N + 1 : ℕ) : ℝ) (KSPSWKB.endpointEntryError N φ upper i j) := by
  obtain ⟨eL, eU, hL, hU, h11'⟩ := h11
  obtain ⟨e1, e2, hs1, hs2, h12'⟩ := h12
  have hF2 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2) :=
    (hasSum_physicalFourier_sq _).summable
  have hF1 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2) :=
    (hasSum_physicalFourier_sq (iteratedDerivative N φ.1)).summable.comp_injective neg_injective
  have hLR := h13 (N + 1) ⟨by omega, le_rfl⟩
  have ht : Summable (fun n : ℤ => (‖e1 n‖ + ‖e2 n‖ + ((N : ℝ) * 2 ^ N * (2 * a)) *
        (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
          ‖physicalFourier (iteratedDerivative N φ.2) n‖) + (‖eU n‖ + ‖eL n‖)) ^ 2) := by
    refine sq_summable_add (sq_summable_add (sq_summable_add hs1 hs2)
      (sq_summable_mul_left _ (sq_summable_add hF1 hF2))) (sq_summable_add hU hL)
  unfold WeightedL2Error
  refine Summable.of_norm_bounded_eventually ht ?_
  filter_upwards [eventually_natAbs (⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)]
    with n hn
  beta_reduce
  rw [rpow_two_mul, ← mul_pow, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (mul_nonneg (pow_nonneg (le_trans zero_le_one (one_le_w n)) _) (norm_nonneg _))
    (entry_tail_bound N φ upper xi hxe a ha hxi eL eU e1 e2 n (h11' n) (h12' n) hLR hn i j) 2

end
end NlsGge.ThirdConsultation.KSPS026W
