import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS026Support5
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU3
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU4

/- KSPS025U14 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS025Uniform14.lean. Pro round-15 SUPPORT (never a packet), chain B.
   h26q (CORE): one uniform cutoff M for the KSPS-026 quadratic formula at both periodic endpoints
   (second conjunct of the h26 binder of KSPS025U7/U8; statement in proof development/KSPS025_CHAINB_STOP.md).
   Route = the landed per-φ KSPS026W.endpoint_side_of, per index, with every smallness threshold made uniform:
   * witnesses = the explicit radicand sequences of endpoint_side_of (third clause by `ring`);
   * q0 ≠ 0: q0 = -1 + Q, Q = αβ + (e + E00) - β(-i a2 + E10) (the endpoint_side_of decomposition, via
     KSPS026W.entryError_eq), |α|,|β| ≤ S0/w, |e| ≤ CIL/w (KSPS026W.e_tail_bound, KSPSU3), |E| ≤ R/w with
     R = √CE from the uniform entry tails (singleton finite sums), |a1|,|a2| ≤ B₀ (KSPSU4, singleton);
   * the uniform pointwise KSPS-015 bound |Δ - 2 cos θ| ≤ 1 is re-derived from KSPS015W.disc_identity:
     by KSPS026W.sec_apply, (2iλ)^{-N}(rf0 + rt1 - α rt0 - β rf1) = s (r00 + r11 - α r01 - β r10)
     = s (E00 + E11 - α(i a1 + E01) - β(-i a2 + E10)) (the e terms cancel), so |Δ - 2cos θ| ≤ K2/w;
   * the sign Δ = 2(-1)^n: body of KSPS026W.disc_sign_eventually per index, CI φ ≤ N·CIL;
   * the quadratic zero: KSPS026W.quad_zero_at.
   CORE/GLUE split (lane memory cap). Hypotheses (discharged in the glue KSPS025Uniform15):
     hloc = KSPS025U4.periodic_loc_uniform (exact body); hthr = KSPS016U.threshold_mono at B₀;
     hSb = KSPS016U.Sb_le; h13 = KSPS-013 integrated_riccati_vanishing; h14 = KSPS-014 WKB_monodromy_entries .2;
     hE = KSPS025U13.entries_tail_uniform (exact conclusion type). No hypothesis is added to any target head. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS025U14
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

/-! ### Real estimates -/

theorem div_of_wpow_le {N : ℕ} {w x R : ℝ} (hw : 1 ≤ w) (hx : 0 ≤ x) (h : w ^ (N + 1) * x ≤ R) :
    x ≤ R * (1 / w) := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  have h1 : w ≤ w ^ (N + 1) := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ (N + 1) := pow_le_pow_right₀ hw (by omega)
  have h2 : w * x ≤ R := le_trans (mul_le_mul_of_nonneg_right h1 hx) h
  rw [mul_one_div, le_div_iff₀ hw0]
  linarith

theorem q0_small (α β e E00 E10 a2 : ℂ) (S0 CIL R A u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hS0 : 0 ≤ S0) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hα : ‖α‖ ≤ S0 * u) (hβ : ‖β‖ ≤ S0 * u) (he : ‖e‖ ≤ CIL * u) (h00 : ‖E00‖ ≤ R * u)
    (h10 : ‖E10‖ ≤ R * u) (ha2 : ‖a2‖ ≤ A) :
    ‖α * β + (e + E00) - β * (-Complex.I * a2 + E10)‖ ≤ (S0 ^ 2 + CIL + R + S0 * (A + R)) * u := by
  have t1 : ‖-Complex.I * a2 + E10‖ ≤ ‖a2‖ + ‖E10‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  have t2 : ‖α * β + (e + E00) - β * (-Complex.I * a2 + E10)‖ ≤
      ‖α‖ * ‖β‖ + (‖e‖ + ‖E00‖) + ‖β‖ * (‖a2‖ + ‖E10‖) := by
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add (le_of_eq (norm_mul _ _)) (norm_add_le _ _))) ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left t1 (norm_nonneg _)
  have p1 : ‖α‖ * ‖β‖ ≤ (S0 * u) * (S0 * u) := mul_le_mul hα hβ (norm_nonneg _) (by positivity)
  have p2 : ‖β‖ * (‖a2‖ + ‖E10‖) ≤ (S0 * u) * (A + R * u) :=
    mul_le_mul hβ (add_le_add ha2 h10) (by positivity) (by positivity)
  have u2 : u * u ≤ u := by nlinarith
  have p3 : (S0 * u) * (S0 * u) ≤ S0 ^ 2 * u := by
    have := mul_le_mul_of_nonneg_left u2 (sq_nonneg S0)
    nlinarith
  have p4 : (S0 * u) * (A + R * u) ≤ S0 * (A + R) * u := by
    have : R * u ≤ R := by nlinarith
    have := mul_le_mul_of_nonneg_left (add_le_add_left this A) (mul_nonneg hS0 hu0)
    nlinarith
  nlinarith

theorem d15_small (Dinv s α β E00 E11 E01 E10 a1 a2 : ℂ) (S0 R A u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hS0 : 0 ≤ S0) (hR : 0 ≤ R) (hA : 0 ≤ A) (hD : ‖Dinv‖ ≤ 2) (hs : ‖s‖ = 1)
    (hα : ‖α‖ ≤ S0 * u) (hβ : ‖β‖ ≤ S0 * u) (h00 : ‖E00‖ ≤ R * u) (h11 : ‖E11‖ ≤ R * u)
    (h01 : ‖E01‖ ≤ R * u) (h10 : ‖E10‖ ≤ R * u) (ha1 : ‖a1‖ ≤ A) (ha2 : ‖a2‖ ≤ A) :
    ‖Dinv * (s * (E00 + E11 - α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10)))‖ ≤
      2 * (2 * R + 2 * S0 * (A + R)) * u := by
  have t1 : ‖Complex.I * a1 + E01‖ ≤ A + R := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    have : R * u ≤ R := by nlinarith
    linarith
  have t2 : ‖-Complex.I * a2 + E10‖ ≤ A + R := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    have : R * u ≤ R := by nlinarith
    linarith
  have t3 : ‖E00 + E11 - α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10)‖ ≤
      ‖E00‖ + ‖E11‖ + ‖α‖ * ‖Complex.I * a1 + E01‖ + ‖β‖ * ‖-Complex.I * a2 + E10‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (norm_add_le _ _) (le_of_eq (norm_mul _ _)))) (le_of_eq (norm_mul _ _)))
  have p1 : ‖α‖ * ‖Complex.I * a1 + E01‖ ≤ (S0 * u) * (A + R) :=
    mul_le_mul hα t1 (norm_nonneg _) (by positivity)
  have p2 : ‖β‖ * ‖-Complex.I * a2 + E10‖ ≤ (S0 * u) * (A + R) :=
    mul_le_mul hβ t2 (norm_nonneg _) (by positivity)
  have hin : ‖E00 + E11 - α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10)‖ ≤
      (2 * R + 2 * S0 * (A + R)) * u := by nlinarith
  rw [norm_mul, norm_mul, hs, one_mul]
  have h0 : 0 ≤ (2 * R + 2 * S0 * (A + R)) * u := by positivity
  calc ‖Dinv‖ * ‖E00 + E11 - α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10)‖
      ≤ 2 * ((2 * R + 2 * S0 * (A + R)) * u) := mul_le_mul hD hin (norm_nonneg _) (by norm_num)
    _ = 2 * (2 * R + 2 * S0 * (A + R)) * u := by ring

theorem CI_le {N : ℕ} (φ : SobolevC N) (CIL : ℝ)
    (hI : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 → ‖integralRiccatiLeft φ k‖ ≤ CIL) :
    NlsGge.ThirdConsultation.KSPS026W.CI φ ≤ (N : ℝ) * CIL := by
  unfold NlsGge.ThirdConsultation.KSPS026W.CI
  calc ∑ k ∈ Finset.Icc 1 N, ‖integralRiccatiLeft φ k‖ ≤ ∑ _k ∈ Finset.Icc 1 N, CIL :=
        Finset.sum_le_sum (fun k hk => hI k (Finset.mem_Icc.1 hk).1 (by have := (Finset.mem_Icc.1 hk).2; omega))
    _ = (N : ℝ) * CIL := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num

/-! ### One endpoint, one index -/

theorem side_at (N : ℕ) (φ : SobolevC N) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N (sobolevNorm N φ) lam.1 →
      monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam)
    (S0 CIL R A : ℝ) (hS : NlsGge.ThirdConsultation.KSPS016W.Sb φ ≤ S0)
    (hI : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 → ‖integralRiccatiLeft φ k‖ ≤ CIL)
    (hR0 : 0 ≤ R) (hA0 : 0 ≤ A)
    (n : ℤ)
    (hroot : NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) ^ 2 = 4)
    (hR : ∀ i j : Fin 2, indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ upper i j n‖ ≤ R)
    (ha1 : ‖physicalFourier (toPotPair φ).1 (-n)‖ ≤ A) (ha2 : ‖physicalFourier (toPotPair φ).2 n‖ ≤ A)
    (hn : ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (hK1 : S0 ^ 2 + CIL + R + S0 * (A + R) < indexWeight n)
    (hK2 : 2 * (2 * R + 2 * S0 * (A + R)) ≤ indexWeight n)
    (hK3 : a + (N : ℝ) * CIL ≤ indexWeight n) :
    ∃ hz : xi n ≠ 0, KSPSWKB.endpointQuadraticAt N φ n ⟨xi n, hz⟩
      (if hz : xi n = 0 then 0 else
        (KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1) ^ 2 -
          4 * KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 *
            KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 2 +
          4 * physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n) := by
  obtain ⟨hz, hthr, hX1, hwX, hD, hα, hβ⟩ :=
    NlsGge.ThirdConsultation.KSPS026W.tail_pack φ xi a ha hxi n hn
  have hw1 : 1 ≤ indexWeight n := NlsGge.ThirdConsultation.KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos hw1
  set u : ℝ := 1 / indexWeight n with hudef
  have hu0 : 0 ≤ u := by rw [hudef]; positivity
  have hu1 : u ≤ 1 := by rw [hudef, div_le_one hw0]; exact hw1
  have hX0 : 0 < 2 * ‖xi n‖ := lt_of_lt_of_le hw0 hwX
  have hS00 : 0 ≤ S0 := (NlsGge.ThirdConsultation.KSPS016W.Sb_nonneg φ).trans hS
  have hCIL0 : 0 ≤ CIL := (norm_nonneg _).trans (hI 1 le_rfl (by omega))
  -- |α|, |β| ≤ S0 / w
  have hab : ∀ x : ℂ, ‖x‖ ≤ NlsGge.ThirdConsultation.KSPS016W.Sb φ / (2 * ‖xi n‖) → ‖x‖ ≤ S0 * u := by
    intro x hx
    refine hx.trans ?_
    rw [hudef, mul_one_div]
    exact (div_le_div_of_nonneg_right hS hX0.le).trans (div_le_div_of_nonneg_left hS00 hw0 hwX)
  have hα' := hab _ hα
  have hβ' := hab _ hβ
  -- entry errors
  have hE : ∀ i j : Fin 2, ‖KSPSWKB.endpointEntryError N φ upper i j n‖ ≤ R * u := fun i j =>
    div_of_wpow_le hw1 (norm_nonneg _) (hR i j)
  -- the leading diagonal correction e
  have he : ‖integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)‖ ≤ CIL * u :=
    div_of_wpow_le hw1 (norm_nonneg _)
      ((NlsGge.ThirdConsultation.KSPS026W.e_tail_bound N _ _ _ hw0 hwX).trans (hI (N + 1) (by omega) le_rfl))
  -- decomposition of the scaled corrections (as in KSPS026W.endpoint_side_of)
  obtain ⟨e, hedef⟩ : ∃ e : ℂ, e = integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1) :=
    ⟨_, rfl⟩
  have q00 := NlsGge.ThirdConsultation.KSPS026W.entryError_eq φ upper xi hxe 0 0 n hz
  have q01 := NlsGge.ThirdConsultation.KSPS026W.entryError_eq φ upper xi hxe 0 1 n hz
  have q10 := NlsGge.ThirdConsultation.KSPS026W.entryError_eq φ upper xi hxe 1 0 n hz
  have q11 := NlsGge.ThirdConsultation.KSPS026W.entryError_eq φ upper xi hxe 1 1 n hz
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at q00 q01 q10 q11
  have s00 : KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 0 =
      e + KSPSWKB.endpointEntryError N φ upper 0 0 n := by rw [q00, hedef]; ring
  have s01 : KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 1 =
      Complex.I * physicalFourier (toPotPair φ).1 (-n) + KSPSWKB.endpointEntryError N φ upper 0 1 n := by
    rw [q01]; ring
  have s10 : KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 0 =
      -Complex.I * physicalFourier (toPotPair φ).2 n + KSPSWKB.endpointEntryError N φ upper 1 0 n := by
    rw [q10]; ring
  have s11 : KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 1 =
      -e + KSPSWKB.endpointEntryError N φ upper 1 1 n := by rw [q11, hedef]; ring
  rw [← hedef] at he
  -- the uniform pointwise KSPS-015 bound, from KSPS015W.disc_identity
  set lam : {z : ℂ // z ≠ 0} := ⟨xi n, hz⟩ with hlamdef
  set s : ℂ := (-1 : ℂ) ^ n with hsdef
  have hs1 : s = 1 ∨ s = -1 := NlsGge.ThirdConsultation.KSPS026W.sign_cases n
  have hss : s * s = 1 := by rcases hs1 with h | h <;> rw [h] <;> norm_num
  have hsn : ‖s‖ = 1 := by rw [hsdef, norm_zpow, norm_neg, norm_one, one_zpow]
  have hid := NlsGge.ThirdConsultation.KSPS015W.disc_identity φ lam h13 (h14 lam hthr) hD
  have hr : ∀ i j : Fin 2, KSPSWKB.scaledEndpointCorrection N φ n lam i j =
      s * ((2 * Complex.I * lam.1) ^ N)⁻¹ *
        (if j = 0 then NlsGge.ThirdConsultation.KSPS015W.rf φ lam i
         else NlsGge.ThirdConsultation.KSPS015W.rt φ lam i) :=
    fun i j => NlsGge.ThirdConsultation.KSPS026W.sec_apply φ n lam i j
  have hr00 := hr 0 0
  have hr01 := hr 0 1
  have hr10 := hr 1 0
  have hr11 := hr 1 1
  simp only [if_pos rfl, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, one_ne_zero, if_false] at hr00 hr01 hr10 hr11
  rw [if_pos trivial] at hr00 hr10
  have hkey : ((2 * Complex.I * lam.1) ^ N)⁻¹ *
      (NlsGge.ThirdConsultation.KSPS015W.rf φ lam 0 + NlsGge.ThirdConsultation.KSPS015W.rt φ lam 1 -
        KSPSWKB.alpha φ lam.1 0 * NlsGge.ThirdConsultation.KSPS015W.rt φ lam 0 -
        KSPSWKB.beta φ lam.1 0 * NlsGge.ThirdConsultation.KSPS015W.rf φ lam 1) =
      s * (KSPSWKB.endpointEntryError N φ upper 0 0 n + KSPSWKB.endpointEntryError N φ upper 1 1 n -
        KSPSWKB.alpha φ (xi n) 0 *
          (Complex.I * physicalFourier (toPotPair φ).1 (-n) + KSPSWKB.endpointEntryError N φ upper 0 1 n) -
        KSPSWKB.beta φ (xi n) 0 *
          (-Complex.I * physicalFourier (toPotPair φ).2 n + KSPSWKB.endpointEntryError N φ upper 1 0 n)) := by
    rw [← s01, ← s10]
    have e0 : KSPSWKB.endpointEntryError N φ upper 0 0 n + KSPSWKB.endpointEntryError N φ upper 1 1 n =
        KSPSWKB.scaledEndpointCorrection N φ n lam 0 0 + KSPSWKB.scaledEndpointCorrection N φ n lam 1 1 := by
      rw [hlamdef, s00, s11]; ring
    rw [e0, hr00, hr01, hr10, hr11]
    linear_combination (-(((2 * Complex.I * lam.1) ^ N)⁻¹ *
      (NlsGge.ThirdConsultation.KSPS015W.rf φ lam 0 + NlsGge.ThirdConsultation.KSPS015W.rt φ lam 1 -
        KSPSWKB.alpha φ lam.1 0 * NlsGge.ThirdConsultation.KSPS015W.rt φ lam 0 -
        KSPSWKB.beta φ lam.1 0 * NlsGge.ThirdConsultation.KSPS015W.rf φ lam 1))) * hss
  have hDinv := (NlsGge.ThirdConsultation.KSPS016W.dinv_facts φ (xi n) (indexWeight n) hX1 hthr hw0 hwX).1
  have hd15 : ‖NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) -
      2 * Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))‖ ≤ 1 := by
    have h1 : NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) -
        2 * Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n)) =
        (1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0)⁻¹ *
          (s * (KSPSWKB.endpointEntryError N φ upper 0 0 n + KSPSWKB.endpointEntryError N φ upper 1 1 n -
            KSPSWKB.alpha φ (xi n) 0 *
              (Complex.I * physicalFourier (toPotPair φ).1 (-n) + KSPSWKB.endpointEntryError N φ upper 0 1 n) -
            KSPSWKB.beta φ (xi n) 0 *
              (-Complex.I * physicalFourier (toPotPair φ).2 n + KSPSWKB.endpointEntryError N φ upper 1 0 n))) := by
      rw [← hkey]; exact hid
    rw [h1]
    refine (d15_small _ _ _ _ _ _ _ _ _ _ S0 R A u hu0 hu1 hS00 hR0 hA0 hDinv hsn hα' hβ'
      (hE 0 0) (hE 1 1) (hE 0 1) (hE 1 0) ha1 ha2).trans ?_
    rw [hudef, mul_one_div, div_le_one hw0]
    exact hK2
  -- the sign Δ(ξ_n) = 2 (-1)^n (body of KSPS026W.disc_sign_eventually, per index)
  have hsign : NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) = 2 * (-1 : ℂ) ^ n := by
    set t : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) - (n : ℂ) * (Real.pi : ℂ) with htdef
    have hCI := NlsGge.ThirdConsultation.KSPS026W.CI_nonneg φ
    have hwbig : a + NlsGge.ThirdConsultation.KSPS026W.CI φ ≤ indexWeight n := by
      have := CI_le φ CIL hI
      linarith
    have ht : ‖t‖ ≤ 1 := by
      have e : t = (xi n - (n : ℂ) * (Real.pi : ℂ)) + Complex.I * ∑ k ∈ Finset.Icc 1 N,
          ((2 * Complex.I * xi n) ^ k)⁻¹ * integralRiccatiLeft φ k := by
        rw [htdef, NlsGge.ThirdConsultation.KSPS015W.wkbPhase_eq]; ring
      have h2 : 1 ≤ 2 * ‖xi n‖ := by linarith
      have hs := NlsGge.ThirdConsultation.KSPS026W.phase_sum_le φ (xi n) h2
      have h3 : NlsGge.ThirdConsultation.KSPS026W.CI φ / (2 * ‖xi n‖) ≤
          NlsGge.ThirdConsultation.KSPS026W.CI φ / indexWeight n := div_le_div_of_nonneg_left hCI hw0 hwX
      have h4 : ‖t‖ ≤ a / indexWeight n + NlsGge.ThirdConsultation.KSPS026W.CI φ / indexWeight n := by
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add (hxi n) ?_)
        rw [norm_mul, Complex.norm_I, one_mul]
        exact hs.trans h3
      have h5 : a / indexWeight n + NlsGge.ThirdConsultation.KSPS026W.CI φ / indexWeight n =
          (a + NlsGge.ThirdConsultation.KSPS026W.CI φ) / indexWeight n := by ring
      rw [h5] at h4
      exact h4.trans ((div_le_one hw0).2 hwbig)
    have hcos : Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n)) =
        (-1 : ℂ) ^ n * Complex.cos t := by
      rw [← NlsGge.ThirdConsultation.KSPS026W.cos_int_mul_pi_add', htdef]; congr 1; ring
    have hct : ‖Complex.cos t - 1‖ ≤ 1 :=
      (NlsGge.ThirdConsultation.KSPS026W.norm_cos_sub_one_le' ht).trans (by nlinarith [norm_nonneg t])
    set D := NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) with hDdef
    have hdev : ‖D - 2 * s‖ ≤ 3 := by
      have e : D - 2 * s = (D - 2 * Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) +
          2 * s * (Complex.cos t - 1) := by rw [hcos]; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_ofNat, hsn]
      linarith
    have hfac : (D - 2 * s) * (D + 2 * s) = 0 := by
      linear_combination hroot - 4 * hss
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have e : D - 2 * s = -(4 * s) := by linear_combination h
      rw [e, norm_neg, norm_mul, hsn, Complex.norm_ofNat] at hdev
      norm_num at hdev
  refine ⟨hz, ?_⟩
  dsimp only [KSPSWKB.endpointQuadraticAt]
  refine ⟨?_, ?_, ?_⟩
  · rw [(NlsGge.ThirdConsultation.KSPS026W.abc_apply φ n (xi n) hz).1, s00, s10]
    intro h0
    have e1 : KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 +
        (e + KSPSWKB.endpointEntryError N φ upper 0 0 n) -
        KSPSWKB.beta φ (xi n) 0 *
          (-Complex.I * physicalFourier (toPotPair φ).2 n + KSPSWKB.endpointEntryError N φ upper 1 0 n) = 1 := by
      linear_combination h0
    have hQ := q0_small (KSPSWKB.alpha φ (xi n) 0) (KSPSWKB.beta φ (xi n) 0) e
      (KSPSWKB.endpointEntryError N φ upper 0 0 n) (KSPSWKB.endpointEntryError N φ upper 1 0 n)
      (physicalFourier (toPotPair φ).2 n) S0 CIL R A u hu0 hu1 hS00 hR0 hA0 hα' hβ' he (hE 0 0) (hE 1 0) ha2
    rw [e1, norm_one, hudef, mul_one_div, le_div_iff₀ hw0, one_mul] at hQ
    linarith
  · exact NlsGge.ThirdConsultation.KSPS026W.quad_zero_at φ n ⟨xi n, hz⟩ h13 (h14 _ hthr) hD hsign
  · rw [dif_neg hz]
    ring

/-! ### The uniform cutoff -/

theorem h26q_of (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (a : ℝ) (ha : 0 ≤ a)
    (hloc : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ n : ℤ,
      ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n ∧
      ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (T0 : ℝ) (hthr : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ) ≤ T0)
    (S0 : ℝ) (hSb : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → NlsGge.ThirdConsultation.KSPS016W.Sb φ ≤ S0)
    (h13 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N (sobolevNorm N φ) lam.1 →
        monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam)
    (hE : ∃ (M : ℕ) (CE : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (upper : Bool) (i j : Fin 2) (F : Finset ℤ), (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) *
          ‖NlsGge.ThirdConsultation.KSPSWKB.endpointEntryError N φ upper i j n‖) ^ 2 ≤ CE) :
    ∃ (M : ℕ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∃ hplus hminus : ℤ → ℂ, ∀ n : ℤ, (M : ℤ) ≤ |n| →
        NlsGge.ThirdConsultation.KSPSWKB.endpointQuadraticFormula N φ n hplus hminus := by
  obtain ⟨ME, CE, hCE⟩ := hE
  obtain ⟨CIL, hCIL0, hCIL⟩ := NlsGge.ThirdConsultation.KSPSU3.integralRiccatiLeft_uniform N hN B₀ hB₀
  set R : ℝ := Real.sqrt CE with hRdef
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  set S1 : ℝ := max S0 0 with hS1
  have hS10 : 0 ≤ S1 := le_max_right _ _
  set K : ℝ := (S1 ^ 2 + CIL + R + S1 * (B₀ + R)) + 2 * (2 * R + 2 * S1 * (B₀ + R)) + (a + (N : ℝ) * CIL) + 1
    with hKdef
  refine ⟨max ME (max (⌈a⌉₊ + ⌈T0⌉₊ + 1) ⌈K⌉₊), fun φ hφ => ?_⟩
  refine ⟨fun n => if hz : periodicPlus φ n = 0 then 0 else
      (KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hz⟩ 1) ^ 2 -
        4 * KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hz⟩ 0 *
          KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hz⟩ 2 +
        4 * physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n,
    fun n => if hz : periodicMinus φ n = 0 then 0 else
      (KSPSWKB.endpointQuadraticABC N φ n ⟨periodicMinus φ n, hz⟩ 1) ^ 2 -
        4 * KSPSWKB.endpointQuadraticABC N φ n ⟨periodicMinus φ n, hz⟩ 0 *
          KSPSWKB.endpointQuadraticABC N φ n ⟨periodicMinus φ n, hz⟩ 2 +
        4 * physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n, fun n hn => ?_⟩
  have hnE : (ME : ℤ) ≤ |n| := le_trans (by exact_mod_cast le_max_left _ _) hn
  have hnT : ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ)
      ≤ |n| := by
    have hc : ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ ≤ ⌈T0⌉₊ :=
      Nat.ceil_mono (hthr φ hφ)
    have h1 : ((⌈a⌉₊ + ⌈T0⌉₊ + 1 : ℕ) : ℤ) ≤ |n| :=
      le_trans (by exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)) hn
    push_cast at h1 ⊢
    omega
  have hnK : (⌈K⌉₊ : ℤ) ≤ |n| :=
    le_trans (by exact_mod_cast (le_max_right _ _).trans (le_max_right _ _)) hn
  have hKw : K ≤ indexWeight n := by
    have h1 : (⌈K⌉₊ : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hnK
    exact (Nat.le_ceil K).trans (h1.trans (NlsGge.ThirdConsultation.KSPS026W.abs_le_indexWeight n))
  have hS : NlsGge.ThirdConsultation.KSPS016W.Sb φ ≤ S1 := (hSb φ hφ).trans (le_max_left _ _)
  have hI : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 → ‖integralRiccatiLeft φ k‖ ≤ CIL := hCIL φ hφ
  -- the Fourier coefficients are ≤ B₀ (singleton finite sum)
  have hW := NlsGge.ThirdConsultation.KSPSU4.weighted_fourier_le N φ {n}
  simp only [Finset.sum_singleton] at hW
  have hs0 : 0 ≤ sobolevNorm N φ := by unfold sobolevNorm; exact Real.sqrt_nonneg _
  have hw1 : 1 ≤ indexWeight n := NlsGge.ThirdConsultation.KSPS015W.one_le_w n
  have hfa : ∀ x : ℝ, 0 ≤ x → (indexWeight n ^ N * x) ^ 2 ≤ sobolevNorm N φ ^ 2 → x ≤ B₀ := by
    intro x hx h
    have h1 : indexWeight n ^ N * x ≤ sobolevNorm N φ :=
      (abs_le_of_sq_le_sq' h hs0).2
    have h2 : x ≤ indexWeight n ^ N * x := le_mul_of_one_le_left hx (one_le_pow₀ hw1)
    linarith
  have ha1 : ‖physicalFourier (toPotPair φ).1 (-n)‖ ≤ B₀ :=
    hfa _ (norm_nonneg _) (by nlinarith [sq_nonneg (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).2 n‖)])
  have ha2 : ‖physicalFourier (toPotPair φ).2 n‖ ≤ B₀ :=
    hfa _ (norm_nonneg _) (by nlinarith [sq_nonneg (indexWeight n ^ N * ‖physicalFourier (toPotPair φ).1 (-n)‖)])
  -- the entry errors at n (singleton finite sum)
  have hR : ∀ (upper : Bool) (i j : Fin 2),
      indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ upper i j n‖ ≤ R := by
    intro upper i j
    have h := hCE φ hφ upper i j {n} (fun m hm => by rw [Finset.mem_singleton.1 hm]; exact hnE)
    rw [Finset.sum_singleton] at h
    exact (le_abs_self _).trans (Real.abs_le_sqrt h)
  have hroot := NlsGge.ThirdConsultation.KSPS026W.periodic_disc_sq φ n
  have hK1 : S1 ^ 2 + CIL + R + S1 * (B₀ + R) < indexWeight n := by
    have : 0 ≤ 2 * (2 * R + 2 * S1 * (B₀ + R)) := by positivity
    have : 0 ≤ a + (N : ℝ) * CIL := by positivity
    linarith
  have hK2 : 2 * (2 * R + 2 * S1 * (B₀ + R)) ≤ indexWeight n := by
    have : 0 ≤ S1 ^ 2 + CIL + R + S1 * (B₀ + R) := by positivity
    have : 0 ≤ a + (N : ℝ) * CIL := by positivity
    linarith
  have hK3 : a + (N : ℝ) * CIL ≤ indexWeight n := by
    have : 0 ≤ S1 ^ 2 + CIL + R + S1 * (B₀ + R) := by positivity
    have : 0 ≤ 2 * (2 * R + 2 * S1 * (B₀ + R)) := by positivity
    linarith
  obtain ⟨hp, hP⟩ := side_at N φ true (periodicPlus φ) (fun m => if_pos rfl) a ha
    (fun m => (hloc φ hφ m).1) (h13 φ hφ) (h14 φ hφ) S1 CIL R B₀ hS hI hR0 hB₀ n hroot.1 (hR true)
    ha1 ha2 hnT hK1 hK2 hK3
  obtain ⟨hm, hM⟩ := side_at N φ false (periodicMinus φ) (fun m => if_neg (by simp)) a ha
    (fun m => (hloc φ hφ m).2) (h13 φ hφ) (h14 φ hφ) S1 CIL R B₀ hS hI hR0 hB₀ n hroot.2 (hR false)
    ha1 ha2 hnT hK1 hK2 hK3
  exact ⟨hp, hm, hP, hM⟩

end
end NlsGge.ThirdConsultation.KSPS025U14
