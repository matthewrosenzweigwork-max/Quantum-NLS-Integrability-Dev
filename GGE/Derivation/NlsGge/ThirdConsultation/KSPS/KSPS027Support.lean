import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS025Support
import NlsGge.ThirdConsultation.KSPS.KSPS027Host

/- KSPS-027 SUPPORT (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS027Support.lean.
   Route (KST proof of Theorem 1.2/1.3, unordered complex endpoints; see KSPS027_ROUTE.md):
   (1) at lam+ (tail) the landed KSPS-026 quadratic gives Z := 2 q0 eta + q1 with Z^2 = q1^2 - 4 q0 q2 = -4 P + h+
       EXACTLY (P = hat phi1(-n) hat phi2(n), w^(2N+1) h+ in l1);
   (2) Z + 2 i (g(lam+) - n pi) = -2(u - i eps) + 2 delta0 u + (r00 - e1) - (r11 + e1) + det r - beta r10 + alpha r01
       (g(lam) = lam + phasePolynomial (N+1) (1/lam), u = eta - 1), so w^(N+1)|Z + 2i(g(lam+) - n pi)| <= C t_n;
   (3) with the KSPS-022 germ ls (g(ls) = n pi, |ls - spoly| <= CT/n^(N+2)) and lam+ = tau + gamma/2:
       g(lam+) - n pi - gamma/2 = (tau - ls) + (P(1/lam+) - P(1/ls)), controlled by the KSPS-025 midpoint expansion;
       hence Z = -i gamma + B' with w^(N+1)|B'| <= Cb_n in l2;
   (4) (gamma/2)^2 - P = (-h+ - 2 i gamma B' + B'^2)/4 =: H, w^(2N+1)|H| <= Hb_n in l1 (w^N |gamma| <= 40 t_n);
   (5) (gamma/2 - sqrt P)(gamma/2 + sqrt P) = H, so for the sign sigma minimizing |sigma gamma/2 - sqrt P| this is
       <= sqrt|H|; {lam-, lam+} = {tau + sigma gamma/2, tau - sigma gamma/2} identically; the errors
       eplus/minus = (tau - spoly) +- (sigma gamma/2 - sqrt P) are weighted l2 of order N + 1/2.
   No square-root branch continuity is used (only (Complex.sqrt P)^2 = P). The KSPS-020, KSPS-026 and KSPS-025
   head conclusions enter as explicit hypotheses of exactly their head types. Local defs are literal abbreviations. -/
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS027W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W
open NlsGge.ThirdConsultation.KSPS024W NlsGge.ThirdConsultation.KSPS025W

/-! ### Pure lemmas -/

theorem Z_alg (α β r00 r01 r10 r11 η ε L : ℂ) :
    2 * (-1 + α * β + r00 - β * r10) * η +
        (1 + (1 - r00) * (1 - r11) - α * β - (α - r10) * (β - r01)) +
        (2 * Complex.I * ε - 2 * L) =
      -2 * ((η - 1) - Complex.I * ε) + 2 * (α * β + r00 - β * r10) * (η - 1) +
        (r00 - L) - (r11 - (-L)) + (r00 * r11 - r01 * r10) - β * r10 + α * r01 := by
  ring

theorem Z_sq (q0 q1 q2 η : ℂ) (h : q0 * η ^ 2 + q1 * η + q2 = 0) :
    (2 * q0 * η + q1) ^ 2 = q1 ^ 2 - 4 * q0 * q2 := by
  linear_combination (4 * q0) * h

theorem Z_norm (α β r00 r01 r10 r11 ε L : ℂ) (R S w Ent : ℝ) (hw : 1 ≤ w) (hS : 0 ≤ S)
    (hR : ‖r00‖ + ‖r01‖ + ‖r10‖ + ‖r11‖ ≤ R) (hR4 : R ≤ 1 / 4)
    (hα : ‖α‖ ≤ S / w) (hβ : ‖β‖ ≤ S / w) (hβ4 : ‖β‖ ≤ 1 / 4)
    (hε : ‖ε‖ ≤ 10 * R) (hε1 : ‖ε‖ ≤ 1) (hu : ‖Complex.exp (Complex.I * ε) - 1‖ ≤ 5 * R)
    (hEnt : ‖r00 - L‖ + ‖r11 - (-L)‖ ≤ Ent) :
    ‖-2 * ((Complex.exp (Complex.I * ε) - 1) - Complex.I * ε) +
        2 * (α * β + r00 - β * r10) * (Complex.exp (Complex.I * ε) - 1) +
        (r00 - L) - (r11 - (-L)) + (r00 * r11 - r01 * r10) - β * r10 + α * r01‖ ≤
      215 * R ^ 2 + 4 * S * R / w + Ent := by
  have h00 := norm_nonneg r00
  have h01 := norm_nonneg r01
  have h10 := norm_nonneg r10
  have h11 := norm_nonneg r11
  have hR0 : 0 ≤ R := by linarith
  have hw0 : 0 < w := by linarith
  have hSw : 0 ≤ S / w := div_nonneg hS hw0.le
  set u : ℂ := Complex.exp (Complex.I * ε) - 1 with hudef
  -- |u - i eps| <= |eps|^2
  have hIe : ‖Complex.I * ε‖ = ‖ε‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hρ : ‖u - Complex.I * ε‖ ≤ ‖ε‖ ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := Complex.I * ε) (by rw [hIe]; exact hε1)
    rw [hIe] at h
    rw [hudef]; exact h
  have t1 : ‖-2 * (u - Complex.I * ε)‖ ≤ 200 * R ^ 2 := by
    rw [norm_mul, norm_neg, Complex.norm_ofNat]
    have : ‖ε‖ ^ 2 ≤ (10 * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hε 2
    nlinarith
  have hαβ : ‖α * β‖ ≤ S / w * (1 / 4) := by
    rw [norm_mul]; exact mul_le_mul hα hβ4 (norm_nonneg _) hSw
  have hβr : ‖β * r10‖ ≤ S / w * ‖r10‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right hβ h10
  have hαr : ‖α * r01‖ ≤ S / w * ‖r01‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right hα h01
  have hβr' : ‖β * r10‖ ≤ ‖r10‖ / 4 := by
    rw [norm_mul]; nlinarith [norm_nonneg β]
  have hδ : ‖α * β + r00 - β * r10‖ ≤ S / w * (1 / 4) + 5 / 4 * R := by
    have := norm_sub_le (α * β + r00) (β * r10)
    have := norm_add_le (α * β) r00
    linarith
  have t2 : ‖2 * (α * β + r00 - β * r10) * u‖ ≤ 5 / 2 * (S / w * R) + 25 / 2 * R ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have hu0 := norm_nonneg u
    have h6 : ‖α * β + r00 - β * r10‖ * ‖u‖ ≤ (S / w * (1 / 4) + 5 / 4 * R) * (5 * R) :=
      mul_le_mul hδ hu (norm_nonneg _) (by positivity)
    nlinarith
  have hp1 : ‖r00 * r11‖ ≤ R * R := by
    rw [norm_mul]; exact mul_le_mul (by linarith) (by linarith) h11 hR0
  have hp2 : ‖r01 * r10‖ ≤ R * R := by
    rw [norm_mul]; exact mul_le_mul (by linarith) (by linarith) h10 hR0
  have t3 : ‖r00 * r11 - r01 * r10‖ ≤ 2 * R ^ 2 := by
    have := norm_sub_le (r00 * r11) (r01 * r10)
    nlinarith
  have t4 : ‖β * r10‖ + ‖α * r01‖ ≤ S / w * R := by
    have : S / w * ‖r10‖ + S / w * ‖r01‖ ≤ S / w * R := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hSw
    linarith
  have hsum := norm_add_le (-2 * (u - Complex.I * ε) + 2 * (α * β + r00 - β * r10) * u +
      (r00 - L) - (r11 - (-L)) + (r00 * r11 - r01 * r10) - β * r10) (α * r01)
  have hs2 := norm_sub_le (-2 * (u - Complex.I * ε) + 2 * (α * β + r00 - β * r10) * u +
      (r00 - L) - (r11 - (-L)) + (r00 * r11 - r01 * r10)) (β * r10)
  have hs3 := norm_add_le (-2 * (u - Complex.I * ε) + 2 * (α * β + r00 - β * r10) * u +
      (r00 - L) - (r11 - (-L))) (r00 * r11 - r01 * r10)
  have hs4 := norm_sub_le (-2 * (u - Complex.I * ε) + 2 * (α * β + r00 - β * r10) * u +
      (r00 - L)) (r11 - (-L))
  have hs5 := norm_add_le (-2 * (u - Complex.I * ε) + 2 * (α * β + r00 - β * r10) * u) (r00 - L)
  have hs6 := norm_add_le (-2 * (u - Complex.I * ε)) (2 * (α * β + r00 - β * r10) * u)
  have e : 4 * S * R / w = 4 * (S / w * R) := by ring
  rw [e]
  have p1 : 0 ≤ S / w * R := mul_nonneg hSw hR0
  have p2 : 0 ≤ R ^ 2 := sq_nonneg R
  linarith

theorem sign_choice (x s H : ℂ) (h : x ^ 2 - s ^ 2 = H) :
    ‖x - s‖ ≤ Real.sqrt ‖H‖ ∨ ‖x + s‖ ≤ Real.sqrt ‖H‖ := by
  have hp : ‖x - s‖ * ‖x + s‖ = ‖H‖ := by
    rw [← norm_mul, ← h]
    congr 1
    ring
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  have hq := Real.sqrt_nonneg ‖H‖
  have hsq := Real.sq_sqrt (norm_nonneg H)
  nlinarith [mul_lt_mul'' h1 h2 hq hq]

theorem sqrt_sq' (a : ℂ) : Complex.sqrt a ^ 2 = a := by
  unfold Complex.sqrt
  exact Complex.cpow_ofNat_inv_pow a 2

/-! ### One endpoint: the completed square -/

/-- The numerical facts at one endpoint (tail). -/
theorem side_core (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ 1 / 4) (hz : xi n ≠ 0)
    (hq : KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) ^ 2 +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 2 = 0) :
    ∃ R : ℝ, 0 ≤ R ∧ R ≤ 1 / 4 ∧ indexWeight n ^ N * R ≤ tP N φ n ∧
      indexWeight n ^ (N + 1) * Eent N φ upper n ≤ tP N φ n ∧
      ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 0‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 1‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 0‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 1‖ ≤ R ∧
      ‖KSPSWKB.alpha φ (xi n) 0‖ ≤ KSPS016W.Sb φ / indexWeight n ∧
      ‖KSPSWKB.beta φ (xi n) 0‖ ≤ KSPS016W.Sb φ / indexWeight n ∧
      ‖KSPSWKB.beta φ (xi n) 0‖ ≤ 1 / 4 ∧
      ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 10 * R ∧
      ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 / 2 ∧
      ‖Complex.exp (Complex.I * (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) -
          (n : ℂ) * (Real.pi : ℂ))) - 1‖ ≤ 5 * R ∧
      ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 0 -
          integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 1 -
          -(integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1))‖ ≤ Eent N φ upper n := by
  obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a _ ha xi hxi n h1
  obtain ⟨-, hXS, -⟩ := KSPS015W.tail_facts a _ ha xi hxi n h2
  have hX0 : 0 < ‖xi n‖ := by linarith
  have hthr : WKBThreshold N (sobolevNorm N φ) (xi n) := ⟨hX0, hXT⟩
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  obtain ⟨-, -, hα, hβ⟩ := KSPS016W.dinv_facts φ (xi n) (indexWeight n) hX1 hthr hw0 hwX
  have hS0 := KSPS016W.Sb_nonneg φ
  have hq4 : KSPS016W.Sb φ / (2 * ‖xi n‖) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hSw : KSPS016W.Sb φ / (2 * ‖xi n‖) ≤ KSPS016W.Sb φ / indexWeight n :=
    div_le_div_of_nonneg_left hS0 hw0 hwX
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := (KSPS016W.tail_nat a _ n h1).1
  obtain ⟨-, -, hF1, hF2⟩ := KSPS016W.fourier_facts φ n hn1R
  set r := KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ with hrdef
  have hE : ∀ i j : Fin 2, KSPSWKB.endpointEntryError N φ upper i j n =
      r i j - (!![integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1),
            Complex.I * physicalFourier (toPotPair φ).1 (-n);
            -Complex.I * physicalFourier (toPotPair φ).2 n,
            -integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)] :
              Matrix (Fin 2) (Fin 2) ℂ) i j :=
    fun i j => NlsGge.ThirdConsultation.KSPS026W.entryError_eq φ upper xi hxe i j n hz
  have hY : ‖integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)‖ =
      ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hent : ∀ (i j : Fin 2) (lead : ℂ),
      KSPSWKB.endpointEntryError N φ upper i j n = r i j - lead →
      ‖r i j‖ ≤ ‖lead‖ + ‖KSPSWKB.endpointEntryError N φ upper i j n‖ := by
    intro i j lead h
    have e : r i j = lead + KSPSWKB.endpointEntryError N φ upper i j n := by rw [h]; ring
    rw [e]; exact norm_add_le _ _
  set L : ℂ := integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1) with hLdef
  have hE00 := hE 0 0
  have hE11 := hE 1 1
  have e00 := hent 0 0 L hE00
  have e01 := hent 0 1 (Complex.I * physicalFourier (toPotPair φ).1 (-n)) (hE 0 1)
  have e10 := hent 1 0 (-Complex.I * physicalFourier (toPotPair φ).2 n) (hE 1 0)
  have e11 := hent 1 1 (-integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)) hE11
  have hENT : ‖r 0 0 - L‖ + ‖r 1 1 - (-L)‖ ≤ Eent N φ upper n := by
    have f00 : r 0 0 - L = KSPSWKB.endpointEntryError N φ upper 0 0 n := by rw [hE00]; rfl
    have f11 : r 1 1 - (-L) = KSPSWKB.endpointEntryError N φ upper 1 1 n := by
      rw [hE11]
      congr 1
      rw [hLdef, ← neg_div]
      rfl
    rw [f00, f11]
    unfold Eent
    linarith [norm_nonneg (KSPSWKB.endpointEntryError N φ upper 0 1 n),
      norm_nonneg (KSPSWKB.endpointEntryError N φ upper 1 0 n)]
  rw [hLdef, hY] at e00
  rw [neg_div, norm_neg, hY] at e11
  rw [norm_mul, Complex.norm_I, one_mul] at e01
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul] at e10
  set R : ℝ := ‖r 0 0‖ + ‖r 0 1‖ + ‖r 1 0‖ + ‖r 1 1‖ with hRdef
  have hEu : Eent N φ upper n ≤ Eent N φ true n + Eent N φ false n := by
    have := Eent_nonneg N φ true n
    have := Eent_nonneg N φ false n
    cases upper <;> linarith
  have hRs : R ≤ Eent N φ upper n +
      (‖physicalFourier (toPotPair φ).1 (-n)‖ + ‖physicalFourier (toPotPair φ).2 n‖) +
      2 * ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) := by
    have h2c : 2 * ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) =
        ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) +
          ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) := by ring
    rw [hRdef, h2c]; unfold Eent; linarith
  have hEw : indexWeight n ^ (N + 1) * Eent N φ upper n ≤ tP N φ n := by
    have h9 : indexWeight n ^ (N + 1) * Eent N φ upper n ≤
        indexWeight n ^ (N + 1) * (Eent N φ true n + Eent N φ false n) :=
      mul_le_mul_of_nonneg_left hEu (pow_nonneg hw0.le _)
    unfold tP
    have := norm_nonneg (physicalFourier (iteratedDerivative N φ.1) (-n))
    have := norm_nonneg (physicalFourier (iteratedDerivative N φ.2) n)
    have : 0 ≤ 2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) := by positivity
    linarith
  have hRw : indexWeight n ^ N * R ≤ tP N φ n := by
    have h8 := tau_pure N (indexWeight n) ‖xi n‖ (Eent N φ upper n) _ _ _ _ ‖integralRiccatiLeft φ (N + 1)‖ R
      hw1 hwX (Eent_nonneg N φ upper n) (norm_nonneg _) hF1 hF2 hRs
    have h9 : indexWeight n ^ (N + 1) * Eent N φ upper n ≤
        indexWeight n ^ (N + 1) * (Eent N φ true n + Eent N φ false n) :=
      mul_le_mul_of_nonneg_left hEu (pow_nonneg hw0.le _)
    unfold tP
    linarith
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hwN : 1 ≤ indexWeight n ^ N := one_le_pow₀ hw1
  have hR4 : R ≤ 1 / 4 := by
    have := le_mul_of_one_le_left hR0 hwN
    linarith
  -- the root bound and eps
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have heta : (-1 : ℂ) ^ n * Complex.exp (Complex.I * θ) = Complex.exp (Complex.I * ε) := eta_eq θ n
  rw [heta] at hq
  have hq' : (-1 + KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 + r 0 0 -
        KSPSWKB.beta φ (xi n) 0 * r 1 0) * ((Complex.exp (Complex.I * ε) - 1) + 1) ^ 2 +
      (1 + (1 - r 0 0) * (1 - r 1 1) - KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 -
        (KSPSWKB.alpha φ (xi n) 0 - r 1 0) * (KSPSWKB.beta φ (xi n) 0 - r 0 1)) *
          ((Complex.exp (Complex.I * ε) - 1) + 1) +
      (-1 + KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 + r 1 1 -
        KSPSWKB.alpha φ (xi n) 0 * r 0 1) = 0 := by
    rw [sub_add_cancel]
    exact hq
  have hu := quad_root_bound _ _ _ _ _ _ _ R le_rfl hR4 (hα.trans hq4) (hβ.trans hq4) hq'
  have hε : ‖ε‖ ≤ 1 / 2 := by
    have := phase_small φ (xi n) n (indexWeight n) a hw0 hX1 hwX (hxi n)
    have h7 : (a + Jsum φ) / indexWeight n ≤ 1 / 2 := by
      rw [div_le_iff₀ hw0]
      linarith
    unfold Jsum at h7
    rw [hεdef, hθ]
    linarith
  have hεu := eps_le_two_exp ε hε
  have h10 : ‖ε‖ ≤ 10 * R := by linarith
  exact ⟨R, hR0, hR4, hRw, hEw, le_rfl, hα.trans hSw, hβ.trans hSw, hβ.trans hq4, h10, hε, hu, hENT⟩

/-- Z := 2 q0 eta + q1 at an endpoint, versus -2 i (g(lam) - n pi). -/
theorem side_Z (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ 1 / 4) (hz : xi n ≠ 0)
    (hq : KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) ^ 2 +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 2 = 0) :
    indexWeight n ^ (N + 1) *
      ‖(2 * KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) +
          KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1) +
        2 * Complex.I * (xi n + KSPSRiccati.phasePolynomial φ (N + 1) (xi n)⁻¹ -
          (n : ℂ) * (Real.pi : ℂ))‖ ≤
      (216 + 4 * KSPS016W.Sb φ) * tP N φ n := by
  obtain ⟨R, hR0, hR4, hRw, hEw, hR, hα, hβ, hβ4, h10, hε, hu, hENT⟩ :=
    side_core N hN φ a ha upper xi hxe hxi n h1 h2 h4 h5 hz hq
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hS0 := KSPS016W.Sb_nonneg φ
  set r := KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ with hrdef
  set L : ℂ := integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1) with hLdef
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have heta : (-1 : ℂ) ^ n * Complex.exp (Complex.I * θ) = Complex.exp (Complex.I * ε) := eta_eq θ n
  rw [heta]
  -- the phase identity g(lam) - n pi = eps + i e1
  have hg : xi n + KSPSRiccati.phasePolynomial φ (N + 1) (xi n)⁻¹ - (n : ℂ) * (Real.pi : ℂ) =
      ε + Complex.I * (((2 * Complex.I * xi n) ^ (N + 1))⁻¹ * integralRiccatiLeft φ (N + 1)) := by
    rw [phase_poly_eq φ (xi n), ← hθ, hεdef]
    ring
  have hgL : 2 * Complex.I * (xi n + KSPSRiccati.phasePolynomial φ (N + 1) (xi n)⁻¹ -
      (n : ℂ) * (Real.pi : ℂ)) = 2 * Complex.I * ε - 2 * L := by
    rw [hg, hLdef, div_eq_mul_inv]
    linear_combination (2 * (((2 * Complex.I * xi n) ^ (N + 1))⁻¹ *
      integralRiccatiLeft φ (N + 1))) * Complex.I_sq
  have hq0 : KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 =
      -1 + KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 + r 0 0 -
        KSPSWKB.beta φ (xi n) 0 * r 1 0 := rfl
  have hq1 : KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1 =
      1 + (1 - r 0 0) * (1 - r 1 1) - KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 -
        (KSPSWKB.alpha φ (xi n) 0 - r 1 0) * (KSPSWKB.beta φ (xi n) 0 - r 0 1) := rfl
  rw [hgL, hq0, hq1, Z_alg]
  have hZ := Z_norm (KSPSWKB.alpha φ (xi n) 0) (KSPSWKB.beta φ (xi n) 0) (r 0 0) (r 0 1) (r 1 0) (r 1 1)
    ε L R (KSPS016W.Sb φ) (indexWeight n) (Eent N φ upper n) hw1 hS0 hR hR4
    hα hβ hβ4 h10 (by linarith) hu hENT
  have hwp : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
  refine (mul_le_mul_of_nonneg_left hZ hwp).trans ?_
  -- weights
  have hRR : indexWeight n ^ (N + 1) * R ^ 2 ≤ tP N φ n := by
    have hw2 : indexWeight n ^ (N + 1) ≤ indexWeight n ^ (2 * N) := pow_le_pow_right₀ hw1 (by omega)
    have h6 : indexWeight n ^ (N + 1) * R ^ 2 ≤ (indexWeight n ^ N * R) ^ 2 := by
      have e : (indexWeight n ^ N * R) ^ 2 = indexWeight n ^ (2 * N) * R ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)
    have h7 : (indexWeight n ^ N * R) ^ 2 ≤ tP N φ n ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (pow_nonneg hw0.le _) hR0) hRw 2
    have htP0 : 0 ≤ tP N φ n := le_trans (mul_nonneg (pow_nonneg hw0.le _) hR0) hRw
    have h8 : tP N φ n ^ 2 ≤ tP N φ n := by
      have h9 := mul_le_mul_of_nonneg_left h5 htP0
      rw [sq]; linarith
    exact h6.trans (h7.trans h8)
  have hRl : indexWeight n ^ (N + 1) * (4 * KSPS016W.Sb φ * R / indexWeight n) =
      4 * KSPS016W.Sb φ * (indexWeight n ^ N * R) := by
    rw [pow_succ]; field_simp
  have e : indexWeight n ^ (N + 1) * (215 * R ^ 2 + 4 * KSPS016W.Sb φ * R / indexWeight n +
      Eent N φ upper n) = 215 * (indexWeight n ^ (N + 1) * R ^ 2) +
        indexWeight n ^ (N + 1) * (4 * KSPS016W.Sb φ * R / indexWeight n) +
        indexWeight n ^ (N + 1) * Eent N φ upper n := by ring
  rw [e, hRl]
  have h11 : 4 * KSPS016W.Sb φ * (indexWeight n ^ N * R) ≤ 4 * KSPS016W.Sb φ * tP N φ n :=
    mul_le_mul_of_nonneg_left hRw (by linarith)
  linarith

/-! ### Bounding sequences (literal abbreviations) -/

def Db (N : ℕ) (φ : SobolevC N) (CT : ℝ) (n : ℤ) : ℝ :=
  3 / 2 * (indexWeight n ^ (N + 1) * ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖) +
    3 / 2 * (CT * 2 ^ (N + 2) * (1 / indexWeight n)) + 80 * Lsum φ * tP N φ n

def Cb (N : ℕ) (φ : SobolevC N) (CT : ℝ) (n : ℤ) : ℝ :=
  (216 + 4 * KSPS016W.Sb φ) * tP N φ n + 2 * Db N φ CT n

def Hb (N : ℕ) (φ : SobolevC N) (CT : ℝ) (hp : ℤ → ℂ) (n : ℤ) : ℝ :=
  (indexWeight n ^ (2 * N + 1) * ‖hp n‖ + Cb N φ CT n ^ 2 + 80 * tP N φ n * Cb N φ CT n) / 4

theorem tP_nonneg (N : ℕ) (φ : SobolevC N) (n : ℤ) : 0 ≤ tP N φ n := by
  have hw0 : 0 ≤ indexWeight n := le_trans zero_le_one (KSPS015W.one_le_w n)
  unfold tP
  have h1 : 0 ≤ indexWeight n ^ (N + 1) * (Eent N φ true n + Eent N φ false n) :=
    mul_nonneg (pow_nonneg hw0 _) (add_nonneg (Eent_nonneg N φ true n) (Eent_nonneg N φ false n))
  have h2 : 0 ≤ 2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) :=
    mul_nonneg (by positivity) (div_nonneg zero_le_one hw0)
  have := norm_nonneg (physicalFourier (iteratedDerivative N φ.1) (-n))
  have := norm_nonneg (physicalFourier (iteratedDerivative N φ.2) n)
  linarith

theorem wpow_ratio (N : ℕ) (w ν : ℝ) (hw : 1 ≤ w) (hν : 1 ≤ ν) (hwν : w ≤ 2 * ν) :
    w ^ (N + 1) * (1 / ν ^ (N + 2)) ≤ 2 ^ (N + 2) * (1 / w) := by
  have hw0 : 0 < w := by linarith
  have hν0 : 0 < ν := by linarith
  have h2 : w ^ (N + 1) ≤ (2 * ν) ^ (N + 1) := pow_le_pow_left₀ hw0.le hwν _
  have h3 : w ^ (N + 1) * (1 / ν ^ (N + 2)) ≤ (2 * ν) ^ (N + 1) * (1 / ν ^ (N + 2)) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have h4 : (2 * ν) ^ (N + 1) * (1 / ν ^ (N + 2)) = 2 ^ (N + 1) * (1 / ν) := by
    rw [mul_pow, pow_succ ν (N + 1)]
    field_simp
  have h5 : 1 / ν ≤ 2 * (1 / w) := by
    rw [div_le_iff₀ hν0]
    have : 2 * (1 / w) * ν = 2 * ν / w := by ring
    rw [this, le_div_iff₀ hw0]
    linarith
  have h6 : 2 ^ (N + 1) * (1 / ν) ≤ 2 ^ (N + 1) * (2 * (1 / w)) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have h7 : (2 : ℝ) ^ (N + 1) * (2 * (1 / w)) = 2 ^ (N + 2) * (1 / w) := by ring
  linarith

/-! ### The radicand relation at one index -/

theorem tail027 (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxp : ∀ n : ℤ, ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hxm : ∀ n : ℤ, ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hplus hminus : ℤ → ℂ) (ζ : ℂ → ℂ) (CT : ℝ) (hCT : 0 ≤ CT) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ 1 / 4)
    (hL : 2 * Lp φ ≤ |(n : ℝ)| ^ 2)
    (hL' : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2)
    (hne : (Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹ ≠ 0)
    (heq : ζ (n : ℂ)⁻¹ + KSPSRiccati.phasePolynomial φ (N + 1)
      ((n : ℂ)⁻¹ / ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹)) = 0)
    (hsmall : ‖ζ (n : ℂ)⁻¹‖ ≤ 1)
    (htay : ‖ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
        KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k‖ ≤ CT * ‖(n : ℂ)⁻¹‖ ^ (N + 2))
    (hqf : KSPSWKB.endpointQuadraticFormula N φ n hplus hminus) :
    indexWeight n ^ (2 * N + 1) *
      ‖((periodicPlus φ n - periodicMinus φ n) / 2) ^ 2 -
        physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n‖ ≤
      Hb N φ CT hplus n := by
  have hg := gap_bound N hN φ a ha hxp hxm hplus hminus n h1 h2 h4 h5 hL hqf
  obtain ⟨hp, hm, hqp, -⟩ := hqf
  obtain ⟨-, hqp2, hqp3⟩ := hqp
  have hZ := side_Z N hN φ a ha true (periodicPlus φ) (fun _ => rfl) hxp n h1 h2 h4 h5 hp hqp2
  set Z : ℂ := 2 * KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 0 *
      ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicPlus φ n))) +
      KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 1 with hZdef
  have hZsq : Z ^ 2 = -4 * physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n +
      hplus n := (Z_sq _ _ _ _ hqp2).trans hqp3
  -- basic facts
  obtain ⟨hn1R, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hν0 : 0 < |(n : ℝ)| := by linarith
  have hwν : indexWeight n ≤ 2 * |(n : ℝ)| := KSPS015W.w_le_two n hn1R
  have htP0 := tP_nonneg N φ n
  have hnC : (n : ℂ) ≠ 0 := by
    intro h0
    have : (n : ℝ) = 0 := by exact_mod_cast h0
    rw [this, abs_zero] at hn1R
    linarith
  -- the exact germ solution
  set ls : ℂ := (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ with hls
  have hgs := lamStar_eq φ ζ n hnC hne heq
  rw [← hls] at hgs
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hpi := Real.pi_gt_three
  have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
  have hpν : |(n : ℝ)| ≤ ‖periodicPlus φ n‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (periodicPlus φ n)
    rw [norm_sub_rev, hnpi] at h7
    have h8 : a / indexWeight n ≤ a := div_le_self ha hw1
    have h9 := hxp n
    linarith
  have hlsν : |(n : ℝ)| ≤ ‖ls‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) ls
    rw [norm_sub_rev, hnpi] at h7
    have h8 : ls - (n : ℂ) * (Real.pi : ℂ) = ζ (n : ℂ)⁻¹ := by rw [hls]; ring
    rw [h8] at h7
    linarith
  have hp0 : periodicPlus φ n ≠ 0 := hp
  have hls0 : ls ≠ 0 := by intro h0; rw [h0, norm_zero] at hlsν; linarith
  have hpi1 : ‖(periodicPlus φ n)⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hlsi : ‖ls⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hinv : ‖(periodicPlus φ n)⁻¹ - ls⁻¹‖ ≤ ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    rw [inv_sub_inv hp0 hls0, norm_div, norm_mul, norm_sub_rev]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hν0 2)
    rw [pow_two]
    exact mul_le_mul hpν hlsν hν0.le (norm_nonneg _)
  have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  have hΔp : ‖KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹‖ ≤ Lsum φ * ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    refine (phasePoly_lip φ (N + 1) _ _ hpi1 hlsi).trans ?_
    unfold Lsum
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hinv (Finset.sum_nonneg (fun k _ => by positivity))
  -- D := g(lam+) - n pi - gamma/2 = (tau - ls) + (P(1/lam+) - P(1/ls))
  set γ : ℂ := periodicPlus φ n - periodicMinus φ n with hγdef
  set τ : ℂ := NlsGge.ThirdConsultation.KSPS.midpoint φ n with hτdef
  have hτp : periodicPlus φ n = τ + γ / 2 := by
    rw [hτdef, hγdef]; unfold NlsGge.ThirdConsultation.KSPS.midpoint; ring
  set D : ℂ := periodicPlus φ n + KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ -
      (n : ℂ) * (Real.pi : ℂ) - γ / 2 with hDdef
  have hDe : D = (τ - ls) + (KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) := by
    rw [hDdef]
    have := hτp
    linear_combination this + hgs
  have hT0 : ‖ls - spectralPolynomial φ n‖ ≤ CT * (1 / |(n : ℝ)| ^ (N + 2)) := by
    rw [spoly_eq, hls]
    have e : (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ - ((n : ℂ) * (Real.pi : ℂ) +
        ∑ k ∈ Finset.Icc 1 (N + 1), KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k) =
        ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
          KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k := by ring
    rw [e]
    refine htay.trans (le_of_eq ?_)
    rw [norm_inv, Complex.norm_intCast, inv_pow]
    ring
  have hτls : ‖τ - ls‖ ≤ ‖τ - spectralPolynomial φ n‖ + CT * (1 / |(n : ℝ)| ^ (N + 2)) := by
    have e : τ - ls = (τ - spectralPolynomial φ n) - (ls - spectralPolynomial φ n) := by ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith)
  have hpls : ‖periodicPlus φ n - ls‖ ≤ ‖τ - ls‖ + ‖γ‖ / 2 := by
    rw [hτp]
    have e : τ + γ / 2 - ls = (τ - ls) + γ / 2 := by ring
    rw [e]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_div, Complex.norm_ofNat]
  have hLn : Lsum φ / |(n : ℝ)| ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (pow_pos hν0 2)]; linarith
  have hDn : ‖D‖ ≤ 3 / 2 * ‖τ - ls‖ + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
    rw [hDe]
    refine (norm_add_le _ _).trans ?_
    have h7 : Lsum φ * ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 ≤
        Lsum φ / |(n : ℝ)| ^ 2 * ‖τ - ls‖ + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
      have e1 : Lsum φ * ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 =
          Lsum φ / |(n : ℝ)| ^ 2 * ‖periodicPlus φ n - ls‖ := by ring
      have e2 : Lsum φ / |(n : ℝ)| ^ 2 * (‖τ - ls‖ + ‖γ‖ / 2) =
          Lsum φ / |(n : ℝ)| ^ 2 * ‖τ - ls‖ + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
        ring
      rw [e1, ← e2]
      exact mul_le_mul_of_nonneg_left hpls (by positivity)
    have h8 : Lsum φ / |(n : ℝ)| ^ 2 * ‖τ - ls‖ ≤ 1 / 2 * ‖τ - ls‖ :=
      mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
    linarith
  -- weighted D
  have hwp : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
  have hD : indexWeight n ^ (N + 1) * ‖D‖ ≤ Db N φ CT n := by
    have hr := wpow_ratio N (indexWeight n) |(n : ℝ)| hw1 hn1R hwν
    have hγw : indexWeight n ^ (N + 1) * (Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) ≤ 80 * Lsum φ * tP N φ n := by
      have hwn2 : indexWeight n ^ 2 ≤ 4 * |(n : ℝ)| ^ 2 :=
        calc indexWeight n ^ 2 ≤ (2 * |(n : ℝ)|) ^ 2 := pow_le_pow_left₀ hw0.le hwν 2
          _ = 4 * |(n : ℝ)| ^ 2 := by ring
      have e : indexWeight n ^ (N + 1) * (Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) =
          Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) * (indexWeight n / |(n : ℝ)| ^ 2) := by
        ring
      have h7 : indexWeight n / |(n : ℝ)| ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (pow_pos hν0 2)]
        have := le_self_pow₀ hw1 (by norm_num : (2 : ℕ) ≠ 0)
        linarith
      rw [e]
      have h8 : 0 ≤ Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) :=
        mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hw0.le _) (norm_nonneg _))
      calc Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) * (indexWeight n / |(n : ℝ)| ^ 2)
          ≤ Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) * 4 := mul_le_mul_of_nonneg_left h7 h8
        _ ≤ Lsum φ / 2 * (40 * tP N φ n) * 4 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by linarith)) (by norm_num)
        _ = 80 * Lsum φ * tP N φ n := by ring
    have hDn' : ‖D‖ ≤ 3 / 2 * (‖τ - spectralPolynomial φ n‖ + CT * (1 / |(n : ℝ)| ^ (N + 2))) +
        Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
      have := mul_le_mul_of_nonneg_left hτls (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith
    have h9 := mul_le_mul_of_nonneg_left hDn' hwp
    have h11 : indexWeight n ^ (N + 1) * (CT * (1 / |(n : ℝ)| ^ (N + 2))) ≤
        CT * 2 ^ (N + 2) * (1 / indexWeight n) := by
      have := mul_le_mul_of_nonneg_left hr hCT
      calc indexWeight n ^ (N + 1) * (CT * (1 / |(n : ℝ)| ^ (N + 2)))
          = CT * (indexWeight n ^ (N + 1) * (1 / |(n : ℝ)| ^ (N + 2))) := by ring
        _ ≤ CT * (2 ^ (N + 2) * (1 / indexWeight n)) := this
        _ = CT * 2 ^ (N + 2) * (1 / indexWeight n) := by ring
    have e : indexWeight n ^ (N + 1) * (3 / 2 * (‖τ - spectralPolynomial φ n‖ +
        CT * (1 / |(n : ℝ)| ^ (N + 2))) + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) =
        3 / 2 * (indexWeight n ^ (N + 1) * ‖τ - spectralPolynomial φ n‖) +
        3 / 2 * (indexWeight n ^ (N + 1) * (CT * (1 / |(n : ℝ)| ^ (N + 2)))) +
        indexWeight n ^ (N + 1) * (Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) := by ring
    unfold Db
    rw [← hτdef]
    linarith
  -- B' := Z + i gamma
  have hB : indexWeight n ^ (N + 1) * ‖Z + Complex.I * γ‖ ≤ Cb N φ CT n := by
    have e : Z + Complex.I * γ = (Z + 2 * Complex.I * (periodicPlus φ n +
        KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ))) -
        2 * Complex.I * D := by rw [hDdef]; ring
    rw [e]
    have h7 := norm_sub_le (Z + 2 * Complex.I * (periodicPlus φ n +
        KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ)))
      (2 * Complex.I * D)
    have h8 : ‖2 * Complex.I * D‖ = 2 * ‖D‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    rw [h8] at h7
    have h9 := mul_le_mul_of_nonneg_left h7 hwp
    rw [mul_add] at h9
    unfold Cb
    linarith
  -- the radicand relation
  set B : ℂ := Z + Complex.I * γ with hBdef
  have hH : 4 * ((γ / 2) ^ 2 - physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n) =
      -hplus n + B ^ 2 - 2 * Complex.I * γ * B := by
    have hZB : Z = B - Complex.I * γ := by rw [hBdef]; ring
    rw [hZB] at hZsq
    linear_combination (-1 : ℂ) * hZsq + γ ^ 2 * Complex.I_sq
  have hHn : ‖(γ / 2) ^ 2 - physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n‖ ≤
      (‖hplus n‖ + ‖B‖ ^ 2 + 2 * (‖γ‖ * ‖B‖)) / 4 := by
    have e : (γ / 2) ^ 2 - physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n =
        (-hplus n + B ^ 2 - 2 * Complex.I * γ * B) / 4 := by rw [← hH]; ring
    rw [e, norm_div, Complex.norm_ofNat]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have h7 := norm_sub_le (-hplus n + B ^ 2) (2 * Complex.I * γ * B)
    have h8 := norm_add_le (-hplus n) (B ^ 2)
    rw [norm_neg, norm_pow] at h8
    have h9 : ‖2 * Complex.I * γ * B‖ = 2 * (‖γ‖ * ‖B‖) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat]; ring
    rw [h9] at h7
    linarith
  have hw2 : indexWeight n ^ (2 * N + 1) ≤ indexWeight n ^ (N + 1) * indexWeight n ^ (N + 1) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hw1 (by omega)
  have hw3 : indexWeight n ^ (2 * N + 1) = indexWeight n ^ N * indexWeight n ^ (N + 1) := by
    rw [← pow_add]; congr 1; omega
  have hB0 : 0 ≤ indexWeight n ^ (N + 1) * ‖B‖ := mul_nonneg hwp (norm_nonneg _)
  have hBB : indexWeight n ^ (2 * N + 1) * ‖B‖ ^ 2 ≤ Cb N φ CT n ^ 2 := by
    have h7 : indexWeight n ^ (2 * N + 1) * ‖B‖ ^ 2 ≤ (indexWeight n ^ (N + 1) * ‖B‖) ^ 2 := by
      have e : (indexWeight n ^ (N + 1) * ‖B‖) ^ 2 =
          (indexWeight n ^ (N + 1) * indexWeight n ^ (N + 1)) * ‖B‖ ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)
    exact h7.trans (pow_le_pow_left₀ hB0 hB 2)
  have hγB : indexWeight n ^ (2 * N + 1) * (‖γ‖ * ‖B‖) ≤ 40 * tP N φ n * Cb N φ CT n := by
    rw [hw3]
    have e : indexWeight n ^ N * indexWeight n ^ (N + 1) * (‖γ‖ * ‖B‖) =
        (indexWeight n ^ N * ‖γ‖) * (indexWeight n ^ (N + 1) * ‖B‖) := by ring
    rw [e]
    exact mul_le_mul hg hB hB0 (by linarith)
  have hwq : 0 ≤ indexWeight n ^ (2 * N + 1) := pow_nonneg hw0.le _
  have h12 := mul_le_mul_of_nonneg_left hHn hwq
  have e : indexWeight n ^ (2 * N + 1) * ((‖hplus n‖ + ‖B‖ ^ 2 + 2 * (‖γ‖ * ‖B‖)) / 4) =
      (indexWeight n ^ (2 * N + 1) * ‖hplus n‖ + indexWeight n ^ (2 * N + 1) * ‖B‖ ^ 2 +
        2 * (indexWeight n ^ (2 * N + 1) * (‖γ‖ * ‖B‖))) / 4 := by ring
  rw [e] at h12
  unfold Hb
  linarith


/-! ### The unordered pair -/

def sqP {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  Complex.sqrt (physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n)

def halfGap {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  (periodicPlus φ n - periodicMinus φ n) / 2

def sgn027 {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  if ‖halfGap φ n - sqP φ n‖ ≤ ‖halfGap φ n + sqP φ n‖ then 1 else -1

def eplus027 {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.ThirdConsultation.KSPS.midpoint φ n + sgn027 φ n * halfGap φ n - spectralPolynomial φ n - sqP φ n

def eminus027 {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.ThirdConsultation.KSPS.midpoint φ n - sgn027 φ n * halfGap φ n - spectralPolynomial φ n + sqP φ n

theorem sel_bound (x s : ℂ) :
    ‖(if ‖x - s‖ ≤ ‖x + s‖ then (1 : ℂ) else -1) * x - s‖ ≤ Real.sqrt ‖x ^ 2 - s ^ 2‖ := by
  rcases sign_choice x s _ rfl with h | h
  · split_ifs with hc
    · rw [one_mul]; exact h
    · push_neg at hc
      have e : (-1 : ℂ) * x - s = -(x + s) := by ring
      rw [e, norm_neg]; linarith
  · split_ifs with hc
    · rw [one_mul]; linarith
    · have e : (-1 : ℂ) * x - s = -(x + s) := by ring
      rw [e, norm_neg]; exact h

theorem pair_eq {N : ℕ} (φ : SobolevC N) (n : ℤ) :
    ({periodicMinus φ n, periodicPlus φ n} : Multiset ℂ) =
      {spectralPolynomial φ n + sqP φ n + eplus027 φ n,
       spectralPolynomial φ n - sqP φ n + eminus027 φ n} := by
  have e1 : spectralPolynomial φ n + sqP φ n + eplus027 φ n =
      NlsGge.ThirdConsultation.KSPS.midpoint φ n + sgn027 φ n * halfGap φ n := by
    unfold eplus027; ring
  have e2 : spectralPolynomial φ n - sqP φ n + eminus027 φ n =
      NlsGge.ThirdConsultation.KSPS.midpoint φ n - sgn027 φ n * halfGap φ n := by
    unfold eminus027; ring
  have hp : NlsGge.ThirdConsultation.KSPS.midpoint φ n + halfGap φ n = periodicPlus φ n := by
    unfold NlsGge.ThirdConsultation.KSPS.midpoint halfGap; ring
  have hm : NlsGge.ThirdConsultation.KSPS.midpoint φ n - halfGap φ n = periodicMinus φ n := by
    unfold NlsGge.ThirdConsultation.KSPS.midpoint halfGap; ring
  rw [e1, e2]
  unfold sgn027
  split_ifs
  · rw [one_mul, hp, hm]
    exact Multiset.pair_comm _ _
  · have hp' : NlsGge.ThirdConsultation.KSPS.midpoint φ n + -1 * halfGap φ n = periodicMinus φ n := by
      rw [← hm]; ring
    have hm' : NlsGge.ThirdConsultation.KSPS.midpoint φ n - -1 * halfGap φ n = periodicPlus φ n := by
      rw [← hp]; ring
    rw [hp', hm']

theorem err_pure (N : ℕ) (W : ℝ) (hW : 1 ≤ W) (x y H : ℂ) (Hb : ℝ)
    (hy : ‖y‖ ≤ Real.sqrt ‖H‖) (hH : W ^ (2 * N + 1) * ‖H‖ ≤ Hb) :
    W ^ (2 * N + 1) * ‖x + y‖ ^ 2 ≤ 2 * (W ^ (N + 1) * ‖x‖) ^ 2 + 2 * Hb := by
  have hW0 : 0 ≤ W := by linarith
  have hy2 : ‖y‖ ^ 2 ≤ ‖H‖ := by
    have := pow_le_pow_left₀ (norm_nonneg y) hy 2
    rwa [Real.sq_sqrt (norm_nonneg _)] at this
  have hxy : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖H‖ := by
    have h1 := norm_add_le x y
    have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hwp : 0 ≤ W ^ (2 * N + 1) := pow_nonneg hW0 _
  have h3 := mul_le_mul_of_nonneg_left hxy hwp
  have hw2 : W ^ (2 * N + 1) ≤ W ^ (N + 1) * W ^ (N + 1) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hW (by omega)
  have h4 : W ^ (2 * N + 1) * ‖x‖ ^ 2 ≤ (W ^ (N + 1) * ‖x‖) ^ 2 := by
    have e : (W ^ (N + 1) * ‖x‖) ^ 2 = (W ^ (N + 1) * W ^ (N + 1)) * ‖x‖ ^ 2 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)
  have e : W ^ (2 * N + 1) * (2 * ‖x‖ ^ 2 + 2 * ‖H‖) =
      2 * (W ^ (2 * N + 1) * ‖x‖ ^ 2) + 2 * (W ^ (2 * N + 1) * ‖H‖) := by ring
  rw [e] at h3
  linarith

theorem wl2_half_of (N : ℕ) (e : ℤ → ℂ) (b : ℤ → ℝ) (hb : Summable b)
    (h : ∀ᶠ n : ℤ in cofinite, indexWeight n ^ (2 * N + 1) * ‖e n‖ ^ 2 ≤ b n) :
    WeightedL2Error ((N : ℝ) + (1 / 2 : ℝ)) e := by
  unfold WeightedL2Error
  have key : ∀ n : ℤ, indexWeight n ^ (2 * ((N : ℝ) + (1 / 2 : ℝ))) * ‖e n‖ ^ 2 =
      indexWeight n ^ (2 * N + 1) * ‖e n‖ ^ 2 := by
    intro n
    rw [show (2 * ((N : ℝ) + (1 / 2 : ℝ))) = ((2 * N + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp_rw [key]
  refine Summable.of_norm_bounded_eventually hb ?_
  filter_upwards [h] with n hn
  have h0 : 0 ≤ indexWeight n ^ (2 * N + 1) * ‖e n‖ ^ 2 :=
    mul_nonneg (pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact hn

/-! ### The unordered endpoint expansion (conditional on the KSPS-020/026 head types and the KSPS-025 head) -/

theorem complex_periodic_endpoint_pair_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (h20 : ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
        ∀ n : ℤ, N ≤ n.natAbs →
          max ‖periodicPlus φ n-(n:ℂ)*Real.pi‖
              ‖periodicMinus φ n-(n:ℂ)*Real.pi‖ ≤
            C/(n.natAbs:ℝ))
    (h26 : EndpointQuadraticWKB N φ)
    (h25 : WeightedL2Error (N+1)
      (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n)) :
    UnorderedEndpointExpansion N φ (N + (1/2:ℝ)) := by
  unfold UnorderedEndpointExpansion
  obtain ⟨a, ha, hloc⟩ := NlsGge.ThirdConsultation.KSPS026W.periodic_localization_of hN φ h20
  obtain ⟨hent, hplus, hminus, hsp, -, hevq⟩ := h26
  rw [Filter.cocompact_eq_cofinite] at hevq
  have htP := tP_sq_summable N φ hent
  have hs : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hs, wl2_iff] at h25
  -- the inverse-phase germ (K = N + 1)
  obtain ⟨ζ, hζa, hζ0, hev, hcoef⟩ :=
    NlsGge.ThirdConsultation.KSPS023T.spectralCoefficient_consistent φ (N + 1) le_rfl
  obtain ⟨CT0, hCT0⟩ := (hζa.hasFPowerSeriesAt.isBigO_sub_partialSum_pow (N + 2)).bound
  set CT : ℝ := max CT0 0 with hCTdef
  have hCT : 0 ≤ CT := le_max_right _ _
  have htay0 : ∀ᶠ y : ℂ in 𝓝 0, ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
      KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤ CT * ‖y‖ ^ (N + 2) := by
    filter_upwards [hCT0] with y hy
    rw [zero_add, partialSum_eq φ ζ hζ0 hcoef y, norm_pow, norm_norm] at hy
    exact hy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsmall0 : ∀ᶠ y : ℂ in 𝓝 0, ‖ζ y‖ ≤ 1 := by
    have h := hζa.continuousAt.eventually (Metric.closedBall_mem_nhds (ζ 0) one_pos)
    filter_upwards [h] with y hy
    rw [dist_eq_norm, hζ0, sub_zero] at hy
    exact hy
  have et := tendsto_inv_int.eventually htay0
  have es := tendsto_inv_int.eventually hsmall0
  have ee := tendsto_inv_int.eventually hev
  -- summability of the bounds
  have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  have hDb : Summable (fun n : ℤ => Db N φ CT n ^ 2) := by
    have h := KSPS015W.sq_summable_add (KSPS015W.sq_summable_add
      (KSPS015W.sq_summable_mul_left (3 / 2) h25)
      (KSPS015W.sq_summable_mul_left (3 / 2)
        (KSPS015W.sq_summable_mul_left (CT * 2 ^ (N + 2)) KSPS016W.sq_summable_inv_w)))
      (KSPS015W.sq_summable_mul_left (80 * Lsum φ) htP)
    refine h.congr (fun n => ?_)
    unfold Db
    ring
  have hCb : Summable (fun n : ℤ => Cb N φ CT n ^ 2) := by
    have h := KSPS015W.sq_summable_add
      (KSPS015W.sq_summable_mul_left (216 + 4 * KSPS016W.Sb φ) htP)
      (KSPS015W.sq_summable_mul_left 2 hDb)
    refine h.congr (fun n => ?_)
    unfold Cb
    ring
  have hCb0 : ∀ n, 0 ≤ Cb N φ CT n := by
    intro n
    have t0 := tP_nonneg N φ n
    have S0 := KSPS016W.Sb_nonneg φ
    have hw0 : 0 ≤ indexWeight n := le_trans zero_le_one (KSPS015W.one_le_w n)
    unfold Cb Db
    have a1 : 0 ≤ (216 + 4 * KSPS016W.Sb φ) * tP N φ n := mul_nonneg (by linarith) t0
    have a2 : 0 ≤ indexWeight n ^ (N + 1) *
        ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖ :=
      mul_nonneg (pow_nonneg hw0 _) (norm_nonneg _)
    have a3 : 0 ≤ CT * 2 ^ (N + 2) * (1 / indexWeight n) :=
      mul_nonneg (mul_nonneg hCT (by positivity)) (div_nonneg zero_le_one hw0)
    have a4 : 0 ≤ 80 * Lsum φ * tP N φ n := mul_nonneg (mul_nonneg (by norm_num) hL0) t0
    linarith
  have hHb : Summable (fun n : ℤ => Hb N φ CT hplus n) := by
    have hprod : Summable (fun n : ℤ => 80 * tP N φ n * Cb N φ CT n) := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        ((htP.add hCb).mul_left 40)
      · exact mul_nonneg (mul_nonneg (by norm_num) (tP_nonneg N φ n)) (hCb0 n)
      · nlinarith [sq_nonneg (tP N φ n - Cb N φ CT n)]
    have h := ((hsp.add hCb).add hprod).div_const 4
    refine h.congr (fun n => ?_)
    unfold Hb
    ring
  have hb : Summable (fun n : ℤ => 2 * (indexWeight n ^ (N + 1) *
      ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖) ^ 2 +
      2 * Hb N φ CT hplus n) :=
    (h25.mul_left 2).add (hHb.mul_left 2)
  -- the tail facts
  have e1 := KSPS015W.eventually_natAbs
    (⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)
  have e2 := KSPS015W.eventually_natAbs (⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1)
  have e3 := KSPS015W.eventually_natAbs 1
  have e4 := eventually_w_ge (2 * (a + Jsum φ))
  have e5 := eventually_le_of_sq (tP N φ) htP (1 / 4) (by norm_num)
  have e6 := KSPS015W.eventually_natAbs ⌈2 * Lp φ⌉₊
  have e7 := KSPS015W.eventually_natAbs ⌈2 * Lsum φ⌉₊
  have hsq : ∀ n : ℤ, (1 : ℤ) ≤ |n| → ∀ M : ℝ, ((⌈M⌉₊ : ℤ) ≤ |n|) → M ≤ |(n : ℝ)| ^ 2 := by
    intro n g3 M g6
    have h7 : ((⌈M⌉₊ : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g6
    rw [Int.cast_abs] at h7
    push_cast at h7
    have h8 := Nat.le_ceil M
    have h9 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g3
      rw [Int.cast_abs] at this
      simpa using this
    nlinarith
  have hev27 : ∀ᶠ n : ℤ in cofinite,
      indexWeight n ^ (2 * N + 1) * ‖halfGap φ n ^ 2 - sqP φ n ^ 2‖ ≤ Hb N φ CT hplus n := by
    filter_upwards [e1, e2, e3, e4, e5, e6, e7, et, es, ee, hevq] with
      n g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
    have ht := tail027 N hN φ a ha (fun m => (hloc m).1) (fun m => (hloc m).2) hplus hminus ζ CT hCT n
      g1 g2 g4 g5 (hsq n (by exact_mod_cast g3) _ g6) (hsq n (by exact_mod_cast g3) _ g7) g10.1 g10.2 g9 g8 g11
    unfold halfGap
    rw [sqP, sqrt_sq']
    exact ht
  have hsel : ∀ n : ℤ, ‖sgn027 φ n * halfGap φ n - sqP φ n‖ ≤
      Real.sqrt ‖halfGap φ n ^ 2 - sqP φ n ^ 2‖ := fun n => sel_bound _ _
  refine ⟨eplus027 φ, eminus027 φ, ?_, ?_, Filter.Eventually.of_forall (fun n => pair_eq φ n)⟩
  · refine wl2_half_of N _ _ hb ?_
    filter_upwards [hev27] with n hn
    have e : eplus027 φ n = (NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) +
        (sgn027 φ n * halfGap φ n - sqP φ n) := by unfold eplus027; ring
    rw [e]
    exact err_pure N _ (KSPS015W.one_le_w n) _ _ _ _ (hsel n) hn
  · refine wl2_half_of N _ _ hb ?_
    filter_upwards [hev27] with n hn
    have e : eminus027 φ n = (NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) +
        -(sgn027 φ n * halfGap φ n - sqP φ n) := by unfold eminus027; ring
    rw [e]
    exact err_pure N _ (KSPS015W.one_le_w n) _ _ _ _ (by rw [norm_neg]; exact hsel n) hn


end
end NlsGge.ThirdConsultation.KSPS027W
