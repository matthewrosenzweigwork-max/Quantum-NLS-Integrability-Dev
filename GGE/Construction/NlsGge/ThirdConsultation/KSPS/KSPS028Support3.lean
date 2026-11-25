import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS025Host
import NlsGge.ThirdConsultation.KSPS.KSPS026Host
import NlsGge.ThirdConsultation.KSPS.KSPS029Host
import NlsGge.ThirdConsultation.KSPS.KSPS028Support1

                                                                                                                    
                                                                                                    
                                                                          
                                                                                                                   
                                                                                                                     
                                                                                                                   
                                                                                                                
                                                                       
                                            
                                                                                                                
                       
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS028C
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPS028P

theorem entryError_eq' {N : ℕ} (φ : SobolevC N) (upper : Bool) (xi : ℤ → ℂ)
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

def Mc {N : ℕ} (φ : SobolevC N) (S : ℝ) : ℝ :=
  4 * ‖integralRiccatiLeft φ (N + 1)‖ * S + (1 + S) ^ 2 + 8 * S ^ 2 + 4 * (1 + S) + 12

def Qc (N : ℕ) (φ : SobolevC N) (S t c : ℝ) (n : ℤ) : ℝ :=
  indexWeight n ^ (N + 1) * ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖ +
    2 * (t + c) + Real.sqrt ((Mc φ S * t + c ^ 2) / 2)

theorem tail028_core (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (n : ℤ) (hp : periodicPlus φ n ≠ 0)
    (h : ℂ) (B : ℂ) (R S t c : ℝ) (hS0 : 0 ≤ S) (htP0 : 0 ≤ t) (h5 : t ≤ 1 / 4) (hCb0 : 0 ≤ c)
    (hw1 : 1 ≤ indexWeight n) (hwX : indexWeight n ≤ 2 * ‖periodicPlus φ n‖)
    (hqp3 : (KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 1) ^ 2 -
      4 * KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 0 *
        KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 2 =
      -4 * physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n + h)
    (hR : ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ 0 0‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ 0 1‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ 1 0‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ 1 1‖ ≤ R)
    (hRw : indexWeight n ^ N * R ≤ t)
    (hEw : indexWeight n ^ (N + 1) * (‖KSPSWKB.endpointEntryError N φ true 0 0 n‖ +
        ‖KSPSWKB.endpointEntryError N φ true 0 1 n‖ + ‖KSPSWKB.endpointEntryError N φ true 1 0 n‖ +
        ‖KSPSWKB.endpointEntryError N φ true 1 1 n‖) ≤ t)
    (hα : ‖KSPSWKB.alpha φ (periodicPlus φ n) 0‖ ≤ S / indexWeight n)
    (hβ : ‖KSPSWKB.beta φ (periodicPlus φ n) 0‖ ≤ S / indexWeight n)
    (hB : indexWeight n ^ (N + 1) * ‖B‖ ≤ c)
    (hH : 4 * (((periodicPlus φ n - periodicMinus φ n) / 2) ^ 2 -
        physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n) =
      -h + B ^ 2 - 2 * Complex.I * (periodicPlus φ n - periodicMinus φ n) * B)
    (hre : ∃ U L : ℝ, L ≤ U ∧ periodicPlus φ n = (U : ℂ) ∧ periodicMinus φ n = (L : ℂ))
    (hst : physicalFourier (toPotPair φ).2 n = star (physicalFourier (toPotPair φ).1 (-n))) :
    indexWeight n ^ (N + 1) * ‖periodicPlus φ n - spectralPolynomial φ n -
        (‖physicalFourier (toPotPair φ).1 (-n)‖ : ℂ)‖ ≤ Qc N φ S t c n ∧
    indexWeight n ^ (N + 1) * ‖periodicMinus φ n - spectralPolynomial φ n +
        (‖physicalFourier (toPotPair φ).1 (-n)‖ : ℂ)‖ ≤ Qc N φ S t c n := by
  have hw0 : 0 < indexWeight n := by linarith
  -- entries at lam+
  set r := KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ with hrdef
  set IL : ℂ := integralRiccatiLeft φ (N + 1) with hILdef
  set Y : ℂ := (2 * Complex.I * periodicPlus φ n) ^ (N + 1) with hYdef
  set a1 : ℂ := physicalFourier (toPotPair φ).1 (-n) with ha1
  set a2 : ℂ := physicalFourier (toPotPair φ).2 n with ha2
  set E00 := KSPSWKB.endpointEntryError N φ true 0 0 n with hE00
  set E01 := KSPSWKB.endpointEntryError N φ true 0 1 n with hE01
  set E10 := KSPSWKB.endpointEntryError N φ true 1 0 n with hE10
  set E11 := KSPSWKB.endpointEntryError N φ true 1 1 n with hE11
  set α := KSPSWKB.alpha φ (periodicPlus φ n) 0 with hαdef
  set β := KSPSWKB.beta φ (periodicPlus φ n) 0 with hβdef
  have q00 : E00 = r 0 0 - IL / Y :=
    entryError_eq' φ true (periodicPlus φ) (fun _ => rfl) 0 0 n hp
  have q01 : E01 = r 0 1 - Complex.I * a1 :=
    entryError_eq' φ true (periodicPlus φ) (fun _ => rfl) 0 1 n hp
  have q10 : E10 = r 1 0 - -Complex.I * a2 :=
    entryError_eq' φ true (periodicPlus φ) (fun _ => rfl) 1 0 n hp
  have q11 : E11 = r 1 1 - -IL / Y :=
    entryError_eq' φ true (periodicPlus φ) (fun _ => rfl) 1 1 n hp
  have hr00 : r 0 0 = IL / Y + E00 := by rw [q00]; ring
  have hr01 : r 0 1 = Complex.I * a1 + E01 := by rw [q01]; ring
  have hr10 : r 1 0 = -Complex.I * a2 + E10 := by rw [q10]; ring
  have hr11 : r 1 1 = -(IL / Y) + E11 := by rw [q11]; ring
  -- the radicand at lam+ in entry form
  have hq0 : KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 0 =
      -1 + α * β + r 0 0 - β * r 1 0 := rfl
  have hq1 : KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 1 =
      1 + (1 - r 0 0) * (1 - r 1 1) - α * β - (α - r 1 0) * (β - r 0 1) := rfl
  have hq2 : KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 2 =
      -1 + α * β + r 1 1 - α * r 0 1 := rfl
  have hq3 := hqp3
  rw [hq0, hq1, hq2, hr00, hr01, hr10, hr11] at hq3
  have key := rad_identity' (IL / Y) a1 a2 E00 E01 E10 E11 α β
  have hh : h = 4 * ((IL / Y) * (α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10))) +
      (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) *
        (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) +
      4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
      4 * ((α * β) * ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
      2 * (((IL / Y + E00) - β * (-Complex.I * a2 + E10) + ((-(IL / Y) + E11) - α * (Complex.I * a1 + E01))) *
        ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) +
      ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) *
        ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) := by
    linear_combination key - hq3
  -- the sharper radicand estimate
  rw [hr00, hr01, hr10, hr11] at hR
  have he : indexWeight n ^ (N + 1) * ‖IL / Y‖ ≤ ‖IL‖ := by
    rw [hYdef]; exact e_bound N IL (periodicPlus φ n) (indexWeight n) hw0 hwX
  have hsplit := rad_split N hN (indexWeight n) hw1 (IL / Y) a1 a2 E00 E01 E10 E11 α β R
    S t ‖IL‖ (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) hS0 htP0 h5 hR hRw le_rfl hEw he hα hβ
  set RHS : ℂ := 4 * ((IL / Y) * (α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10))) +
      (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) *
        (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) +
      4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
      4 * ((α * β) * ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
      2 * (((IL / Y + E00) - β * (-Complex.I * a2 + E10) + ((-(IL / Y) + E11) - α * (Complex.I * a1 + E01))) *
        ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) +
      ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) *
        ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) with hRHS
  -- real-type facts
  obtain ⟨U, L, hLU, hPU, hML⟩ := hre
  have ha2n : ‖a2‖ = ‖a1‖ := by rw [hst, norm_star]
  have hP : a1 * a2 = ((‖a1‖ ^ 2 : ℝ) : ℂ) := by
    rw [hst, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set s : ℝ := ‖a1‖ with hsdef
  have hs0 : 0 ≤ s := norm_nonneg _
  set x : ℝ := (U - L) / 2 with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; linarith
  have hγ : periodicPlus φ n - periodicMinus φ n = ((2 * x : ℝ) : ℂ) := by
    rw [hPU, hML, hxdef]; push_cast; ring
  have hHx : ((periodicPlus φ n - periodicMinus φ n) / 2) ^ 2 - a1 * a2 = ((x ^ 2 - s ^ 2 : ℝ) : ℂ) := by
    rw [hγ, hP]; push_cast; ring
  rw [hHx, hγ, hh] at hH
  -- |x^2 - s^2| <= Hg + (x + s) K
  set bad : ℂ := 4 * (-Complex.I * (a1 * E10) + Complex.I * (a2 * E01)) with hbad
  have hbadn : ‖bad‖ ≤ 4 * (s * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖)) := by
    rw [hbad, norm_mul, Complex.norm_ofNat]
    have h7 := norm_add_le (-Complex.I * (a1 * E10)) (Complex.I * (a2 * E01))
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul] at h7
    rw [ha2n] at h7
    have h8 : s * ‖E10‖ + s * ‖E01‖ ≤ s * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) := by
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ hs0
      linarith [norm_nonneg E00, norm_nonneg E11]
    have e9 : ‖a1‖ = s := rfl
    rw [e9] at h7
    linarith
  have hxs : |x ^ 2 - s ^ 2| ≤ (‖RHS - bad‖ + ‖B‖ ^ 2) / 4 + (x + s) * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) := by
    have h7 : (4 : ℝ) * |x ^ 2 - s ^ 2| = ‖-RHS + B ^ 2 - 2 * Complex.I * ((2 * x : ℝ) : ℂ) * B‖ := by
      rw [← hH, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    have h8 : -RHS + B ^ 2 - 2 * Complex.I * ((2 * x : ℝ) : ℂ) * B =
        -(RHS - bad) - bad + B ^ 2 - 2 * Complex.I * ((2 * x : ℝ) : ℂ) * B := by ring
    have h9 : ‖2 * Complex.I * ((2 * x : ℝ) : ℂ) * B‖ = 4 * x * ‖B‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * x)]
      ring
    have s1 := norm_sub_le (-(RHS - bad) - bad + B ^ 2) (2 * Complex.I * ((2 * x : ℝ) : ℂ) * B)
    have s2 := norm_add_le (-(RHS - bad) - bad) (B ^ 2)
    have s3 := norm_sub_le (-(RHS - bad)) bad
    rw [norm_neg] at s3
    rw [norm_pow] at s2
    rw [h9] at s1
    rw [h8] at h7
    have hEnt0 : 0 ≤ (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) := by positivity
    have h10 : s * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) ≤ (x + s) * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) :=
      mul_le_mul_of_nonneg_right (by linarith) hEnt0
    have h11 : x * ‖B‖ ≤ (x + s) * ‖B‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have e1 : (x + s) * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) = (x + s) * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + (x + s) * ‖B‖ := by ring
    linarith
  have hd := d_bound x s ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4) ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) hx0 hs0
    (by positivity) (by positivity) hxs
  -- weighted
  have hW1 : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
  have hK : indexWeight n ^ (N + 1) * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) ≤ t + c := by
    rw [mul_add]; linarith
  have hHg : indexWeight n ^ (N + 1) * Real.sqrt (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4)) ≤
      Real.sqrt ((Mc φ S * t + c ^ 2) / 2) := by
    have e1 : indexWeight n ^ (N + 1) * Real.sqrt (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4)) =
        Real.sqrt ((indexWeight n ^ (N + 1)) ^ 2 * (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4))) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW1]
    rw [e1]
    apply Real.sqrt_le_sqrt
    have h7 : (indexWeight n ^ (N + 1) * ‖B‖) ^ 2 ≤ c ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hW1 (norm_nonneg _)) hB 2
    have h8 : (indexWeight n ^ (N + 1)) ^ 2 * ‖RHS - bad‖ ≤ Mc φ S * t := by
      unfold Mc; exact hsplit
    have e2 : (indexWeight n ^ (N + 1)) ^ 2 * (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4)) =
        ((indexWeight n ^ (N + 1)) ^ 2 * ‖RHS - bad‖ + (indexWeight n ^ (N + 1) * ‖B‖) ^ 2) / 2 := by ring
    rw [e2]
    linarith
  have hwd : indexWeight n ^ (N + 1) * |x - s| ≤ 2 * (t + c) +
      Real.sqrt ((Mc φ S * t + c ^ 2) / 2) := by
    have h7 := mul_le_mul_of_nonneg_left hd hW1
    have e1 : indexWeight n ^ (N + 1) * (2 * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) +
        Real.sqrt (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4))) =
        2 * (indexWeight n ^ (N + 1) * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖)) +
        indexWeight n ^ (N + 1) * Real.sqrt (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4)) := by ring
    rw [e1] at h7
    linarith
  -- the two endpoints
  have hτ : NlsGge.ThirdConsultation.KSPS.midpoint φ n = ((L : ℂ) + (U : ℂ)) / 2 := by
    unfold NlsGge.ThirdConsultation.KSPS.midpoint; rw [hPU, hML]
  have hpl : periodicPlus φ n - spectralPolynomial φ n - (s : ℂ) =
      (NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) + ((x - s : ℝ) : ℂ) := by
    rw [hτ, hPU, hxdef]; push_cast; ring
  have hmi : periodicMinus φ n - spectralPolynomial φ n + (s : ℂ) =
      (NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) - ((x - s : ℝ) : ℂ) := by
    rw [hτ, hML, hxdef]; push_cast; ring
  have hxsn : ‖((x - s : ℝ) : ℂ)‖ = |x - s| := by rw [Complex.norm_real, Real.norm_eq_abs]
  constructor
  · rw [hpl]
    have h7 := norm_add_le (NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n)
      ((x - s : ℝ) : ℂ)
    rw [hxsn] at h7
    have h8 := mul_le_mul_of_nonneg_left h7 hW1
    rw [mul_add] at h8
    unfold Qc
    linarith
  · rw [hmi]
    have h7 := norm_sub_le (NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n)
      ((x - s : ℝ) : ℂ)
    rw [hxsn] at h7
    have h8 := mul_le_mul_of_nonneg_left h7 hW1
    rw [mul_add] at h8
    unfold Qc
    linarith


theorem KSPSsq_mul_add (k : ℝ) {f g : ℤ → ℝ} (hf : Summable (fun n => f n ^ 2)) (hg : Summable (fun n => g n ^ 2)) :
    Summable (fun n => (k * (f n + g n)) ^ 2) := by
  have h : Summable (fun n => (f n + g n) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ((hf.mul_left 2).add (hg.mul_left 2))
    nlinarith [sq_nonneg (f n - g n)]
  simp_rw [mul_pow]
  exact h.mul_left _

theorem lp4_of (A t c : ℤ → ℝ) (M : ℝ) (hM : 0 ≤ M) (e : ℤ → ℂ)
    (hA : Summable (fun n => A n ^ 2)) (ht : Summable (fun n => t n ^ 2)) (hc : Summable (fun n => c n ^ 2))
    (hA0 : ∀ n, 0 ≤ A n) (ht0 : ∀ n, 0 ≤ t n) (hc0 : ∀ n, 0 ≤ c n)
    (he : ∀ᶠ n : ℤ in cofinite, ‖e n‖ ≤ A n + 2 * (t n + c n) + Real.sqrt ((M * t n + c n ^ 2) / 2)) :
    LpSequence 4 e := by
  have hA4 := four_of_sq _ hA
  have hU4 := four_of_sq _ (KSPSsq_mul_add 2 ht hc)
  have hc4 := four_of_sq _ hc
  have hY2 : Summable (fun n : ℤ => ((M * t n + c n ^ 2) / 2) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      ((ht.mul_left (M ^ 2 / 2)).add (hc4.div_const 2))
    have e1 : c n ^ 4 = (c n ^ 2) ^ 2 := by ring
    rw [e1]
    nlinarith [sq_nonneg (M * t n - c n ^ 2)]
  have hQ4 : Summable (fun n : ℤ => (A n + 2 * (t n + c n) + Real.sqrt ((M * t n + c n ^ 2) / 2)) ^ 4) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((hA4.add hU4).add hY2).mul_left 27)
    have hU0 : 0 ≤ 2 * (t n + c n) := mul_nonneg (by norm_num) (add_nonneg (ht0 n) (hc0 n))
    have hy0 : 0 ≤ (M * t n + c n ^ 2) / 2 := by
      have h8 := mul_nonneg hM (ht0 n)
      have h9 := sq_nonneg (c n)
      linarith
    have hV : Real.sqrt ((M * t n + c n ^ 2) / 2) ^ 4 = ((M * t n + c n ^ 2) / 2) ^ 2 := by
      have e1 : Real.sqrt ((M * t n + c n ^ 2) / 2) ^ 4 =
          (Real.sqrt ((M * t n + c n ^ 2) / 2) ^ 2) ^ 2 := by ring
      rw [e1, Real.sq_sqrt hy0]
    have h7 := pow4_sum_le _ _ _ (hA0 n) hU0 (Real.sqrt_nonneg ((M * t n + c n ^ 2) / 2))
    rw [hV] at h7
    exact h7
  unfold LpSequence
  have key : ∀ n : ℤ, ‖e n‖ ^ (4 : ℝ) = ‖e n‖ ^ (4 : ℕ) := by
    intro n
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [key]
  refine Summable.of_norm_bounded_eventually hQ4 ?_
  filter_upwards [he] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 4

end
end NlsGge.ThirdConsultation.KSPS028C
