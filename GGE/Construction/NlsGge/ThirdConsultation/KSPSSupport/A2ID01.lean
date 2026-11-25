import Mathlib
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPSSupport.EXP01
import NlsGge.ThirdConsultation.KSPSSupport.UNI01
import NlsGge.ThirdConsultation.KSPSSupport.A1U01
import NlsGge.ThirdConsultation.KSPSSupport.CLAUSES01
import NlsGge.ThirdConsultation.KSPSSupport.RHO01

                                                                               
                                                                         
                                                                           
                                                                                           
                                                                                              
                                                                                             
                                                                                     
                                                                           
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- v = z^{-1} for z = 2 i lam. -/
def h161_v (lam : ℂ) : ℂ := (2 * Complex.I * lam)⁻¹

/-- Sign of the right-hand coefficient in a1 (the sign used in a1). -/
def h161_sig (b : Bool) : ℂ := if b then 1 else -1

/-- Sign of the phase exponent. -/
def h161_sgn (b : Bool) : ℂ := if b then -1 else 1

/-- Tp: the tail sum of quadratic terms of order at least N+2. -/
def h161_Tp {N : ℕ} (ψ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc (N + 2) (2 * N),
    h161_v lam ^ (j - N - 2) * coverRep38 (KSPSRiccati.quadratic ψ b j) x

/-- W2: the phase exponent without its first-order term (sum over k = 2..N). -/
def h161_W2 {N : ℕ} (ψ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ) : ℂ :=
  h161_sgn b * ∑ k ∈ Finset.Icc 2 N, h161_v lam ^ (k - 2) * KSPSRiccati.«prefix» ψ b k x

/-- G: the rhoTail combination after multiplication by z^N. -/
def h161_G {N : ℕ} (ψ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ) : ℂ :=
  coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) x +
    h161_v lam * coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) x +
    h161_v lam ^ 2 * h161_Tp ψ b lam x

/-- wexp: the phase exponent in the expanded form v sig M + v^2 W2. -/
def h161_wexp {N : ℕ} (ψ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ) : ℂ :=
  h161_v lam * (h161_sig b * KSPSRiccati.massPrefix ψ x) + h161_v lam ^ 2 * h161_W2 ψ b lam x

/-- Power splitting: z^N (z^j)⁻¹ = (z⁻¹)^(j-N) for N ≤ j and z ≠ 0. -/
theorem h161_pow_split (z : ℂ) (hz : z ≠ 0) (N j : ℕ) (hj : N ≤ j) :
    z ^ N * (z ^ j)⁻¹ = (z⁻¹) ^ (j - N) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show N + m - N = m by omega, pow_add, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero N hz), one_mul, inv_pow]

/-- The first Picard term of the phase is minus the mass prefix (for both sides). -/
theorem h161_prefix_one {N : ℕ} (ψ : SobolevC N) (b : Bool) (x : ℝ) :
    KSPSRiccati.«prefix» ψ b 1 x = -KSPSRiccati.massPrefix ψ x := by
  unfold KSPSRiccati.«prefix» KSPSRiccati.massPrefix
  have hc : ∀ᵐ t : ℝ, coverRep38 (KSPSRiccati.coefficient ψ b 1) t =
      -coverRep38 (KSPSRiccati.sideInput ψ b) t := by
    rw [h150_C1 ψ b]
    filter_upwards [coverRep38_smul_ae (-1 : ℂ) (KSPSRiccati.sideInput ψ b)] with t ht
    rw [neg_one_smul] at ht
    simpa using ht
  have hint : (∫ t in (0 : ℝ)..x,
      coverRep38 (KSPSRiccati.sidePotential ψ b) t * coverRep38 (KSPSRiccati.coefficient ψ b 1) t) =
      ∫ t in (0 : ℝ)..x, -(coverRep38 (KSPSRiccati.sidePotential ψ b) t *
        coverRep38 (KSPSRiccati.sideInput ψ b) t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hc] with t ht _
    rw [ht]
    ring
  rw [hint, intervalIntegral.integral_neg]
  congr 1
  cases b
  · rfl
  · exact intervalIntegral.integral_congr (fun t _ => mul_comm _ _)

/-- The phase exponent splits as v (sig M) + v^2 W2. -/
theorem h161_phase_split {N : ℕ} (hN : 1 ≤ N) (ψ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ) :
    (if b then (-1 : ℂ) else 1) * ∑ k ∈ Finset.Icc 1 N,
      ((2 * Complex.I * lam) ^ k)⁻¹ * KSPSRiccati.«prefix» ψ b k x =
      h161_wexp ψ b lam x := by
  have hI : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hsum : ∑ k ∈ Finset.Icc 2 N, ((2 * Complex.I * lam) ^ k)⁻¹ *
      KSPSRiccati.«prefix» ψ b k x =
      h161_v lam ^ 2 * ∑ k ∈ Finset.Icc 2 N, h161_v lam ^ (k - 2) *
        KSPSRiccati.«prefix» ψ b k x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hk1, _⟩ := Finset.mem_Icc.1 hk
    have hpow : ((2 * Complex.I * lam) ^ k)⁻¹ = h161_v lam ^ 2 * h161_v lam ^ (k - 2) := by
      unfold h161_v
      rw [← inv_pow, ← pow_add]
      congr 1
      omega
    rw [hpow]
    ring
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 N := by simp
  rw [hI, Finset.sum_insert hnot, pow_one, h161_prefix_one, mul_add, hsum]
  unfold h161_wexp h161_W2 h161_sig h161_sgn h161_v
  cases b <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The sum of a family of scalar multiples has the coordinatewise a.e. representative. -/
theorem h161_coverRep_sum_smul_ae {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (f : ι → PhysicalL2) :
    ∀ᵐ t : ℝ, coverRep38 (∑ i ∈ s, c i • f i) t = ∑ i ∈ s, c i * coverRep38 (f i) t := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 := coverRep38_smul_ae (0 : ℂ) (0 : PhysicalL2)
    simpa using h0
  | insert a s ha ih =>
    filter_upwards [coverRep38_add_ae (c a • f a) (∑ i ∈ s, c i • f i),
      coverRep38_smul_ae (c a) (f a), ih] with t h1 h2 h3
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, h2, h3]

/-- Splitting the sum over j in [N+1, 2N] at j = N+1. -/
theorem h161_sum_split (N : ℕ) (hN : 1 ≤ N) (g : ℕ → ℂ) :
    ∑ j ∈ Finset.Icc (N + 1) (2 * N), g j =
      g (N + 1) + ∑ j ∈ Finset.Icc (N + 2) (2 * N), g j := by
  have hI : Finset.Icc (N + 1) (2 * N) = insert (N + 1) (Finset.Icc (N + 2) (2 * N)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : N + 1 ∉ Finset.Icc (N + 2) (2 * N) := by simp
  rw [hI, Finset.sum_insert hnot]

/-- The forcing equals the phase factor times G, almost everywhere. -/
theorem h161_forcing_ae {N : ℕ} (hN : 1 ≤ N) (ψ : SobolevC N) (b : Bool) (lam : ℂ)
    (hlam : lam ≠ 0) :
    ∀ᵐ x : ℝ, KSPSRiccati.forcing ψ b lam x =
      KSPSRiccati.phaseFactor ψ b lam x * h161_G ψ b lam x := by
  have hz : (2 * Complex.I * lam) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hlam
  have hrho := h150_rho_eq_rhoTail N hN ψ b lam hlam
  have hfor : ∀ x : ℝ, KSPSRiccati.forcing ψ b lam x =
      (2 * Complex.I * lam) ^ N * KSPSRiccati.phaseFactor ψ b lam x *
        coverRep38 (KSPSRiccati.rhoTail ψ b lam) x := by
    intro x
    unfold KSPSRiccati.forcing
    rw [hrho]
  have hcov : ∀ᵐ x : ℝ, coverRep38 (KSPSRiccati.rhoTail ψ b lam) x =
      ((2 * Complex.I * lam) ^ N)⁻¹ * coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) x +
        ∑ j ∈ Finset.Icc (N + 1) (2 * N),
          ((2 * Complex.I * lam) ^ j)⁻¹ * coverRep38 (KSPSRiccati.quadratic ψ b j) x := by
    unfold KSPSRiccati.rhoTail
    filter_upwards [coverRep38_add_ae (((2 * Complex.I * lam) ^ N)⁻¹ •
        KSPSRiccati.coefficient ψ b (N + 1))
      (∑ j ∈ Finset.Icc (N + 1) (2 * N), ((2 * Complex.I * lam) ^ j)⁻¹ •
        KSPSRiccati.quadratic ψ b j),
      coverRep38_smul_ae (((2 * Complex.I * lam) ^ N)⁻¹) (KSPSRiccati.coefficient ψ b (N + 1)),
      h161_coverRep_sum_smul_ae (Finset.Icc (N + 1) (2 * N))
        (fun j => ((2 * Complex.I * lam) ^ j)⁻¹) (fun j => KSPSRiccati.quadratic ψ b j)] with
      t h1 h2 h3
    rw [h1, h2, h3]
  filter_upwards [hcov] with x hx
  rw [hfor x, hx]
  unfold h161_G
  rw [h161_sum_split N hN (fun j => ((2 * Complex.I * lam) ^ j)⁻¹ *
    coverRep38 (KSPSRiccati.quadratic ψ b j) x)]
  have hNz : (2 * Complex.I * lam) ^ N * ((2 * Complex.I * lam) ^ N)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero N hz)
  have hv1 : (2 * Complex.I * lam) ^ N * ((2 * Complex.I * lam) ^ (N + 1))⁻¹ = h161_v lam := by
    unfold h161_v
    rw [h161_pow_split _ hz N (N + 1) (by omega), show N + 1 - N = 1 by omega, pow_one]
  have hTp' : (2 * Complex.I * lam) ^ N * ∑ j ∈ Finset.Icc (N + 2) (2 * N),
      ((2 * Complex.I * lam) ^ j)⁻¹ * coverRep38 (KSPSRiccati.quadratic ψ b j) x =
      h161_v lam ^ 2 * h161_Tp ψ b lam x := by
    unfold h161_Tp
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj1, _⟩ := Finset.mem_Icc.1 hj
    have hpow : ((2 * Complex.I * lam)⁻¹) ^ (j - N) =
        (2 * Complex.I * lam)⁻¹ ^ 2 * (2 * Complex.I * lam)⁻¹ ^ (j - N - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← mul_assoc, h161_pow_split _ hz N j (by omega), hpow]
    unfold h161_v
    ring
  linear_combination (KSPSRiccati.phaseFactor ψ b lam x * coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) x) * hNz +
    (KSPSRiccati.phaseFactor ψ b lam x * coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) x) * hv1 +
    KSPSRiccati.phaseFactor ψ b lam x * hTp'

/-- The algebraic core of the a2 expansion: a polynomial identity modulo z v = 1. -/
theorem h161_alg (z v E C Q1 Tp M σ W2 : ℂ) (hz : z * v = 1) :
    z ^ 2 * (E * (C + v * Q1 + v ^ 2 * Tp) - C - v * (Q1 + σ * C * M)) =
      Tp + σ * M * Q1 + v * σ * M * Tp + W2 * (C + v * Q1 + v ^ 2 * Tp) +
        z ^ 2 * (E - 1 - (v * (σ * M) + v ^ 2 * W2)) * (C + v * Q1 + v ^ 2 * Tp) := by
  linear_combination ((z * v + 1) * (Tp + σ * M * Q1 + v * σ * M * Tp +
    W2 * (C + v * Q1 + v ^ 2 * Tp))) * hz

/-- R2a: the a.e. expansion of a2 (the cancellation of the (2 i lam)^{-1} terms). -/
theorem h161_a2_identity {N : ℕ} (hN : 1 ≤ N) (ψ : SobolevC N) (b : Bool) (lam : ℂ)
    (hlam : lam ≠ 0) :
    ∀ᵐ x : ℝ, KSPSRiccati.a2 ψ b lam x =
      h161_Tp ψ b lam x + h161_sig b * KSPSRiccati.massPrefix ψ x *
          coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) x +
        h161_v lam * (h161_sig b * KSPSRiccati.massPrefix ψ x) * h161_Tp ψ b lam x +
        h161_W2 ψ b lam x * h161_G ψ b lam x +
        (2 * Complex.I * lam) ^ 2 *
          (Complex.exp (h161_wexp ψ b lam x) - 1 - h161_wexp ψ b lam x) * h161_G ψ b lam x := by
  have hz : (2 * Complex.I * lam) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hlam
  have hzv : (2 * Complex.I * lam) * h161_v lam = 1 := by
    unfold h161_v
    exact mul_inv_cancel₀ hz
  filter_upwards [h161_forcing_ae hN ψ b lam hlam] with x hx
  have ha1 : KSPSRiccati.a1 ψ b x = coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) x +
      h161_sig b * coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) x *
        KSPSRiccati.massPrefix ψ x := rfl
  have hph := h161_phase_split hN ψ b lam x
  unfold KSPSRiccati.a2
  rw [hx, ha1]
  unfold KSPSRiccati.phaseFactor
  rw [hph]
  have key := h161_alg (2 * Complex.I * lam) (h161_v lam)
    (Complex.exp (h161_wexp ψ b lam x))
    (coverRep38 (KSPSRiccati.coefficient ψ b (N + 1)) x)
    (coverRep38 (KSPSRiccati.quadratic ψ b (N + 1)) x) (h161_Tp ψ b lam x)
    (KSPSRiccati.massPrefix ψ x) (h161_sig b) (h161_W2 ψ b lam x) hzv
  simp only [h161_G, h161_wexp, h161_v] at key ⊢
  linear_combination key

end
end NlsGge.ThirdConsultation.KSPSSupport
