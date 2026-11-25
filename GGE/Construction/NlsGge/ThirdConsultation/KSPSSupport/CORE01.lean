import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.WkbStructure
import NlsGge.ThirdConsultation.G1.Wkb035A
import NlsGge.Atomic.G1.G1034
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPSSupport

                                                       
                                                                                                      
                                                                                                   
                                                                      
                                                                                      
                                                                                       
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- Scalar multiples preserve physical Sobolev membership (coordinatewise in the Fourier basis). -/
theorem h150_smul_mem (r : ℝ) (c : ℂ) {u : PhysicalL2} (hu : physicalSobolev r u) :
    physicalSobolev r (c • u) := by
  unfold physicalSobolev SobolevSquareSummable at hu ⊢
  refine (hu.mul_left (‖c‖ ^ 2)).congr (fun n => ?_)
  rw [reflectedFourierL2_smul_apply, norm_mul, mul_pow]
  ring

/-- The zero field lies in every physical Sobolev class. -/
theorem h150_zero_mem (r : ℝ) : physicalSobolev r (0 : PhysicalL2) := by
  unfold physicalSobolev SobolevSquareSummable
  simp

/-- One weak derivative: the Fourier symbol formula, for a field of Sobolev index at least one. -/
theorem h150_wD_coeff (m : ℕ) {u : PhysicalL2} (hu : physicalSobolev ((m + 1 : ℕ) : ℝ) u) (n : ℤ) :
    reflectedFourierL2 (weakDerivative u) n =
      (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * reflectedFourierL2 u n :=
  weakDerivative_coeff u
    (weakDerivative_domain_of_H1 u (g35_H1_nat _ (psn_mono (Nat.le_add_left 1 m) hu).1)) n

/-- S3 (iterate form): the j-th weak derivative of v lies in order N-j and has the symbol power. -/
theorem h150_iter_coeff (N : ℕ) (v : PhysicalL2) (hv : physicalSobolev (N : ℝ) v) :
    ∀ j : ℕ, j ≤ N →
      physicalSobolev ((N - j : ℕ) : ℝ) (weakDerivative^[j] v) ∧
      ∀ n : ℤ, reflectedFourierL2 (weakDerivative^[j] v) n =
        (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ j * reflectedFourierL2 v n := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨by simpa using hv, fun n => by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨hmem, hcoef⟩ := ih (by omega)
    obtain ⟨m, hm⟩ : ∃ m, N - j = m + 1 := ⟨N - j - 1, by omega⟩
    have hm' : N - (j + 1) = m := by omega
    rw [hm] at hmem
    rw [Function.iterate_succ_apply', hm']
    refine ⟨(psn_deriv m hmem).1, fun n => ?_⟩
    rw [h150_wD_coeff m hmem n, hcoef n]
    ring

/-- S3: the fixed-order Riccati derivative of an order-N Sobolev field is the N-fold weak-derivative
iterate of its embedding in physical L2. -/
theorem physicalSobolevDerivative38_eq_iterate (N : ℕ) (u : PhysicalSobolev38 (N : ℝ)) :
    physicalSobolevDerivative38 N u = weakDerivative^[N] (physicalSobolevEmbed N u) := by
  obtain ⟨_, hcoef⟩ :=
    h150_iter_coeff N (physicalSobolevEmbed N u) (physicalSobolevEmbed_mem N u) N le_rfl
  apply reflectedFourierL2.injective
  apply lp.ext
  funext n
  have hL : reflectedFourierL2 (physicalSobolevDerivative38 N u) n =
      (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
        carrierCoe38 (N : ℝ) (physicalSobolevFourierEquiv38 (N : ℝ) u) n :=
    physicalSobolevDerivative38_reflected N u n
  have hE : reflectedFourierL2 (physicalSobolevEmbed N u) n =
      carrierCoe38 (N : ℝ) (physicalSobolevFourierEquiv38 (N : ℝ) u) n :=
    physicalSobolevEmbed_fourier N u n
  rw [hL, hcoef n, hE]

/-- C2 (left and right, index N+1-k) for 1 <= k <= N: the coefficient is the G1 WKB coefficient of the
relevant pair (the right one is the swapped pair with a unit sign). -/
theorem h150_coef_mem_le (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (k : ℕ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    physicalSobolev ((N + 1 - k : ℕ) : ℝ) (KSPSRiccati.coefficient φ b k) := by
  obtain ⟨_, _, _, h⟩ := G1_034 N hN
  cases b
  · show physicalSobolev _ (wkbR (toPotPair φ) k)
    exact ((h (toPotPair φ) (pairSobolev_toPotPair φ)).2.2.1 k hk1 hkN).1
  · show physicalSobolev _ (((-1 : ℂ) ^ (k + 1)) • wkbR (Prod.swap (toPotPair φ)) k)
    exact h150_smul_mem _ _ ((h (Prod.swap (toPotPair φ)) (pairSobolev_swap_toPotPair φ)).2.2.1 k hk1 hkN).1

/-- C2 for all 1 <= k <= N+1; at k = N+1 the index is zero and every physical L2 field qualifies. -/
theorem h150_coef_mem (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (k : ℕ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N + 1) :
    physicalSobolev ((N + 1 - k : ℕ) : ℝ) (KSPSRiccati.coefficient φ b k) := by
  rcases Nat.lt_or_ge N k with h | h
  · have hk : k = N + 1 := by omega
    subst hk
    simpa using physicalSobolev_zero_all (KSPSRiccati.coefficient φ b (N + 1))
  · exact h150_coef_mem_le N hN φ b k hk1 h

/-- The coefficient of order k <= N is in H^1 (its index N+1-k is at least one). -/
theorem h150_coef_H1 (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (k : ℕ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    physicalSobolev 1 (KSPSRiccati.coefficient φ b k) :=
  g35_H1_nat _ (psn_mono (show 1 ≤ N + 1 - k by omega)
    (h150_coef_mem N hN φ b k hk1 (by omega))).1

/-- The side potential is in order N, hence in H^1 for N >= 1. -/
theorem h150_side_mem (N : ℕ) (φ : SobolevC N) (b : Bool) :
    physicalSobolev ((N : ℕ) : ℝ) (sidePotential φ b) := by
  obtain ⟨hs1, hs2⟩ := pairSobolev_toPotPair φ
  cases b
  · exact hs1
  · exact hs2

theorem h150_side_H1 (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) :
    physicalSobolev 1 (sidePotential φ b) :=
  g35_H1_nat _ (psn_mono hN (h150_side_mem N φ b)).1

/-- S7: the partial sum defining `partial` lies in H^1 for every lam (only N >= 1 is used). -/
theorem partial_H1 {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (hN : 1 ≤ N) :
    physicalSobolev 1 («partial» φ b lam) := by
  unfold «partial»
  refine g35_H1_sum (Finset.Icc 1 N) (fun k => ((2 * Complex.I * lam) ^ k)⁻¹ • KSPSRiccati.coefficient φ b k)
    (fun k hk => g35_H1_smul _ (h150_coef_H1 N hN φ b k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2))

/-- S10: each quadratic term is in H^1 for every j: products of two order-(N+1-k) fields with
indices at least one, multiplied by the H^1 side potential. -/
theorem quadratic_H1 {N : ℕ} (φ : SobolevC N) (b : Bool) (j : ℕ) (hN : 1 ≤ N) :
    physicalSobolev 1 (quadratic φ b j) := by
  unfold quadratic
  apply g35_H1_nat
  obtain ⟨_, _, hP⟩ := psn_prod 1 le_rfl
  have hterm : ∀ k ∈ Finset.Icc 1 N, ∀ l ∈ Finset.Icc 1 N,
      physicalSobolev 1 (if k + l = j then
        physicalProduct (KSPSRiccati.coefficient φ b k) (KSPSRiccati.coefficient φ b l) else 0) := by
    intro k hk l hl
    split_ifs
    · exact g35_H1_nat _ (hP _ _ (g35_H1_cast _ (h150_coef_H1 N hN φ b k
        (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2))
        (g35_H1_cast _ (h150_coef_H1 N hN φ b l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2))).1
    · exact g35_H1_zero
  have hin : physicalSobolev 1 (∑ k ∈ Finset.Icc 1 N, ∑ l ∈ Finset.Icc 1 N,
      if k + l = j then physicalProduct (KSPSRiccati.coefficient φ b k) (KSPSRiccati.coefficient φ b l) else 0) :=
    g35_H1_sum (Finset.Icc 1 N)
      (fun k => ∑ l ∈ Finset.Icc 1 N,
        if k + l = j then physicalProduct (KSPSRiccati.coefficient φ b k) (KSPSRiccati.coefficient φ b l) else 0)
      (fun k hk => g35_H1_sum (Finset.Icc 1 N)
        (fun l => if k + l = j then physicalProduct (KSPSRiccati.coefficient φ b k) (KSPSRiccati.coefficient φ b l) else 0)
        (fun l hl => hterm k hk l hl))
  exact (hP _ _ (g35_H1_cast _ (h150_side_H1 N hN φ b)) (g35_H1_cast _ hin)).1

end
end NlsGge.ThirdConsultation.KSPSSupport
