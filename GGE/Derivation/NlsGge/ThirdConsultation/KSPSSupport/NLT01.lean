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
import NlsGge.ThirdConsultation.KSPSSupport.CORE01
import NlsGge.ThirdConsultation.KSPSSupport.RHO01

/- KSPS-010 NLT01 (proof development, AUTHOR; not reviewed).
   S9: physicalSobolev 2 (nonlinearTop phi b), by the remainder induction.
   With R'(j) := wkbR p (j+1) + weakDerivative^[j] p.2 (p = the left pair, or its swap for b = true):
   R'(1) = 0 (G1 wkbR_two), and R'(j+1) = weakDerivative (R'(j)) + physicalProduct p.1 (recurrence sum), so
   R'(j) lies in order N+2-j; at j = N this is order 2, and nonlinearTop equals R'(N) (b = false) or a unit
   multiple of it (b = true, using S3). -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- The G1 coefficient membership on the pair p (index N+1-k) for 1 <= k <= N. -/
theorem h150_wkbR_mem (N : ℕ) (hN : 1 ≤ N) (p : PotPair) (hp : pairSobolev (N : ℝ) p)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    physicalSobolev ((N + 1 - k : ℕ) : ℝ) (wkbR p k) := by
  obtain ⟨_, _, _, h⟩ := G1_034 N hN
  exact ((h p hp).2.2.1 k hk1 hkN).1

/-- R'(1) = 0: the second WKB term is the negated weak derivative of the input. -/
theorem h150_R_one (p : PotPair) : wkbR p 2 + weakDerivative^[1] p.2 = 0 := by
  rw [wkbR_two, Function.iterate_one, neg_add_cancel]

/-- Remainder induction: R'(m+1) = wkbR p (m+2) + D^(m+1) p.2 lies in order N-m+1 for m < N. -/
theorem h150_R_claim (N : ℕ) (hN : 1 ≤ N) (p : PotPair) (hp : pairSobolev (N : ℝ) p) :
    ∀ m : ℕ, m < N →
      physicalSobolev ((N + 1 - m : ℕ) : ℝ) (wkbR p (m + 1 + 1) + weakDerivative^[m + 1] p.2) := by
  obtain ⟨hp1, hp2⟩ := hp
  intro m
  induction m with
  | zero =>
    intro _
    have h0 : wkbR p (0 + 1 + 1) + weakDerivative^[0 + 1] p.2 = 0 := h150_R_one p
    rw [h0]
    simpa using h150_zero_mem (((N + 1 - 0 : ℕ)) : ℝ)
  | succ m ih =>
    intro hm
    have hR := ih (by omega)
    have hW : physicalSobolev 1 (wkbR p (m + 1 + 1)) :=
      h150_wkbR_H1 N hN p ⟨hp1, hp2⟩ (m + 1 + 1) (by omega) (by omega)
    have hV : physicalSobolev 1 (weakDerivative^[m + 1] p.2) :=
      g35_H1_nat _ (psn_mono (show 1 ≤ N - (m + 1) by omega)
        (h150_iter_coeff N p.2 hp2 (m + 1) (by omega)).1).1
    have hrec := wkbR_succ p (m + 1 + 1) (by omega)
    have hit : weakDerivative^[m + 1 + 1] p.2 = weakDerivative (weakDerivative^[m + 1] p.2) :=
      Function.iterate_succ_apply' _ _ _
    have hfin : wkbR p (m + 1 + 1 + 1) + weakDerivative^[m + 1 + 1] p.2 =
        weakDerivative (wkbR p (m + 1 + 1) + weakDerivative^[m + 1] p.2) +
          physicalProduct p.1 (∑ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
            physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) := by
      rw [hrec, hit, g35_D_add hW hV]
      abel
    rw [hfin]
    have e1 : N + 1 - m = N - m + 1 := by omega
    rw [e1] at hR
    have hD : physicalSobolev ((N - m : ℕ) : ℝ)
        (weakDerivative (wkbR p (m + 1 + 1) + weakDerivative^[m + 1] p.2)) :=
      (psn_deriv (N - m) hR).1
    obtain ⟨_, _, hPr⟩ := psn_prod (N - m) (by omega)
    have hpA : physicalSobolev ((N - m : ℕ) : ℝ) p.1 := (psn_mono (show N - m ≤ N by omega) hp1).1
    have hterm : ∀ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
        physicalSobolev ((N - m : ℕ) : ℝ) (physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
      have hA : physicalSobolev ((N - m : ℕ) : ℝ) (wkbR p i) :=
        (psn_mono (show N - m ≤ N + 1 - i by omega) (h150_wkbR_mem N hN p ⟨hp1, hp2⟩ i hi1 (by omega))).1
      have hB : physicalSobolev ((N - m : ℕ) : ℝ) (wkbR p (m + 1 + 1 - i)) :=
        (psn_mono (show N - m ≤ N + 1 - (m + 1 + 1 - i) by omega)
          (h150_wkbR_mem N hN p ⟨hp1, hp2⟩ (m + 1 + 1 - i) (by omega) (by omega))).1
      exact (hPr _ _ hA hB).1
    have hSum : physicalSobolev ((N - m : ℕ) : ℝ) (∑ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
        physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) :=
      (psn_sum (N - m) (Finset.Icc 1 (m + 1 + 1 - 1))
        (fun i => physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i))) hterm).1
    have hP : physicalSobolev ((N - m : ℕ) : ℝ)
        (physicalProduct p.1 (∑ i ∈ Finset.Icc 1 (m + 1 + 1 - 1),
          physicalProduct (wkbR p i) (wkbR p (m + 1 + 1 - i)))) :=
      (hPr _ _ hpA hSum).1
    have e2 : N + 1 - (m + 1) = N - m := by omega
    rw [e2]
    exact (psn_add (N - m) hD hP).1


/-- R'(N) at the top index: the remainder of order two. -/
theorem h150_R_final (N : ℕ) (hN : 1 ≤ N) (p : PotPair) (hp : pairSobolev (N : ℝ) p) :
    physicalSobolev ((2 : ℕ) : ℝ) (wkbR p (N + 1) + weakDerivative^[N] p.2) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hc := h150_R_claim (m + 1) hN p hp m (by omega)
  have e3 : m + 1 + 1 - m = 2 := by omega
  rw [e3] at hc
  exact hc

/-- The left nonlinearTop is the remainder R'(N) (the S3 iterate identifies the top derivative). -/
theorem h150_nonlinear_false (N : ℕ) (φ : SobolevC N) :
    KSPSRiccati.nonlinearTop φ false =
      wkbR (toPotPair φ) (N + 1) + weakDerivative^[N] (toPotPair φ).2 := by
  show wkbR (toPotPair φ) (N + 1) - -physicalSobolevDerivative38 N φ.2 = _
  rw [physicalSobolevDerivative38_eq_iterate, sub_neg_eq_add]
  rfl

/-- The right nonlinearTop is (-1)^N times the remainder of the swap pair. -/
theorem h150_nonlinear_true (N : ℕ) (φ : SobolevC N) :
    KSPSRiccati.nonlinearTop φ true =
      (-1 : ℂ) ^ N • (wkbR (Prod.swap (toPotPair φ)) (N + 1) +
        weakDerivative^[N] (Prod.swap (toPotPair φ)).2) := by
  show ((-1 : ℂ) ^ (N + 1 + 1)) • wkbR (Prod.swap (toPotPair φ)) (N + 1) -
      ((-1 : ℂ) ^ (N + 1)) • physicalSobolevDerivative38 N φ.1 = _
  rw [physicalSobolevDerivative38_eq_iterate]
  have e1 : (-1 : ℂ) ^ (N + 1 + 1) = (-1 : ℂ) ^ N := by ring
  have e2 : (-1 : ℂ) ^ (N + 1) = -(-1 : ℂ) ^ N := by ring
  rw [e1, e2, neg_smul, sub_neg_eq_add, smul_add]
  rfl

/-- S9: the nonlinear top term of the Riccati recursion is in H^2, for both sides. -/
theorem nonlinearTop_H2 (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) :
    physicalSobolev 2 (KSPSRiccati.nonlinearTop φ b) := by
  cases b
  · rw [h150_nonlinear_false]
    exact_mod_cast h150_R_final N hN (toPotPair φ) (pairSobolev_toPotPair φ)
  · rw [h150_nonlinear_true]
    have h := h150_R_final N hN (Prod.swap (toPotPair φ)) (pairSobolev_swap_toPotPair φ)
    exact h150_smul_mem _ _ (by exact_mod_cast h)

end
end NlsGge.ThirdConsultation.KSPSSupport
