import Mathlib
import NlsGge.Atomic.KSN.KSN018Sup1
import NlsGge.ThirdConsultation.KSPS.KSPS025Host
import NlsGge.ThirdConsultation.KSPS.KSPS016Host
import NlsGge.ThirdConsultation.KSPS.KSPS019Host
import NlsGge.GK38.TauGamma

/- KSN018 LINK PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN018Link.lean.
   SUPPORT (no packet increment) for KSN-018: transports Pro r15's two uniform remainder companions
   (KSPS.midpoint_dirichlet_difference_uniform, KSPS.antitrace_at_dirichlet_uniform; conclusion types taken verbatim as
   hypotheses) to the PairScale-N carrier through the landed all-order bridge toSobolevCN (KSN018Sup1):
   toPotPair (toSobolevCN N x) = pairPotential N x, sobolevNorm N ≤ 2ᴺ‖x‖, Fourier coefficients = raw coefficients
   (KSN-001 reflected signs), midpoint = tauN on gkW (tauN_value38), mu = muSeq, antitrace = antiDiscrim (literal bodies),
   bracket n ≤ indexWeight n. Output: for ‖x‖ ≤ H, finite sums of (⟨n⟩^{N+1}·|E_i|)² bounded by C_i², the exact forms of
   the hE1/hE2 hypotheses of KSN018Sum. No hypothesis added. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem ksn018_bracket_le_indexWeight (n : ℤ) : bracket n ≤ NlsGge.ThirdConsultation.KSPS.indexWeight n := by
  unfold bracket NlsGge.ThirdConsultation.KSPS.indexWeight
  have hm : ((n.natAbs : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have h0 : 0 ≤ max 1 ((n.natAbs : ℕ) : ℝ) := le_trans zero_le_one (le_max_left _ _)
  rw [← Real.sqrt_sq h0]
  apply Real.sqrt_le_sqrt
  rcases max_cases 1 ((n.natAbs : ℕ) : ℝ) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; nlinarith [sq_nonneg (n : ℝ)]
  · rw [h, hm]; linarith

theorem ksn018_fourier_fst (N : ℕ) (x : PairScale (N : ℝ)) (n : ℤ) :
    physicalFourier (pairPotential (N : ℝ) (Nat.cast_nonneg N) x).1 n = rawCoefficient (N : ℝ) x true n := by
  rw [← physicalFourierL2_apply]
  change physicalFourierL2 (physicalFourierL2.symm ⟨rawCoefficient (N : ℝ) x true,
    rawCoefficient_mem (N : ℝ) (Nat.cast_nonneg N) x true⟩) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem ksn018_fourier_snd (N : ℕ) (x : PairScale (N : ℝ)) (n : ℤ) :
    physicalFourier (pairPotential (N : ℝ) (Nat.cast_nonneg N) x).2 n = rawCoefficient (N : ℝ) x false n := by
  rw [← physicalFourierL2_apply]
  change physicalFourierL2 (physicalFourierL2.symm ⟨rawCoefficient (N : ℝ) x false,
    rawCoefficient_mem (N : ℝ) (Nat.cast_nonneg N) x false⟩) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem ksn018_E1_eq (N : ℕ) (x : PairScale (N : ℝ)) (hW : pairPotential (N : ℝ) (Nat.cast_nonneg N) x ∈ gkW)
    (n : ℤ) :
    tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n - muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n +
        (rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2 =
      NlsGge.ThirdConsultation.KSPS.midpoint (toSobolevCN N x) n -
        NlsGge.ThirdConsultation.KSPS.mu (toSobolevCN N x) n +
        (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair (toSobolevCN N x)).1 (-n) +
          physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair (toSobolevCN N x)).2 n) / 2 := by
  unfold NlsGge.ThirdConsultation.KSPS.midpoint NlsGge.ThirdConsultation.KSPS.mu
    NlsGge.ThirdConsultation.KSPS.periodicMinus NlsGge.ThirdConsultation.KSPS.periodicPlus
  rw [toPotPair_toSobolevCN, ksn018_fourier_fst, ksn018_fourier_snd, tauN_value38 _ hW n]
  ring

theorem ksn018_E2_eq (N : ℕ) (x : PairScale (N : ℝ)) (n : ℤ) :
    antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
        (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
      Complex.I * (-1 : ℂ) ^ n * (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n) =
    NlsGge.ThirdConsultation.KSPSWKB.antitrace (toSobolevCN N x)
        (NlsGge.ThirdConsultation.KSPS.mu (toSobolevCN N x) n) -
      Complex.I * (-1 : ℂ) ^ n *
        (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair (toSobolevCN N x)).1 (-n) -
          physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair (toSobolevCN N x)).2 n) := by
  unfold NlsGge.ThirdConsultation.KSPSWKB.antitrace NlsGge.ThirdConsultation.KSPS.mu
  rw [toPotPair_toSobolevCN, ksn018_fourier_fst, ksn018_fourier_snd]
  rfl

theorem ksn018_transfer (N : ℕ) (F : Finset ℤ) (a b : ℤ → ℂ) (hab : ∀ n, a n = b n) :
    ∑ n ∈ F, (bracket n ^ (N + 1) * ‖a n‖) ^ 2 ≤
      ∑ n ∈ F, (NlsGge.ThirdConsultation.KSPS.indexWeight n ^ (N + 1) * ‖b n‖) ^ 2 := by
  refine Finset.sum_le_sum (fun n _ => ?_)
  rw [hab n]
  have h0 : 0 ≤ bracket n := le_trans zero_le_one (le_max_left _ _)
  exact pow_le_pow_left₀ (mul_nonneg (pow_nonneg h0 _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (ksn018_bracket_le_indexWeight n) _) (norm_nonneg _)) 2

/-- The two remainder finite sums on PairScale N, from the two KSPS companions at B₀ = 2ᴺ·H. -/
theorem ksn018_remainders (N : ℕ) (H : ℝ)
    (hmd : ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, NlsGge.ThirdConsultation.KSPS.sobolevNorm N φ ≤ 2 ^ N * H →
        NlsGge.ThirdConsultation.KSPS.WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - NlsGge.ThirdConsultation.KSPS.mu φ n +
            (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 (-n) +
             physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 n) / 2) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (NlsGge.ThirdConsultation.KSPS.indexWeight n ^ (N + 1) *
              ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - NlsGge.ThirdConsultation.KSPS.mu φ n +
                (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 (-n) +
                 physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 n) / 2‖)^2) ≤ C^2)
    (hat : ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, NlsGge.ThirdConsultation.KSPS.sobolevNorm N φ ≤ 2 ^ N * H →
        NlsGge.ThirdConsultation.KSPS.WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => NlsGge.ThirdConsultation.KSPSWKB.antitrace φ (NlsGge.ThirdConsultation.KSPS.mu φ n) -
            Complex.I * (-1 : ℂ)^n *
              (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 (-n) -
               physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 n)) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (NlsGge.ThirdConsultation.KSPS.indexWeight n ^ (N + 1) *
              ‖NlsGge.ThirdConsultation.KSPSWKB.antitrace φ (NlsGge.ThirdConsultation.KSPS.mu φ n) -
                Complex.I * (-1 : ℂ)^n *
                  (physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 (-n) -
                   physicalFourier (NlsGge.ThirdConsultation.KSPS.toPotPair φ).2 n)‖)^2) ≤ C^2) :
    ∃ CE1 CE2 : ℝ, ∀ x : PairScale (N : ℝ), ‖x‖ ≤ H →
      pairPotential (N : ℝ) (Nat.cast_nonneg N) x ∈ gkW →
      (∀ F : Finset ℤ, ∑ n ∈ F, (bracket n ^ (N + 1) *
          ‖tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
            muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n +
            (rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2‖) ^ 2 ≤ CE1) ∧
      (∀ F : Finset ℤ, ∑ n ∈ F, (bracket n ^ (N + 1) *
          ‖antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
              (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
            Complex.I * (-1 : ℂ) ^ n *
              (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n)‖) ^ 2 ≤ CE2) := by
  obtain ⟨C1, -, h1⟩ := hmd
  obtain ⟨C2, -, h2⟩ := hat
  refine ⟨C1 ^ 2, C2 ^ 2, fun x hx hW => ?_⟩
  have hB : NlsGge.ThirdConsultation.KSPS.sobolevNorm N (toSobolevCN N x) ≤ 2 ^ N * H :=
    (sobolevNorm_toSobolevCN_le N x).trans (mul_le_mul_of_nonneg_left hx (by positivity))
  exact ⟨fun F => (ksn018_transfer N F _ _ (ksn018_E1_eq N x hW)).trans ((h1 _ hB).2 F),
    fun F => (ksn018_transfer N F _ _ (ksn018_E2_eq N x)).trans ((h2 _ hB).2 F)⟩

end
end NlsGge.ThirdConsultation.KSN
