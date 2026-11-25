import Mathlib
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Birkhoff.BirkhoffInput38
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.GK38.Defs
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.Atomic.G6.G6022
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST043
import NlsGge.Atomic.KST.KST059
import NlsGge.Atomic.KST.KST064
import NlsGge.Atomic.KST.KST030
import NlsGge.Atomic.KST.KST060
import NlsGge.Atomic.KST.KST065
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST033Host

/- G6-023 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/G6/G6023.lean,
   namespace NlsGge.GKDefinitionDesign.  Head VERBATIM from design STATEMENTS/G6.md "## G6-023"
   (byte-identical in gpt6pro_followup1..5,7..10; no Pro round 5-12 entry touches G6-023).  No repair of the head.
   Route (packet skeleton: translate H^m into weighted gap summability via the forward/inverse weighted-gap theorems,
   then gap summability into weighted actions and coordinate norms):
   (1) m = 0: both sequences lie in l^2 = h^0 (u in L2, Phi u in L2Z);
   (2) m >= 1: fourierSeq38 u in h^m  <->  Summable (sobolevModeWeight m n * gap_n^2)
         (=>) KST-030 (kst030) with the polynomial weight (1+|k|)^m, via the doubled-cover energy formula (landed KST065S.energy_realSlice)
              and the pointwise comparison polynomialWeight m (2n)^2 <= 6^m sobolevModeWeight m n;
         (<=) KST-060 (kst060, subexponential case, RealForm 1 (realSlice u)) and landed KST065S.mem_of_energy_lt_top;
       Summable (w * gap^2)  <->  Summable (w * I_n)  by G6-022 (landed G6022);
       Summable (w * I_n)  <->  physicalBirkhoff u in h^m by ||Phi u n||^2 = I_n (X-006 field Phi_action of sourceFamily;
         foundation consumption as in G6-015/G6-009 reviews). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G6023Aux

/-- Pointwise comparison of the doubled polynomial weight with the Sobolev mode weight. -/
theorem poly_two_mul_sq_le (m : ℕ) (n : ℤ) :
    NlsGge.Atomic.KST064.polynomialWeight (m : ℝ) (2 * n) ^ 2 ≤
      (6 : ℝ) ^ (m : ℝ) * sobolevModeWeight (m : ℝ) n := by
  rw [NlsGge.ThirdConsultation.KST.KST065S.polynomialWeight_two_mul_sq,
    NlsGge.ThirdConsultation.KST.KST065S.sobolevModeWeight_eq,
    NlsGge.ThirdConsultation.KST.KST065S.intCast_sq_eq,
    ← Real.mul_rpow (by norm_num) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ (Nat.cast_nonneg m)
  nlinarith [sq_nonneg ((n.natAbs : ℝ) - 1), Nat.cast_nonneg (α := ℝ) n.natAbs]

/-- The norm of the real-slice gap sequence is the real gap width. -/
theorem gapSeq_norm_sq (u : PhysicalL2) (n : ℤ) :
    ‖NlsGge.Atomic.KST059.actualGapSequence (realSlice u) n‖ ^ 2 =
      (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 := by
  unfold NlsGge.Atomic.KST059.actualGapSequence
  rw [(lamPlus_real u n).1, (lamPlus_real u n).2, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Fourier side to gap side: `fourierSeq38 u ∈ h^m` gives weighted gap summability. -/
theorem gap_summable_of_fourier (m : ℕ) (u : PhysicalL2)
    (h : fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) :
    Summable (fun n : ℤ => sobolevModeWeight (m : ℝ) n *
      (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2) := by
  have hs : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hsub := (NlsGge.Atomic.KST064.kst_sobolev_weight_equivalence (m : ℝ) hs).1
  have hSec := NlsGge.ThirdConsultation.KST.KST060S.secondary_of_subexp _ hsub
  have hF : Summable (fun n : ℤ => sobolevModeWeight (m : ℝ) n * ‖fourierSeq38 u n‖ ^ 2) :=
    (mem_seqSobolev38_iff (m : ℝ) (fourierSeq38 u)).1 h
  have hE : NlsGge.Atomic.KST001.weightedNormSq₂ (NlsGge.Atomic.KST064.polynomialWeight (m : ℝ))
      (realSlice u) < ⊤ := by
    rw [NlsGge.ThirdConsultation.KST.KST065S.energy_realSlice _
      (NlsGge.ThirdConsultation.KST.KST065S.polyEven (m : ℝ) hs) u]
    have hle : ∀ k : ℤ, ENNReal.ofReal (NlsGge.Atomic.KST064.polynomialWeight (m : ℝ) (2 * k) ^ 2 *
        ‖fourierSeq38 u k‖ ^ 2) ≤
        ENNReal.ofReal ((6 : ℝ) ^ (m : ℝ) * (sobolevModeWeight (m : ℝ) k * ‖fourierSeq38 u k‖ ^ 2)) := by
      intro k
      apply ENNReal.ofReal_le_ofReal
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (poly_two_mul_sq_le m k) (sq_nonneg _)
    have hnn : ∀ k : ℤ, 0 ≤ (6 : ℝ) ^ (m : ℝ) *
        (sobolevModeWeight (m : ℝ) k * ‖fourierSeq38 u k‖ ^ 2) := fun k =>
      mul_nonneg (by positivity)
        (mul_nonneg ((sobolevModeWeightPositive (m : ℝ)).out k).le (sq_nonneg _))
    have hfin : ∑' k : ℤ, ENNReal.ofReal (NlsGge.Atomic.KST064.polynomialWeight (m : ℝ) (2 * k) ^ 2 *
        ‖fourierSeq38 u k‖ ^ 2) < ⊤ :=
      calc _ ≤ ∑' k : ℤ, ENNReal.ofReal ((6 : ℝ) ^ (m : ℝ) *
              (sobolevModeWeight (m : ℝ) k * ‖fourierSeq38 u k‖ ^ 2)) := ENNReal.tsum_le_tsum hle
        _ = ENNReal.ofReal (∑' k : ℤ, (6 : ℝ) ^ (m : ℝ) *
              (sobolevModeWeight (m : ℝ) k * ‖fourierSeq38 u k‖ ^ 2)) :=
            (ENNReal.ofReal_tsum_of_nonneg hnn (hF.mul_left _)).symm
        _ < ⊤ := ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top (by simp) hfin
  have h030 := NlsGge.ThirdConsultation.KST.kst030 _ hSec.1 hSec.2 (realSlice u) hE
  have hsum := NlsGge.Atomic.KST059.summable_weighted_gap _ _ h030
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg
    ((sobolevModeWeightPositive (m : ℝ)).out n).le (sq_nonneg _)) (fun n => ?_) hsum
  rw [← gapSeq_norm_sq u n]
  exact mul_le_mul_of_nonneg_right
    (NlsGge.ThirdConsultation.KST.KST065S.sobolevModeWeight_le (m : ℝ) hs n) (sq_nonneg _)

/-- Gap side to Fourier side: weighted gap summability gives `fourierSeq38 u ∈ h^m`. -/
theorem fourier_of_gap_summable (m : ℕ) (u : PhysicalL2)
    (h : Summable (fun n : ℤ => sobolevModeWeight (m : ℝ) n *
      (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2)) :
    fourierSeq38 u ∈ seqSobolev38 (m : ℝ) := by
  have hs : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hsub := (NlsGge.Atomic.KST064.kst_sobolev_weight_equivalence (m : ℝ) hs).1
  have hle : ∀ n : ℤ, ENNReal.ofReal (NlsGge.Atomic.KST064.polynomialWeight (m : ℝ) (2 * n) ^ 2 *
      ‖NlsGge.Atomic.KST059.actualGapSequence (realSlice u) n‖ ^ 2) ≤
      ENNReal.ofReal ((6 : ℝ) ^ (m : ℝ) * (sobolevModeWeight (m : ℝ) n *
        (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2)) := by
    intro n
    apply ENNReal.ofReal_le_ofReal
    rw [gapSeq_norm_sq u n, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (poly_two_mul_sq_le m n) (sq_nonneg _)
  have hnn : ∀ n : ℤ, 0 ≤ (6 : ℝ) ^ (m : ℝ) * (sobolevModeWeight (m : ℝ) n *
      (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2) := fun n =>
    mul_nonneg (by positivity)
      (mul_nonneg ((sobolevModeWeightPositive (m : ℝ)).out n).le (sq_nonneg _))
  have hγ : NlsGge.Atomic.KST059.weightedGapEnergy (NlsGge.Atomic.KST064.polynomialWeight (m : ℝ))
      (NlsGge.Atomic.KST059.actualGapSequence (realSlice u)) < ⊤ := by
    unfold NlsGge.Atomic.KST059.weightedGapEnergy
    calc _ ≤ ∑' n : ℤ, ENNReal.ofReal ((6 : ℝ) ^ (m : ℝ) * (sobolevModeWeight (m : ℝ) n *
            (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2)) :=
          ENNReal.tsum_le_tsum hle
      _ = ENNReal.ofReal (∑' n : ℤ, (6 : ℝ) ^ (m : ℝ) * (sobolevModeWeight (m : ℝ) n *
            (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2)) :=
          (ENNReal.ofReal_tsum_of_nonneg hnn (h.mul_left _)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hreal : NlsGge.ThirdConsultation.KST.RealForm 1 (realSlice u) :=
    ⟨Or.inl rfl, by simp [realSlice_snd]⟩
  have h60 := NlsGge.ThirdConsultation.KST.kst060 (realSlice u) 1 hreal _ hγ
  exact NlsGge.ThirdConsultation.KST.KST065S.mem_of_energy_lt_top (m : ℝ) hs u (h60.1 hsub)

/-- Birkhoff side: `physicalBirkhoff u ∈ h^m` is weighted action summability. -/
theorem birkhoff_mem_iff_action (m : ℕ) (u : PhysicalL2) :
    (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ) ↔
      Summable (fun n : ℤ => sobolevModeWeight (m : ℝ) n * actualGapActionAllE02_38 u n) := by
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  refine summable_congr (fun n => ?_)
  change sobolevModeWeight (m : ℝ) n * ‖(sourceFamily.Phi u : ℤ → ℂ) n‖ ^ 2 = _
  rw [sourceFamily.Phi_action u n]

/-- Every `l^2` sequence lies in `h^0`. -/
theorem l2_mem_seqSobolev_zero (x : Lib.L2Z) :
    (x : ℤ → ℂ) ∈ seqSobolev38 ((0 : ℕ) : ℝ) := by
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  have h := Lib.summable_sq_lp x
  refine h.congr (fun n => ?_)
  simp [sobolevModeWeight]

end G6023Aux

theorem G6023 (u : PhysicalL2) (m : ℕ) :
  fourierSeq38 u ∈ seqSobolev38 (m : ℝ) ↔
    (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact iff_of_true (G6023Aux.l2_mem_seqSobolev_zero (reflectedFourierL2 u))
      (G6023Aux.l2_mem_seqSobolev_zero (physicalBirkhoff u))
  · rw [G6023Aux.birkhoff_mem_iff_action m u, G6022 u m hm]
    exact ⟨G6023Aux.gap_summable_of_fourier m u, G6023Aux.fourier_of_gap_summable m u⟩

end
end NlsGge.GKDefinitionDesign
