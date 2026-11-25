import Mathlib
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.ThirdConsultation.G2.HigherActionOne
import NlsGge.Atomic.LIB.LIB086
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

                                                                                                     
                                                                                                     
                                                                                                        
                                                                                                     
                                                                                        
                                                                                                  
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.M
noncomputable section

abbrev PotentialR := PhysicalL2

def action (u : PhysicalL2) (n : ℤ) : ℝ :=
  actualGapActionAllE02_38 u n

def molnarWeight (m : ℕ) (n : ℤ) : ℝ :=
  (1 + |2*Real.pi*(n:ℝ)|)^m

def actionWeightedSum (m : ℕ) (u : PhysicalL2) : ℝ :=
  ∑' n : ℤ, molnarWeight m n^2 * action u n

def molnarBirkhoff (u : PhysicalL2) : NlsGge.GKDefinitionDesign.CartesianReal :=
  NlsGge.GKDefinitionDesign.realBirkhoffCartesian u

def realSeqNorm (m : ℕ)
    (z : NlsGge.GKDefinitionDesign.CartesianReal) : ℝ :=
  Real.sqrt (∑' n : ℤ, molnarWeight m n^2 *
    (z (true,n)^2 + z (false,n)^2))

def higherAction (u : PhysicalL2) (n : ℤ) (k : ℕ) : ℝ :=
  if hk : 1 ≤ k then
    ((k:ℝ)⁻¹ : ℝ) *
      (NlsGge.GKDefinitionDesign.higherAction k (realSlice u) n).re
  else 0

def actionWeightedSumENNReal (m : ℕ) (u : PhysicalL2) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (molnarWeight m n ^ 2 * action u n)

def realSeqNormSqENNReal (m : ℕ)
    (z : NlsGge.GKDefinitionDesign.CartesianReal) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal
    (molnarWeight m n ^ 2 * (z (true, n)^2 + z (false, n)^2))

theorem molnarPoint_identity (u : PhysicalL2) (m : ℕ) (n : ℤ) :
    molnarWeight m n ^ 2 * (molnarBirkhoff u (true, n) ^ 2 + molnarBirkhoff u (false, n) ^ 2) =
      2 * (molnarWeight m n ^ 2 * action u n) := by
  rw [molnarBirkhoff, NlsGge.GKDefinitionDesign.realBirkhoffCartesian_true,
    NlsGge.GKDefinitionDesign.realBirkhoffCartesian_false]
  have h' := NlsGge.GKDefinitionDesign.realX_sq_add_realY_sq n u
  unfold action
  linear_combination (molnarWeight m n ^ 2) * h'

theorem molnar_action_norm (u : PotentialR) (m : ℕ) :
  realSeqNormSqENNReal m (molnarBirkhoff u) =
      2 * actionWeightedSumENNReal m u ∧
  (∀ n : ℤ, action u n = higherAction u n 1) ∧
  (∀ n : ℤ, ∀ k : ℕ, 1 ≤ k →
    higherAction u n k =
      ((k : ℝ)⁻¹ *
        (NlsGge.GKDefinitionDesign.higherAction k (realSlice u) n).re)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold realSeqNormSqENNReal actionWeightedSumENNReal
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [molnarPoint_identity, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat]
  · intro n
    unfold action NlsGge.ThirdConsultation.M.higherAction
    rw [dif_pos (le_refl (1 : ℕ))]
    rw [NlsGge.GKDefinitionDesign.higherAction_one_re_eq_action]
    simp
  · intro n k hk
    unfold NlsGge.ThirdConsultation.M.higherAction
    rw [dif_pos hk]

theorem molnar_action_norm_finite
    (u : PotentialR) (m : ℕ)
    (hfinite : actionWeightedSumENNReal m u ≠ ⊤) :
  Summable (fun n : ℤ => molnarWeight m n ^ 2 * action u n) ∧
  Summable (fun n : ℤ => molnarWeight m n ^ 2 *
    ((molnarBirkhoff u) (true, n)^2 +
      (molnarBirkhoff u) (false, n)^2)) ∧
  ENNReal.ofReal (actionWeightedSum m u) =
    actionWeightedSumENNReal m u ∧
  ENNReal.ofReal (realSeqNorm m (molnarBirkhoff u)^2) =
    realSeqNormSqENNReal m (molnarBirkhoff u) ∧
  realSeqNorm m (molnarBirkhoff u)^2 =
    2 * actionWeightedSum m u := by
  have hnn : ∀ n : ℤ, 0 ≤ molnarWeight m n ^ 2 * action u n := fun n =>
    mul_nonneg (sq_nonneg _) (NlsGge.GKDefinitionDesign.realActionNonneg38 u n)
  have hsum : Summable (fun n : ℤ => molnarWeight m n ^ 2 * action u n) :=
    NlsGge.Atomic.LIB086.summable_of_tsum_ofReal_ne_top hnn hfinite
  have hterm : ∀ n : ℤ, 0 ≤ molnarWeight m n ^ 2 *
      ((molnarBirkhoff u) (true, n)^2 + (molnarBirkhoff u) (false, n)^2) := fun n =>
    mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hsum2 : Summable (fun n : ℤ => molnarWeight m n ^ 2 *
      ((molnarBirkhoff u) (true, n)^2 + (molnarBirkhoff u) (false, n)^2)) := by
    have hfun : (fun n : ℤ => molnarWeight m n ^ 2 *
        ((molnarBirkhoff u) (true, n)^2 + (molnarBirkhoff u) (false, n)^2)) =
        fun n : ℤ => 2 * (molnarWeight m n ^ 2 * action u n) :=
      funext fun n => molnarPoint_identity u m n
    rw [hfun]
    exact hsum.mul_left 2
  have hS : 0 ≤ ∑' n : ℤ, molnarWeight m n ^ 2 *
      ((molnarBirkhoff u) (true, n)^2 + (molnarBirkhoff u) (false, n)^2) :=
    tsum_nonneg hterm
  refine ⟨hsum, hsum2, ?_, ?_, ?_⟩
  · unfold actionWeightedSum actionWeightedSumENNReal
    exact ENNReal.ofReal_tsum_of_nonneg hnn hsum
  · unfold realSeqNorm realSeqNormSqENNReal
    rw [Real.sq_sqrt hS]
    exact ENNReal.ofReal_tsum_of_nonneg hterm hsum2
  · unfold realSeqNorm actionWeightedSum
    rw [Real.sq_sqrt hS, tsum_congr (fun n => molnarPoint_identity u m n), tsum_mul_left]

end
end NlsGge.ThirdConsultation.M

