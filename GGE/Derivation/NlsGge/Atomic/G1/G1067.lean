import Mathlib
import NlsGge.GK38.GradFundamentalStar
import NlsGge.GK38.PoissonMixedNormingMutual
import NlsGge.ThirdConsultation.G1.G1WronskianHost

/- G1-067 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1067.lean.
   CORRECTED TARGET: head is Pro rounds 7-8 77c4e4d3 section 16 (plus-i potential sign), names and
   opens taken from Pro. The printed Pro-round-6 sign is refuted; statement_status "corrected_target".
   Proof body: Work/isolated_20261027/proof development/G1067_CORR01.lean (compiled), adapted by renames only:
   G1_067_corrected -> G1_067, twoPotentialWronskianRhsCorrected -> twoPotentialWronskianRhs,
   solution_eq_state made private, and wedge/symmetricPair/bilinearPair taken from the shared host
   NlsGge.ThirdConsultation.G1.G1WronskianHost (not redeclared here).
   Extra open (not in Pro section 16, needed for state_isPairSolution38): NlsGge.GK38.PoissonMixed38. -/
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38
open NlsGge.GK38.PoissonMixed38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

def solution (φ : PotPair) (z : ℂ)
    (a : PairVec38) (t : ℝ) : PairVec38 :=
  (Set.IccExtend zero_le_one (fundPair φ z) t) *ᵥ a

def twoPotentialWronskianRhs (φ ψ : PotPair) (μ ν : ℂ)
    (a b : PairVec38) (t : ℝ) : ℂ :=
  -Complex.I * (μ - ν) *
      symmetricPair (solution φ μ a t) (solution ψ ν b t) +
    Complex.I *
      bilinearPair
        (starProd38 (solution φ μ a t) (solution ψ ν b t))
        ![potRepFst38 φ t - potRepFst38 ψ t,
          potRepSnd38 φ t - potRepSnd38 ψ t]

private theorem solution_eq_state (φ : PotPair) (z : ℂ) (a : PairVec38) (s : ℝ) :
    solution φ z a s = pairKernelExt38 (state φ z a) s := by
  funext i
  rw [state_ext]
  simp only [solution, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have : ext38 (fundContP φ z) s = Set.IccExtend zero_le_one (fundPair φ z) s := rfl
  rw [this]
  ring

theorem G1_067 (φ ψ : PotPair) (μ ν : ℂ) (a b : PairVec38) :
    IntervalIntegrable
      (twoPotentialWronskianRhs φ ψ μ ν a b) volume 0 1 ∧
    (∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) 1),
      HasDerivAt
        (fun s : ℝ =>
          wedge (solution φ μ a s) (solution ψ ν b s))
        (twoPotentialWronskianRhs φ ψ μ ν a b t) t) := by
  have ha := state_isPairSolution38 φ μ a
  have hb := state_isPairSolution38 ψ ν b
  set A := pairKernelExt38 (state φ μ a) with hA
  set B := pairKernelExt38 (state ψ ν b) with hB
  have hsA : ∀ s, solution φ μ a s = A s := solution_eq_state φ μ a
  have hsB : ∀ s, solution ψ ν b s = B s := solution_eq_state ψ ν b
  have hrhs : twoPotentialWronskianRhs φ ψ μ ν a b = fun t =>
      -Complex.I * (μ-ν) * (A t 0 * B t 1 + A t 1 * B t 0) +
      Complex.I * ((A t 1 * B t 1) * (potRepFst38 φ t - potRepFst38 ψ t) +
        (A t 0 * B t 0) * (potRepSnd38 φ t - potRepSnd38 ψ t)) := by
    funext t
    simp only [twoPotentialWronskianRhs, symmetricPair, bilinearPair, starProd38, hsA, hsB,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hfun : (fun s : ℝ => wedge (solution φ μ a s) (solution ψ ν b s)) =
      fun s => A s 0 * B s 1 - A s 1 * B s 0 := by
    funext s; simp only [wedge, hsA, hsB]
  have hcA : Continuous A := continuous_pairKernelExt38 _
  have hcB : Continuous B := continuous_pairKernelExt38 _
  have hA0 : Continuous fun t => A t 0 := (continuous_apply 0).comp hcA
  have hA1 : Continuous fun t => A t 1 := (continuous_apply 1).comp hcA
  have hB0 : Continuous fun t => B t 0 := (continuous_apply 0).comp hcB
  have hB1 : Continuous fun t => B t 1 := (continuous_apply 1).comp hcB
  have hsub : Set.uIcc (0 : ℝ) 1 ⊆ Set.uIcc (0 : ℝ) 2 := by
    rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have hf1 : IntervalIntegrable (potRepFst38 φ - potRepFst38 ψ) volume 0 1 :=
    ((intervalIntegrable_coverRep38_two φ.1).sub (intervalIntegrable_coverRep38_two ψ.1)).mono_set hsub
  have hf2 : IntervalIntegrable (potRepSnd38 φ - potRepSnd38 ψ) volume 0 1 :=
    ((intervalIntegrable_coverRep38_two φ.2).sub (intervalIntegrable_coverRep38_two ψ.2)).mono_set hsub
  have hae : ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivAt (fun s : ℝ => A s 0 * B s 1 - A s 1 * B s 0)
        (-Complex.I * (μ-ν) * (A s 0 * B s 1 + A s 1 * B s 0) +
          Complex.I * ((A s 1 * B s 1) * (potRepFst38 φ s - potRepFst38 ψ s) +
            (A s 0 * B s 0) * (potRepSnd38 φ s - potRepSnd38 ψ s))) s := by
    filter_upwards [ha.2 0, ha.2 1, hb.2 0, hb.2 1] with s ha0 ha1 hb0 hb1 hs
    have h := ((ha0 hs).mul (hb1 hs)).sub ((ha1 hs).mul (hb0 hs))
    refine h.congr_deriv ?_
    simp [zsCoeffPot38, zsCoeffPair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  constructor
  · rw [hrhs]
    have e1 : IntervalIntegrable (fun t => -Complex.I * (μ-ν) * (A t 0 * B t 1 + A t 1 * B t 0)) volume 0 1 :=
      ((Continuous.mul continuous_const ((hA0.mul hB1).add (hA1.mul hB0))).intervalIntegrable 0 1)
    have e2 : IntervalIntegrable (fun t => (A t 1 * B t 1) * (potRepFst38 φ t - potRepFst38 ψ t)) volume 0 1 :=
      hf1.continuousOn_mul (hA1.mul hB1).continuousOn
    have e3 : IntervalIntegrable (fun t => (A t 0 * B t 0) * (potRepSnd38 φ t - potRepSnd38 ψ t)) volume 0 1 :=
      hf2.continuousOn_mul (hA0.mul hB0).continuousOn
    exact e1.add ((e2.add e3).const_mul Complex.I)
  · rw [hfun, hrhs]
    exact (ae_restrict_iff' measurableSet_Ioo).2
      (hae.mono fun s h hs => h ⟨hs.1.le, hs.2.le⟩)

end
end NlsGge.GKDefinitionDesign
