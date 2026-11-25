import Mathlib
import NlsGge.Atomic.T.T009
import NlsGge.Atomic.T.T016
import NlsGge.Atomic.T.T017
import NlsGge.Birkhoff.F11Claim38
import NlsGge.Birkhoff.F11Claim38b
import NlsGge.Birkhoff.F11Claim38c
import NlsGge.Birkhoff.S04Moments38d
import NlsGge.Hierarchy.UniformPartitionBound38
import NlsGge.ThirdConsultation.T.TDefsHost
import NlsGge.ThirdConsultation.T.TDefs2Host

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem fullFourier_finiteCharge_exp_uniform
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (J : ℕ) (t : ℕ → ℝ) (ht : TiltAdmissible38 c J t) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      Integrable (fun u : PhysicalL2 => Real.exp
        (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 (max 2 (J + 1)) j u))
        (fullFourierLaw c N) ∧
      (∫ u : PhysicalL2, Real.exp
        (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 (max 2 (J + 1)) j u)
          ∂fullFourierLaw c N) ≤ C := by
  let cTilt : BoundedCoefficients (tiltLower38 c J t) up :=
    tiltedCoefficients38 c ht
  have hTiltLower : 0 < tiltLower38 c J t := tiltLower38_pos c ht
  have hTiltUpper : tiltLower38 c J t ≤ up := cTilt.property.2.1
  obtain ⟨Cpart, hCpartPos, hCpart⟩ :=
    uniformRelativePartition_bound38 (tiltLower38 c J t) up hTiltLower hTiltUpper
  have hNumeratorUpper : ∀ N : ℕ, relativePartition38 cTilt N ≤ Cpart :=
    fun N => hCpart cTilt N
  obtain ⟨_, _, ⟨zmin, hzminPos, hzminBound⟩⟩ :=
    fullFourier_normalizers_limit_lower lo up c
  have hDenominatorLower : ∀ N : ℕ, zmin ≤ relativePartition38 c N := by
    intro N
    simpa [relativePartition] using hzminBound N
  obtain ⟨_, _, _, ⟨D, hDPos, _, hDBound⟩⟩ :=
    finiteChargeTilt_product_limit lo up c J t ht
  let m : ℕ := max 2 (J + 1)
  have hm : 2 ≤ m := le_max_left 2 (J + 1)
  have hJm : J ≤ m := le_trans (Nat.le_succ J) (le_max_right 2 (J + 1))
  refine ⟨Cpart / (D * zmin), div_pos hCpartPos (mul_pos hDPos hzminPos), ?_⟩
  intro N
  have hExact := NlsGge.Birkhoff.exact_identity38 c ht m hm hJm N
  refine ⟨?_, ?_⟩
  · simpa [fullFourierLaw, m] using hExact.1
  · have hIntegral :
        (∫ u : PhysicalL2, Real.exp
          (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 (max 2 (J + 1)) j u)
            ∂fullFourierLaw c N) =
          (tiltDet38 c J t N)⁻¹ *
            (relativePartition38 cTilt N / relativePartition38 c N) := by
      simpa [fullFourierLaw, cTilt, m] using hExact.2
    have hDetPos : 0 < tiltDet38 c J t N :=
      lt_of_lt_of_le hDPos (hDBound N).1
    have hBasePos : 0 < relativePartition38 c N := relativePartition38_pos c N
    have hTiltedNumeratorNonneg : 0 ≤ relativePartition38 cTilt N :=
      (relativePartition38_pos cTilt N).le
    have hDenominatorProduct :
        D * zmin ≤ tiltDet38 c J t N * relativePartition38 c N := by
      calc
        D * zmin ≤ tiltDet38 c J t N * zmin :=
          mul_le_mul_of_nonneg_right (hDBound N).1 hzminPos.le
        _ ≤ tiltDet38 c J t N * relativePartition38 c N :=
          mul_le_mul_of_nonneg_left (hDenominatorLower N) hDetPos.le
    have hCrossMultiply :
        relativePartition38 cTilt N * (D * zmin) ≤
          Cpart * (tiltDet38 c J t N * relativePartition38 c N) := by
      calc
        relativePartition38 cTilt N * (D * zmin) ≤ Cpart * (D * zmin) :=
          mul_le_mul_of_nonneg_right (hNumeratorUpper N)
            (mul_nonneg hDPos.le hzminPos.le)
        _ ≤ Cpart * (tiltDet38 c J t N * relativePartition38 c N) :=
          mul_le_mul_of_nonneg_left hDenominatorProduct hCpartPos.le
    have hRatioBound :
        relativePartition38 cTilt N /
            (tiltDet38 c J t N * relativePartition38 c N) ≤
          Cpart / (D * zmin) := by
      apply (div_le_div_iff₀ (mul_pos hDetPos hBasePos)
        (mul_pos hDPos hzminPos)).2
      exact hCrossMultiply
    calc
      (∫ u : PhysicalL2, Real.exp
        (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 (max 2 (J + 1)) j u)
          ∂fullFourierLaw c N) =
        (tiltDet38 c J t N)⁻¹ *
          (relativePartition38 cTilt N / relativePartition38 c N) := hIntegral
      _ = relativePartition38 cTilt N /
          (tiltDet38 c J t N * relativePartition38 c N) := by
        field_simp [ne_of_gt hDetPos, ne_of_gt hBasePos] <;> ring
      _ ≤ Cpart / (D * zmin) := hRatioBound

end
end NlsGge.ThirdConsultation.T
