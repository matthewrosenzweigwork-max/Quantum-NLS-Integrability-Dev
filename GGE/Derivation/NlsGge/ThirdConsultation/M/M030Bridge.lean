import Mathlib
import NlsGge.ThirdConsultation.KST.KST029Bridge
import NlsGge.ThirdConsultation.M.M029Host
import NlsGge.ThirdConsultation.M.MW1Power
import NlsGge.ThirdConsultation.M.MW2Series
import NlsGge.ThirdConsultation.M.MRound11Elim
import NlsGge.ThirdConsultation.M.M030Label
import NlsGge.Atomic.KST.KST013
import NlsGge.GK38.IsolatingDefs

/-!
# M-030 / M-031 support: the `perChar`/`schurDet` bridge and the thresholded label identification
(proof development, AUTHOR; not self-reviewed)

`perChar_zero_schurDet_zero`: under the weighted source threshold, a zero of the periodic characteristic in the strip
is a zero of the Schur determinant.  Route: landed `KST029Bridge.perChar_to_diracEigen` gives a nonzero eigenvector of
`dirac (schurPhysicalPair ψ)` (no parity sector is claimed); the parity-free forward half of the landed
`MW2Elim.periodicEigenvalue_iff_det_core_w` (graph identity, `P_n f ≠ 0`, forward reduced formula; the inverse of
`1 - T` from `MW1Power.summable_sq_powers_of_weighted` and `MW2Series.inverse_one_sub_of_sq_summable`), then the landed
`raw_iff_kernel` and `kernel_iff_det`.  The three KST013 lemma statements enter the core as the Prop-valued arguments
`ElimAC/ElimG/ElimK` (the `MW2Elim` convention) and are instantiated with the landed public KST013 lemmas.

`periodic_labels_are_local_roots` = `M030Label.periodic_labels_are_local_roots_of_bridge` with this bridge.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.GK38 NlsGge.Atomic.KST003 NlsGge.ThirdConsultation.MTwoModeSupp

/-- Parity-free forward half of `MW2Elim.periodicEigenvalue_iff_det_core_w`: a nonzero eigenvector of
`dirac (schurPhysicalPair ψ)` at a strip point of a thresholded pair forces `schurDet = 0`. -/
theorem schurDet_zero_of_eigen_core (hAC : ElimAC) (hG : ElimG) (hK : ElimK)
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (ψ : PotPair)
    (hψ : MTwoMode.potentialCoefficientEnergy w ψ ≠ ⊤) (m : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w ψ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight m)
    (z : ℂ) (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip m)
    (F : (NlsGge.Atomic.KST013.dirac (MTwoMode.schurPhysicalPair ψ)).domain)
    (hFne : (F : KSTPairL2) ≠ 0)
    (heq : NlsGge.Atomic.KST013.dirac (MTwoMode.schurPhysicalPair ψ) F = z • (F : KSTPairL2)) :
    MTwoMode.schurDet ψ m z hz = 0 := by
  have hT := NlsGge.ThirdConsultation.MTwoModeW.summable_sq_powers_of_weighted
    w hw ψ hψ m z hz hthreshold
  have hT' : Summable fun j : ℕ =>
      ‖(NlsGge.Atomic.KST006.qOperator (MTwoMode.schurPhysicalPair ψ) m z hz ^ 2) ^ j‖ := hT
  obtain ⟨hunit, _, _, _⟩ := NlsGge.ThirdConsultation.MTwoModeW.inverse_one_sub_of_sq_summable
    (NlsGge.Atomic.KST006.qOperator (MTwoMode.schurPhysicalPair ψ) m z hz) hT'
  have hdirac : NlsGge.Atomic.KST013.dirac (MTwoMode.schurPhysicalPair ψ) F =
      -NlsGge.Schur.actualFullPeriodTwoDoubledCirclePerturbedDiracAction
        (-(MTwoMode.schurPhysicalPair ψ true)) (-(MTwoMode.schurPhysicalPair ψ false))
        ⟨(F : KSTPairL2), F.property⟩ := rfl
  have hact : NlsGge.Schur.actualFullPeriodTwoDoubledCirclePerturbedDiracAction
      (-(MTwoMode.schurPhysicalPair ψ true)) (-(MTwoMode.schurPhysicalPair ψ false))
      ⟨(F : KSTPairL2), F.property⟩ = -(z • (F : KSTPairL2)) := by
    rw [hdirac] at heq
    exact neg_eq_iff_eq_neg.mp heq
  obtain ⟨g, hgraph, hprod⟩ :=
    (hAC (MTwoMode.schurPhysicalPair ψ) (F : KSTPairL2) (z • (F : KSTPairL2))).2
      ⟨F.property, hact⟩
  have hpne : spectralPn m (F : KSTPairL2) ≠ 0 := fun h =>
    hFne (hG (MTwoMode.schurPhysicalPair ψ) m z hz (F : KSTPairL2) g hgraph hprod hunit h)
  have hi : spectralPn m (spectralPn m (F : KSTPairL2)) = spectralPn m (F : KSTPairL2) := by
    have hi := congrArg (fun S : KSTPairL2 →L[ℂ] KSTPairL2 => S (F : KSTPairL2))
      (spectralPn_idempotent m)
    simpa only [ContinuousLinearMap.comp_apply] using hi
  exact (kernel_iff_det ψ m z hz).1
    ((raw_iff_kernel (MTwoMode.schurPhysicalPair ψ) m z hz).1
      ⟨spectralPn m (F : KSTPairL2), hpne, hi,
        hK (MTwoMode.schurPhysicalPair ψ) m z hz (F : KSTPairL2) g hgraph hprod hunit⟩)

theorem perChar_zero_schurDet_zero_core (hAC : ElimAC) (hG : ElimG) (hK : ElimK)
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (ψ : PotPair)
    (hψ : MTwoMode.potentialCoefficientEnergy w ψ ≠ ⊤) (m : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w ψ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight m)
    (z : ℂ) (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip m) (h0 : perChar ψ z = 0) :
    MTwoMode.schurDet ψ m z hz = 0 := by
  have hP : NlsGge.ThirdConsultation.KST.periodicPair (MTwoMode.schurPhysicalPair ψ) = ψ := rfl
  obtain ⟨F, hFne, heq⟩ := NlsGge.ThirdConsultation.KST.KST029Bridge.perChar_to_diracEigen
    (MTwoMode.schurPhysicalPair ψ) z (by rw [hP]; exact h0)
  exact schurDet_zero_of_eigen_core hAC hG hK w hw ψ hψ m hthreshold z hz F hFne heq

theorem perChar_zero_schurDet_zero
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (ψ : PotPair)
    (hψ : MTwoMode.potentialCoefficientEnergy w ψ ≠ ⊤) (m : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w ψ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight m)
    (z : ℂ) (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip m) (h0 : perChar ψ z = 0) :
    MTwoMode.schurDet ψ m z hz = 0 :=
  perChar_zero_schurDet_zero_core
    NlsGge.Atomic.KST013.stage13AC_actual_proper_operator_graph_iff
    NlsGge.Atomic.KST013.stage13G_projection_zero_forces_zero
    NlsGge.Atomic.KST013.stage13K_actual_forward_reduced_formula
    w hw ψ hψ m hthreshold z hz h0

theorem periodic_labels_are_local_roots
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair) (hW : φ ∈ gkW)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤) (n : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    ∃ (h1 : lamMinus φ n ∈ NlsGge.Atomic.KST004.spectralStrip n)
      (h2 : lamPlus φ n ∈ NlsGge.Atomic.KST004.spectralStrip n),
      lamMinus φ n ∈ MTwoMode.localSpectralDisc w φ n ∧ lamPlus φ n ∈ MTwoMode.localSpectralDisc w φ n ∧
      MTwoMode.schurDet φ n (lamMinus φ n) h1 = 0 ∧ MTwoMode.schurDet φ n (lamPlus φ n) h2 = 0 :=
  periodic_labels_are_local_roots_of_bridge w hw φ hφ n hthreshold
    (fun ψ hψ m hm z hz h0 => perChar_zero_schurDet_zero w hw ψ hψ m hm z hz h0)

end NlsGge.ThirdConsultation.M

end
