import Mathlib
import NlsGge.Spectral.F04Lemma38
import NlsGge.Birkhoff.F05Identity38
import NlsGge.NLS38.PhysicalFlow38

                                                                                                 
                                                                                           
                                                                                                 
                                                                                                          
                                                                                                           
                                                                                                               
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.F009Aux

/-- The true inclusion `H^m → H^{m-1}` keeps every Fourier coefficient. -/
theorem lower_coeff (m : ℕ) (y : SobolevHilbert (m : ℝ)) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      ofCarrier38 _ (NlsGge.Birkhoff.carrierIncl38
        (show ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) from Nat.cast_le.mpr (Nat.sub_le m 1))
        (toCarrier38 _ y))) n =
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n :=
  congrFun (carrierCoe38_incl38 _ (toCarrier38 _ y)) n

/-- Equal Fourier coefficients give the same `L²` field. -/
theorem sobolevToL2_eq (m : ℕ) (y : SobolevHilbert (m : ℝ))
    (y' : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hy' : ∀ n, (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n) :
    sobolevToL2_38 (m - 1) y' = sobolevToL2_38 m y :=
  NlsGge.NLS38.physicalFourier_injective38 (funext fun n => by
    rw [sobolevToL2_38_fourier, sobolevToL2_38_fourier]; exact (hy' n).symm)

theorem core (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (Φ : PhysicalL2 → ℤ → ℂ)
    (hact : ∀ (u : PhysicalL2) (n : ℤ), actualGapActionAllE02_38 u n = ‖Φ u n‖ ^ 2)
    (y : SobolevHilbert (m : ℝ)) (y' : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hy' : ∀ n, (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n) :
    Summable (fun n : ℤ => finiteHierarchyRate38 m β n * ‖Φ (sobolevToL2_38 m y) n‖ ^ 2) ∧
    Summable (fun n : ℤ => finiteHierarchyRate38 m β n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) ∧
    Summable (fun n : ℤ => |gapRemainderTermE02_38 (finiteWeightE02_38 m β)
      (sobolevToL2_38 m y) n|) ∧
    energySobolev38 m β y =
      (∑' n : ℤ, finiteHierarchyRate38 m β n * ‖Φ (sobolevToL2_38 m y) n‖ ^ 2) +
        Rm38 m β y' ∧
    energySobolev38 m β y =
      (∑' n : ℤ, finiteHierarchyRate38 m β n *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2) + Vm38 m β y' := by
  obtain ⟨h1, -, h3⟩ := F04_spectral_lemma38 m hm β hβ
  obtain ⟨hsA, -, hE1, hsF, -, hE2⟩ := h3 y
  have hu := sobolevToL2_eq m y y' hy'
  have hfun : (fun n : ℤ => finiteWeightE02_38 m β (2 * Real.pi * (n : ℝ)) *
      actualGapActionAllE02_38 ((sobolevToL2_38 m) y) n) =
      fun n : ℤ => finiteHierarchyRate38 m β n * ‖Φ (sobolevToL2_38 m y) n‖ ^ 2 :=
    funext fun n => by rw [hact]; rfl
  refine ⟨Eq.mp (congrArg Summable hfun) hsA, hsF, ?_, ?_, ?_⟩
  · have h := (h1 y').1
    rwa [hu] at h
  · refine hE1.trans ?_
    have hR : (∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β)
        ((sobolevToL2_38 m) y) n) = Rm38 m β y' := by
      unfold Rm38
      rw [hu]
    exact congrArg₂ (· + ·) (congrArg tsum hfun) hR
  · exact hE2 y' hy'

end NlsGge.ThirdConsultation.F009Aux
