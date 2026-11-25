import Mathlib
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.Atomic.G6.G6011Sup1Core
import NlsGge.Atomic.G6.G6013Host
import NlsGge.Atomic.G6.G6013Sup1
import NlsGge.Atomic.G6.G6003
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G5.G5011
import NlsGge.Atomic.G5.G5012Sup4
import NlsGge.Atomic.G2.G2040
import NlsGge.Atomic.X.X004

/- G6-014 PACKET (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6014.lean.
   Head `G6014` VERBATIM from followup12 STATEMENTS/G6.md "## G6-014" (CONVENTION_CORRECTION head; round 14 row: retain); G6 shared
   opens. No lexical repair.  Proof (GK Theorem 19.4): analyticity of realBirkhoffCartesian from the G6003 charts; the global
   inverse agrees near each value with a chart inverse (G6011Aux.invFun_analyticOnNhd, bijectivity G6013); the physical map and
   inverse are the Cartesian ones conjugated by the G6013Sup1 bridge CLE; inverse equations from G6013; norms (Parseval, GK
   Prop. 13.4) from G2-040 (HasSum of actions, potNormSq38 = 2 |u|^2), landed realX_sq_add_realY_sq and the X-004 action
   identity |Phi_n|^2 = I_n; Jacobian at 0 = G5011.1.  No X-006 analyticity / derivative field is used. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6014 :
  AnalyticOnNhd ℝ realBirkhoffCartesian Set.univ ∧
  AnalyticOnNhd ℝ inverseBirkhoffCartesian Set.univ ∧
  AnalyticOnNhd ℝ physicalBirkhoff Set.univ ∧
  AnalyticOnNhd ℝ physicalInverseBirkhoff Set.univ ∧
  Function.LeftInverse inverseBirkhoffCartesian realBirkhoffCartesian ∧
  Function.RightInverse inverseBirkhoffCartesian realBirkhoffCartesian ∧
  (∀ u : PhysicalL2, ‖realBirkhoffCartesian u‖^2 = potNormSq38 (realSlice u) ∧
    potNormSq38 (realSlice u) = 2 * ‖u‖^2 ∧ ‖physicalBirkhoff u‖ = ‖u‖) ∧
  fderiv ℝ physicalBirkhoff 0 =
    reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ := by
  obtain ⟨hR, hP, hl, hr, -, -⟩ := G6013
  obtain ⟨e, -, he⟩ := exists_physicalCartesianEquiv
  have hAR : AnalyticOnNhd ℝ realBirkhoffCartesian Set.univ := fun u _ => by
    obtain ⟨U, V, g, -, huU, -, -, hfU, -⟩ := G6003 u
    exact hfU u huU
  have hAI : AnalyticOnNhd ℝ inverseBirkhoffCartesian Set.univ :=
    G6011Aux.invFun_analyticOnNhd realBirkhoffCartesian hR G6003
  have hPeq : ∀ u : PhysicalL2, physicalBirkhoff u = e.symm (realBirkhoffCartesian u) :=
    fun u => by rw [he u, ContinuousLinearEquiv.symm_apply_apply]
  have hAP : AnalyticOnNhd ℝ physicalBirkhoff Set.univ := fun u _ => by
    have h := ((e.symm : CartesianReal →L[ℝ] Lib.L2Z).analyticAt
      (realBirkhoffCartesian u)).comp (hAR u (Set.mem_univ u))
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    exact (hPeq v).symm
  have hIeq : ∀ z : Lib.L2Z, physicalInverseBirkhoff z = inverseBirkhoffCartesian (e z) := by
    intro z
    have hv : physicalBirkhoff (inverseBirkhoffCartesian (e z)) = z := by
      apply e.injective
      rw [← he, hr (e z)]
    calc physicalInverseBirkhoff z
        = physicalInverseBirkhoff (physicalBirkhoff (inverseBirkhoffCartesian (e z))) := by
          rw [hv]
      _ = inverseBirkhoffCartesian (e z) := Function.leftInverse_invFun hP.1 _
  have hAPI : AnalyticOnNhd ℝ physicalInverseBirkhoff Set.univ := fun z _ => by
    have h := (hAI (e z) (Set.mem_univ _)).comp ((e : Lib.L2Z →L[ℝ] CartesianReal).analyticAt z)
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    exact (hIeq w).symm
  refine ⟨hAR, hAI, hAP, hAPI, hl, hr, fun u => ⟨?_, (G2_040.2 u).2.1, ?_⟩, G5011.1⟩
  · have hx : Summable (fun n : ℤ => realX n u ^ 2) := by
      have h := g5012_slice_sq_summable (realBirkhoffCartesian u) true
      simpa [realBirkhoffCartesian_true, Real.norm_eq_abs, sq_abs] using h
    have hy : Summable (fun n : ℤ => realY n u ^ 2) := by
      have h := g5012_slice_sq_summable (realBirkhoffCartesian u) false
      simpa [realBirkhoffCartesian_false, Real.norm_eq_abs, sq_abs] using h
    rw [G6013Aux.cart_norm_sq, (G2_040.2 u).2.1]
    simp only [realBirkhoffCartesian_true, realBirkhoffCartesian_false]
    calc ∑' n : ℤ, realX n u ^ 2 + ∑' n : ℤ, realY n u ^ 2
        = ∑' n : ℤ, (realX n u ^ 2 + realY n u ^ 2) := (hx.tsum_add hy).symm
      _ = ∑' n : ℤ, 2 * actualGapActionAllE02_38 u n :=
          tsum_congr (fun n => realX_sq_add_realY_sq n u)
      _ = 2 * ∑' n : ℤ, actualGapActionAllE02_38 u n := tsum_mul_left
      _ = 2 * ‖u‖ ^ 2 := by rw [(G2_040.2 u).1.tsum_eq]
  · have hsq : ‖physicalBirkhoff u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [G6013Aux.l2z_norm_sq]
      calc ∑' n : ℤ, ‖physicalBirkhoff u n‖ ^ 2
          = ∑' n : ℤ, actualGapActionAllE02_38 u n :=
            tsum_congr (fun n => (NlsGge.Atomic.X004.samePhi_cartesian_normalization u n).2.2.2.2.2)
        _ = ‖u‖ ^ 2 := (G2_040.2 u).1.tsum_eq
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

end
end NlsGge.GKDefinitionDesign
