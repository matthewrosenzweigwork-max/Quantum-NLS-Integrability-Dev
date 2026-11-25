import Mathlib
import NlsGge.Atomic.G6.G6028Sup2Core
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.Atomic.G4.G4036Host
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.X.X006
import Armstrong.Work.ActualCartesianRealTraceAction
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Sobolev.PeriodicBridge

/- G6-028 SUPPORT 3 CORE (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6028Sup3Core.lean, namespace NlsGge.GKDefinitionDesign.G6028Aux.
   Assembly of the G6-028 head (GK §20.2 physical normalization) with every landed input as an explicit hypothesis whose
   type is the landed conclusion VERBATIM (discharged one-to-one in the G6028 glue):
     hcart = G6013Sup1 physicalBirkhoff_eq_cartesian (round-14 cluster 6 bridge, reused, not reproved);
     hX004 = X004.samePhi_cartesian_normalization; hZminus = G4014Aux.cartZ_minus; h5011 = G5011; h5012 = G5012;
     hcoord = gradient_physicalCoordinate (G5012Sup3); hstar/hfre = G5032Sup1.star_pairGradientCLM_snd/fderiv_realSlice_im;
     h4040 = G4040; h5040 = G5040; h6002 = G6002.
   Clause 1: hcart; Phi_formula form via hZminus on gkW (real slice lies in sourceBetaW ⊆ W ⊆ gkW); action = X004 conjunct 6.
   Clause 2: sourceFamily.Phi_mass (landed X-006 record field of the same selected family).
   Clause 3: G6028Aux.core6028 (G6028Sup2Core) with the core6001 inputs as in landed G6001 and injectivity from G6002.
   Clauses 4/5: G5011 and reflectedFourierL2_apply (reflected sign convention -û(-n)).
   KSN-001 is NOT consumed: the head's symplectic clause is real-only and follows from the real canonical relations G5040. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G6028Aux
noncomputable section

theorem assemble6028
    (hcart : ∀ (u : PhysicalL2) (n : ℤ),
      physicalBirkhoff u n =
        (cartesianX n (realSlice u) - Complex.I * cartesianY n (realSlice u)) /
          (Real.sqrt 2 : ℂ))
    (hX004 : ∀ (u : PhysicalL2) (n : ℤ),
      (cartesianX n (realSlice u)).im = 0 ∧
      (cartesianY n (realSlice u)).im = 0 ∧
      sourceFamily.Phi u n =
        (cartesianX n (realSlice u) -
          Complex.I * cartesianY n (realSlice u)) /
          (Real.sqrt 2 : ℂ) ∧
      sourceFamily.Phi u n =
        (xiN38 n (realSlice u) / 2) *
          (gk16ActualScalarZMinus38 sourceF n (realSlice u) *
            Complex.exp (-Complex.I * betaSum n (realSlice u))) ∧
      ‖sourceFamily.Phi u n‖^2 =
        ((cartesianX n (realSlice u)).re^2 +
          (cartesianY n (realSlice u)).re^2) / 2 ∧
      ‖sourceFamily.Phi u n‖^2 =
        actualGapActionAllE02_38 u n)
    (hZminus : ∀ (n : ℤ) (φ : PotPair) (hgk : φ ∈ gkW),
      cartesianZExtended n (-1) φ = gk16ActualScalarZMinus38 sourceF n φ)
    (h5011 : fderiv ℝ physicalBirkhoff 0 =
      reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ ∧
      (∀ h : PhysicalL2, ‖fderiv ℝ physicalBirkhoff 0 h‖ = ‖h‖) ∧
      (∀ (h : PhysicalL2) (n : ℤ),
        fderiv ℝ realBirkhoffCartesian 0 h (true, n) =
          Real.sqrt 2 * (reflectedFourierL2 h n).re ∧
        fderiv ℝ realBirkhoffCartesian 0 h (false, n) =
          -Real.sqrt 2 * (reflectedFourierL2 h n).im) ∧
      (∀ h : PhysicalL2, ‖fderiv ℝ realBirkhoffCartesian 0 h‖^2 = 2 * ‖h‖^2))
    (h5012 : Continuous jacobianConjugate ∧ Continuous jacobianAdjoint ∧
      ∀ (u : PhysicalL2) (j : Bool × ℤ),
        jacobianAdjoint u (physicalFourierBasis j) = gradient (physicalCoordinate j) u)
    (hcoord : ∀ (u : PhysicalL2) (j : Bool × ℤ),
      gradient (physicalCoordinate j) u =
        if j.1 then
          (1 / Real.sqrt 2 : ℝ) •
            pairGradientProjection (pairGradient (cartesianX j.2) (realSlice u))
        else
          (-1 / Real.sqrt 2 : ℝ) •
            pairGradientProjection (pairGradient (cartesianY j.2) (realSlice u)))
    (hstar : ∀ (L : PotPair →L[ℂ] ℂ)
      (hL : ∀ a : PhysicalL2, (L (realSlice a)).im = 0),
      star (pairGradientCLM L).2 = (pairGradientCLM L).1)
    (hfre : ∀ (h : PotPair → ℂ) (hr : ∀ w : PhysicalL2, (h (realSlice w)).im = 0)
      (u a : PhysicalL2), (fderiv ℂ h (realSlice u) (realSlice a)).im = 0)
    (h4040 : ∀ (u : PhysicalL2) (n : ℤ),
      (cartesianX n (realSlice u)).im = 0 ∧
      (cartesianY n (realSlice u)).im = 0 ∧
      (actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n →
        cartesianZExtended n 1 (realSlice u) = 0 ∧
        cartesianZExtended n (-1) (realSlice u) = 0))
    (h5040 : ∀ (u : PhysicalL2) (m n : ℤ),
      pairPoisson (cartesianX m) (cartesianX n) (realSlice u) = 0 ∧
      pairPoisson (cartesianX m) (cartesianY n) (realSlice u) =
        -(if m = n then (1 : ℂ) else 0) ∧
      pairPoisson (cartesianY m) (cartesianY n) (realSlice u) = 0)
    (h6002 : ∀ (u : PhysicalL2),
      (∃ e : PhysicalL2 ≃L[ℝ] Lib.L2Z,
        e.toContinuousLinearMap = fderiv ℝ physicalBirkhoff u) ∧
      (∃ e : PhysicalL2 ≃L[ℝ] CartesianReal,
        e.toContinuousLinearMap = fderiv ℝ realBirkhoffCartesian u)) :
  (∀ (u : PhysicalL2) (n : ℤ),
    physicalBirkhoff u n =
      (cartesianX n (realSlice u) - Complex.I * cartesianY n (realSlice u)) /
        (Real.sqrt 2 : ℂ) ∧
    physicalBirkhoff u n = xiN38 n (realSlice u) / 2 *
      cartesianZExtended n (-1) (realSlice u) *
      Complex.exp (-Complex.I * betaSum n (realSlice u)) ∧
    actualGapActionAllE02_38 u n = ‖physicalBirkhoff u n‖^2) ∧
  (∀ u : PhysicalL2, HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖^2)) ∧
  (∀ u h k : PhysicalL2,
    inner ℝ ((Complex.I : ℂ) • fderiv ℝ physicalBirkhoff u h)
      (fderiv ℝ physicalBirkhoff u k) = inner ℝ ((Complex.I : ℂ) • h) k) ∧
  fderiv ℝ physicalBirkhoff 0 =
    reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ ∧
  (∀ (u : PhysicalL2) (n : ℤ),
    fderiv ℝ physicalBirkhoff 0 u n = -physicalFourier u (-n)) := by
  refine ⟨fun u n => ⟨hcart u n, ?_, ?_⟩, fun u => (sourceFamily.Phi_mass u).1,
    fun u h k => ?_, h5011.1, fun u n => ?_⟩
  · have hgk : realSlice u ∈ gkW :=
      sourceFamily.W_gk (sourceFamily.V_W (sourceFamily.V_real (Set.mem_range_self u)))
    rw [hZminus n (realSlice u) hgk, mul_assoc]
    exact (hX004 u n).2.2.2.1
  · exact ((hX004 u n).2.2.2.2.2).symm
  · have hre : ∀ (v : PhysicalL2) (n : ℤ),
        (cartesianX n (realSlice v)).im = 0 ∧ (cartesianY n (realSlice v)).im = 0 :=
      fun v n => ⟨(h4040 v n).1, (h4040 v n).2.1⟩
    obtain ⟨⟨e, he⟩, -⟩ := h6002 u
    have hinj : Function.Injective (fderiv ℝ physicalBirkhoff u) := by
      rw [← he]
      exact e.injective
    exact core6028 u (h5012.2.2 u) (hcoord u)
      (fun n => hstar _ (hfre _ (fun v => (hre v n).1) u))
      (fun n => hstar _ (hfre _ (fun v => (hre v n).2) u))
      (fun m n => h5040 u m n) hinj h k
  · rw [h5011.1]
    show reflectedFourierL2 u n = -physicalFourier u (-n)
    rw [reflectedFourierL2_apply]
    rfl

end
end G6028Aux
end NlsGge.GKDefinitionDesign
