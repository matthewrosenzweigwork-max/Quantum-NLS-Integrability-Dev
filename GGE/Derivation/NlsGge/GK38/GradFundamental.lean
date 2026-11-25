import NlsGge.GK38.GradFundamentalGradientProbe
import NlsGge.GK38.GradFundamentalStarProbe
import NlsGge.GK38.GradFundamentalCompact
import NlsGge.GK38.GradFundamentalL2Probe

/-! # K1: public independent fundamental variation and scalar gradient interface.
GK Chapter I, Proposition3.1, Corollary3.2, Lemmas4.2–4.3 and8.2.
All definitions use the integral/resolvent construction already identified with
actual source derivatives. No scalar gradient is defined through fderiv.
-/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

/-- Independent potential variation CLM, with its raw VOC identity below. -/
def fundPotentialCLM38 (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] PairCont38 :=
  fundPotentialResolventCLM38 φ z

theorem fundPotentialCLM38_apply (φ : PotPair) (z : ℂ) (h : PotPair) (t : Icc (0 : ℝ) 1) :
    fundPotentialCLM38 φ z h t = fundPotentialIntegral38 φ z t h :=
  fundPotentialResolventCLM38_voc φ z h t

theorem fundPotentialCLM38_volterra (φ : PotPair) (z : ℂ) (h : PotPair) :
    fundPotentialCLM38 φ z h = volterraP h z (fundContP φ z) +
      volterraP φ z (fundPotentialCLM38 φ z h) :=
  fundPotentialResolventCLM38_volterra φ z h

theorem hasFDerivAt_fundPotentialCLM38 (φ : PotPair) (z : ℂ) :
    HasFDerivAt (fun ψ => fundContP ψ z) (fundPotentialCLM38 φ z) φ :=
  hasFDerivAt_fundPotentialResolvent38 φ z

/-- Exact plan contract: the independently integral-defined full-trace gradient. -/
theorem hasFDerivAt_discrim (z : ℂ) (φ : PotPair) :
    HasFDerivAt (fun ψ => discrim ψ z) (gradDiscrimCLM φ z) φ :=
  hasFDerivAt_gradDiscrimCLM φ z

theorem hasFDerivAt_antiDiscrim (z : ℂ) (φ : PotPair) :
    HasFDerivAt (fun ψ => antiDiscrim ψ z) (gradAntiDiscrimCLM φ z) φ :=
  hasFDerivAt_gradAntiDiscrimCLM φ z

end
end NlsGge.GK38
