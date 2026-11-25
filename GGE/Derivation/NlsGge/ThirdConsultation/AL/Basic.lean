import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Hierarchy.ALFreeFields38
import NlsGge.Hierarchy.ALCorrector38
import NlsGge.Hierarchy.ALFreeDeterminant38
import NlsGge.Hierarchy.ALRatesBridge38
import NlsGge.Hierarchy.ALCompactConsistency38
import NlsGge.Hierarchy.ALPlaneConsistency38
import NlsGge.Hierarchy.ALNegativeQuartic38
import NlsGge.Hierarchy.ALTiltMeasure38
import NlsGge.Birkhoff.W04WeightedSmoothing38
import NlsGge.Birkhoff.S05FreeEnergy38b
import NlsGge.Hierarchy.ALEnergyAnalytic38
import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Hierarchy.ALFiniteMeasure38
import NlsGge.Hierarchy.ALMoments38
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALTransferDefs38
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALSamplingV2Formula38
import NlsGge.Hierarchy.ALQ4Ensemble38
import NlsGge.Hierarchy.ALQ4Gaussian38
import NlsGge.Hierarchy.ALGaussianNormalizer38
import NlsGge.Hierarchy.ALTilt38
import NlsGge.Hierarchy.ALLaurent38
import NlsGge.Hierarchy.ALExteriorBranch38
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.Hierarchy.ALIsospectral38
import NlsGge.Hierarchy.ALGlobalFlow38
import NlsGge.Hierarchy.ALLiouvilleInvariance38
import NlsGge.Hierarchy.ALBoundaryKappa38
import NlsGge.Hierarchy.ALPoissonLiouville38
import NlsGge.Hierarchy.ALComplexMonodromy38
import NlsGge.Hierarchy.ALComplexExteriorLog38
import NlsGge.Hierarchy.ALPlaneWaveGap38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Spectral.ActualComplexZsDysonProductHasSumV2
import NlsGge.Analysis.NaturalCover
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Schur.FourierMultiplier
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev.FiniteFourier
import NlsGge.Birkhoff.F08Bare38g
import NlsGge.Birkhoff.F08Bare38d
import NlsGge.Birkhoff.F05Identity38
import NlsGge.Bootstrap



/- AL shared-definitions host (proof development, author; source: gpt6pro followup2 DEFINITIONS/AL.lean.md).
   Verbatim definitions except the names listed in the exclusion report (already declared in NlsGge). Reviewer: proof development. -/

noncomputable section
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.AL

-- Li–Nenciu (2.10), with their Verblunsky coefficient β.
open Classical in
def riccatiRatio {L : ℕ} [NeZero L]
    (α : ZMod L → ℂ) (ζ : ℂ) : ZMod L → ℂ :=
  if h : ∃ q : ZMod L → ℂ,
      (∀ j, ‖q j‖ < 1) ∧
      (∀ j, q (j+1) =
        (ζ * star (α j) + ζ^2 * q j) / (1 + ζ * α j * q j))
  then h.choose else 0

def positiveWeightENN (β : ℕ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (β j * x^(2*j))

def complexMoment {L : ℕ} [NeZero L]
    (p : (ZMod L → ℂ) × (ZMod L → ℂ)) (j : ℕ) : ℂ :=
  (alKc38 j p + alKc38 j p.swap) / 2

def complexEnergy {L : ℕ} [NeZero L] (c : ℕ → ℝ) (h : ℝ)
    (p : (ZMod L → ℂ) × (ZMod L → ℂ)) : ℂ :=
  ∑' j : ℕ, (NlsGge.coefficient c j : ℂ) *
    ((h⁻¹ : ℝ) : ℂ)^(2*j+1) * complexMoment p j

end NlsGge.ThirdConsultation.AL

end

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik
open NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.AL

def scaledQuarticTerms (N : ℕ) (v : ZMod (2 * N + 1) → ℂ)
    (i : Fin 3) : ℝ :=
  let h := alh38 N
  let α := fun j => (h : ℂ) * v j
  if i = 0 then
    ((3 : ℝ) / 2) * (∑ j, (alR α (j + 1) - alR α j) ^ 2) / h ^ 5
  else if i = 1 then
    (∑ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2) / h ^ 5
  else
    2 * (∑ j, (α j * star (α (j - 1))).im ^ 2) / h ^ 5

def q4Good : Set (ℤ → ℂ) :=
  {g | ∀ j : ℕ, Summable (fun k : ℤ =>
    sobolevModeWeight ((3 : ℝ) / 2 - 1 / ((j : ℝ) + 1)) k *
      ‖g k‖ ^ 2 / (1 + (k : ℝ) ^ 4))}

end NlsGge.ThirdConsultation.AL
end

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Set
open NlsGge.Pilot NlsGge.AblowitzLadik NlsGge.SpectralFoundations
open NlsGge.Analysis NlsGge.Schur NlsGge.HierarchyRiccati.Core NlsGge.Weights
open NlsGge.Birkhoff
open scoped Topology ENNReal Matrix
namespace NlsGge.ThirdConsultation.AL

/-- One cofinal, countable Gaussian event for all real Sobolev orders. -/
def alFreeGoodEvent (c : ℕ → ℝ) : Set (ℤ → ℂ) :=
  {g | ∀ r : ℕ, Summable (fun k : ℤ =>
    sobolevModeWeight (r : ℝ) k * ‖g k‖ ^ 2 / alRateComp38 c k)}

open Classical in
/-- The actual E_s realization; finite lattice support eliminates the fallback. -/
def alCriticalRealization {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) (g : ℤ → ℂ) :
    ECarrier38 c s :=
  if hz : alUhCoef38 c.val N g ∈ seqE38 c s then
    eMk38 c s (alUhCoef38 c.val N g) hz else 0

/-- The uncorrected free law on the existing critical Hilbert space. -/
def alCriticalLaw {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) [MeasurableSpace (ECarrier38 c s)] (N : ℕ) :
    Measure (ECarrier38 c s) :=
  alFreeLaw38.map (alCriticalRealization c s N)

/-- Common-space lattice weight on physical Fourier coefficients u. -/
def alCommonWeight (c : ℕ → ℝ) (N : ℕ) (u : ℤ → ℂ) : ℝ :=
  alReweight38 c (alMeshStep38 N)
    (fun k : ZMod (2 * N + 1) => alCorrInvCoef38 c N u k.valMinAbs)

/-- Evolution from a to b, normalized to the identity at a. -/
def alContinuumPropagator38 (U : ℝ → ℂ) (lam a b : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  actualComplexZsDysonTsum (fun x => -Complex.I * U (a + x))
    (-(lam : ℂ)) (b - a)

/-- Supremum norm on the period [0,1]. -/
def alIntervalSup38 (U : ℝ → ℂ) : ℝ :=
  sSup ((fun x => ‖U x‖) '' Icc (0 : ℝ) 1)

/-- Modulus on [0,1]; used only for δ≥0 and continuous U. -/
def alIntervalModulus38 (U : ℝ → ℂ) (δ : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Icc (0 : ℝ) 1, ∃ y ∈ Icc (0 : ℝ) 1,
    |x - y| ≤ δ ∧ r = ‖U x - U y‖}

/-- The candidate tilt determinant is the exponential of the real log sum.
    AL-115 supplies absolute convergence before it is used as a product. -/
def alTiltLimit38 (c : ℕ → ℝ) (δ : ℝ) : ℝ :=
  Real.exp (∑' k : ℤ,
    Real.log (alTiltFactor38 c δ (2 * Real.pi * (k : ℝ)) 0))

end NlsGge.ThirdConsultation.AL
end
