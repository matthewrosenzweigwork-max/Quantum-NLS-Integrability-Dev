import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
noncomputable section
set_option autoImplicit false
namespace NlsGge.ThirdConsultation.KSPSVolterra

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Vec := Fin 2 → ℂ
abbrev SobolevC (N : ℕ) :=
  PhysicalSobolev38 (N : ℝ) × PhysicalSobolev38 (N : ℝ)

def R : Mat := !![Complex.I, 0; 0, -Complex.I]

def E (lam : ℂ) (x : ℝ) : Mat :=
  !![Complex.exp (-(Complex.I * lam * (x : ℂ))), 0;
     0, Complex.exp (Complex.I * lam * (x : ℂ))]

def phi (p : PotPair) (x : ℝ) : Mat :=
  !![0, potRepFst38 p x; potRepSnd38 p x, 0]

def integrateMatrix (a b : ℝ) (F : ℝ → Mat) : Mat :=
  fun i j => ∫ t in a..b, F t i j

def integrateVector (a b : ℝ) (F : ℝ → Vec) : Vec :=
  fun i => ∫ t in a..b, F t i

-- Picard order zero is the free propagator, not the identity matrix.
def term : ℕ → ℝ → ℂ → PotPair → Mat
  | 0, x, lam, _p => E lam x
  | j+1, x, lam, p =>
      integrateMatrix 0 x (fun t => E lam (x-t) * R * phi p t * term j t lam p)

def toPair (φ : SobolevC 1) : PotPair :=
  (NlsGge.GKDefinitionDesign.physicalSobolevEmbed 1 φ.1,
   NlsGge.GKDefinitionDesign.physicalSobolevEmbed 1 φ.2)

def phiPrime (φ : SobolevC 1) (t : ℝ) : Mat :=
  !![0, coverRep38 (physicalSobolevDerivative38 1 φ.1) t;
     coverRep38 (physicalSobolevDerivative38 1 φ.2) t, 0]

def P (lam : ℂ) (φ : SobolevC 1) (x : ℝ) : Mat :=
  integrateMatrix 0 x (fun t => E lam (-2*t) * phiPrime φ t)

def integratedQuadratic (φ : SobolevC 1) (x : ℝ) : Mat :=
  (∫ t in (0 : ℝ)..x,
    potRepFst38 (toPair φ) t * potRepSnd38 (toPair φ) t) • (1 : Mat)

-- Finite-order definition, followed by the actual convergent Picard sum.
-- Each scalar sum must be proved summable on [0,1] before identities use it.
def fundamental (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : Mat :=
  fun i j => ∑' k : ℕ, term k x lam (toPair φ) i j

def adjugate2 (A : Mat) : Mat := !![A 1 1, -A 0 1; -A 1 0, A 0 0]

def inverseFundamental (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : Mat :=
  adjugate2 (fundamental φ x lam)

def perturbedOscillatoryIntegral (α : ℤ → ℂ) (f : PhysicalL2)
    (x : ℝ) (n : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..x,
    (Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + α n) *
        ((x - 2*t : ℝ) : ℂ)) -
     Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) *
        ((x - 2*t : ℝ) : ℂ))) * coverRep38 f t

end NlsGge.ThirdConsultation.KSPSVolterra


namespace NlsGge.ThirdConsultation.KSPS
open NlsGge.Pilot NlsGge.GK38

abbrev SobolevC (N : ℕ) :=
  NlsGge.Atomic.Common.PhysicalSobolev38 (N:ℝ) ×
  NlsGge.Atomic.Common.PhysicalSobolev38 (N:ℝ)

abbrev SobolevR (N : ℕ) :=
  NlsGge.Atomic.Common.PhysicalSobolev38 (N:ℝ)

def toPotPair {N : ℕ} (φ : SobolevC N) : PotPair :=
  (NlsGge.GKDefinitionDesign.physicalSobolevEmbed N φ.1,
   NlsGge.GKDefinitionDesign.physicalSobolevEmbed N φ.2)

def toPhysical {N : ℕ} (u : SobolevR N) : PhysicalL2 :=
  NlsGge.GKDefinitionDesign.physicalSobolevEmbed N u

def indexWeight (n : ℤ) : ℝ := Real.sqrt (1 + (n:ℝ)^2)

def iteratedDerivative (N : ℕ) (f : NlsGge.Atomic.Common.PhysicalSobolev38 (N:ℝ)) :
    PhysicalL2 :=
  NlsGge.Atomic.Common.physicalSobolevDerivative38 N f

def freePropagator (x : ℝ) (lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(Complex.I*lam*x)), 0;
     0, Complex.exp (Complex.I*lam*x)]

def potentialMatrix {N : ℕ} (φ : SobolevC N) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, NlsGge.GKDefinitionDesign.sobolevPointValue N φ.1 x;
     NlsGge.GKDefinitionDesign.sobolevPointValue N φ.2 x, 0]

def volterraTerm {N : ℕ} (j : ℕ) (x : ℝ) (lam : ℂ) (φ : SobolevC N) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  NlsGge.ThirdConsultation.KSPSVolterra.term j x lam (toPotPair φ)

def oscillatoryPotentialDerivative (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  NlsGge.ThirdConsultation.KSPSVolterra.P lam φ x

def weightedErrorL2 (α : ℤ → ℂ) (f : PhysicalL2) (x : ℝ) : ℝ :=
  ∑' n : ℤ, indexWeight n^2 *
    ‖NlsGge.ThirdConsultation.KSPSVolterra.perturbedOscillatoryIntegral α f x n‖^2

end NlsGge.ThirdConsultation.KSPS

