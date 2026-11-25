import NlsGge.Atomic.G1.G1062
import NlsGge.Atomic.LIB.LIB033
import NlsGge.Atomic.LIB.LIB038
import NlsGge.Atomic.LIB.LIB041
import NlsGge.Atomic.LIB.LIB042
import NlsGge.Atomic.IntervalZSBoundary

/-!
# G1-104 host: operator realizations, root spaces and characteristic functions

Verbatim from Pro round 9/10, `DEFINITIONS/G1.lean.md` (followup8), section "Operator realizations,
root spaces and characteristic functions" (lines 456-479) and the statement-only obligation
`sourceIntervalClass_spec` (proved here, proof not part of Pro's text).

Lexical repairs only: added `import`/`open` lines (`NlsGge.Pilot NlsGge.GK38` for `PhysicalL2`,
`PotPair`, `coverRep38`, `dirichletChar`, `discrim`, `perChar`; `MeasureTheory` for `volume`;
scoped `Classical` for the `if h : MemLp` decision).
The names `gkNeumannCharacteristic` (landed in NlsGge.Atomic.G1.G1062, namespace
NlsGge.GKDefinitionDesign) are reused, not redefined.
-/

set_option autoImplicit false

open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB038 NlsGge.Atomic.LIB041
open NlsGge.Atomic.LIB042
open NlsGge.Pilot NlsGge.GK38 MeasureTheory

namespace NlsGge.GKDefinitionDesign
noncomputable section
open scoped Classical

def sourceIntervalClass (f : PhysicalL2) : SourceIntervalL2 :=
  if h : MemLp (coverRep38 f) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) then
    h.toLp (coverRep38 f)
  else 0

def intervalPotential (φ : PotPair) : SourcePairL2 :=
  WithLp.toLp 2 (fun b : Bool => if b then sourceIntervalClass φ.1
    else sourceIntervalClass φ.2)

def boundaryCharacteristic (φ : PotPair) (bc : ZSBoundaryCondition) : ℂ → ℂ :=
  match bc with
  | .dirichlet => dirichletChar φ
  | .neumann => gkNeumannCharacteristic φ
  | .periodic => fun z => discrim φ z-2
  | .antiperiodic => fun z => discrim φ z+2

def rootVector (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ)
    (v : SourcePairL2) : Prop :=
  ∃ N : ℕ, ∃ w : ℕ → SourcePairL2,
    w 0 = v ∧ w N = 0 ∧
    ∀ j : ℕ, j < N →
      ∃ hj : w j ∈ A.domain, A ⟨w j,hj⟩ - z • w j = w (j+1)

def rootSpace (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ) :
    Submodule ℂ SourcePairL2 :=
  Submodule.span ℂ {v | rootVector A z v}

def algebraicMultiplicity (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ) : ℕ :=
  Module.finrank ℂ (rootSpace A z)

end
end NlsGge.GKDefinitionDesign
