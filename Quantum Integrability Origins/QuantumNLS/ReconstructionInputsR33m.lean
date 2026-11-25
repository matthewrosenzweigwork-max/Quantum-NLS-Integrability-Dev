import QuantumNLS.ActualModelTargetR53a
import QuantumNLS.StrongSymbolDef
import QuantumNLS.PreparationStability
import QuantumNLS.UnitPhaseTransfer

/-! Printed interfaces for dynamic gauge comparison and reduced reconstruction.
The gauge is context fixed by R-D51987CA, with the established conjugate
convention for the basis rephasing. The interfaces quantify over the tests
only after this gauge and the physical Hamiltonian family have been fixed. -/

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ComplexConjugate ENNReal

namespace QuantumNLS.ReconstructionR33m

open ActualModelTargetR53a (HigherFlows hamFlows higher)
open BetheCoefficientTransform (HN)
open BetheOccupationGauge (Gauge)
open Def033HierarchyR24m (Smooth physical jointSmooth)
open OccupationUnitary (OneParticle)
open TraceClass

variable {L κ : ℝ} [Fact (0 < L)]

abbrev flows (hκ : 0 < κ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    HigherFlows L κ :=
  higher (ActualModelBindingR53a.hierarchy_intermediate hκ HierarchyInput)

abbrev basis (hκ : 0 < κ) (n : ℕ) :=
  UnconditionalBetheBasis.meanField_physicalBasis L (1 + n) (by omega) hκ

abbrev product (u : Smooth L) (n : ℕ) : HN L (1 + n) :=
  HighMomentsOps.wvec (1 + n) (physical u)

abbrev U (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ) :=
  HierarchyFlow.quantumFlow (basis (L := L) hκ n) κ R t

abbrev w (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L)
    (R : Finset ℕ) (t : ℕ → ℝ) : OneParticle :=
  (Def021ChartR41b.chart L κ hκ).Φ (physical (jointSmooth (hamFlows F R) t u))

abbrev E (hκ : 0 < κ) (g : Gauge) (n : ℕ) (a b : ℤ) :=
  CartesianOccupationTransfer.physical (basis (L := L) hκ n) g a b

abbrev W (hκ : 0 < κ) (g : Gauge) (n : ℕ) (a b : ℤ) :=
  UnitPhaseTransfer.physical (basis (L := L) hκ n) g a b

abbrev density (hκ : 0 < κ) (g : Gauge) (n : ℕ) (ψ : HN L (1 + n)) :=
  PreparationStability.density (basis hκ n) g ψ

abbrev projector := AuxiliaryDensity.rankOneOperator

abbrev Preparation (u : Smooth L) (ψ : ∀ n : ℕ, HN L (1 + n)) : Prop :=
  StrongSymbolDef.IsNormClosePrep ψ (product u)

/-- A strong scalar symbol and its adjoint, uniformly on the fixed time set. -/
def StrongSymbols {T : Type*} (K : Set T) (A : ∀ n : ℕ, HN L (1 + n) →L[ℂ] HN L (1 + n))
    (z : T → ℂ) (v : T → ∀ n : ℕ, HN L (1 + n)) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ K,
    ‖A n (v t n) - z t • v t n‖ ≤ ε ∧
    ‖(A n).adjoint (v t n) - conj (z t) • v t n‖ ≤ ε

/-- A fixed box in the active times. Inactive coordinates do not enter
either the joint generator or the joint Hamiltonian flow. -/
def TimeBox (R : Finset ℕ) (lo hi : ↥R → ℝ) : Set (ℕ → ℝ) :=
  {t | ∀ r : ↥R, t r ∈ Set.Icc (lo r) (hi r)}

/-- R-8362E5EB, weighted_actions_and_same_gauge_dynamics.tex:155–164.
For the supplied retargeted gauge, the Cartesian symbols include the
diagonals and collapsed actions. The phase symbols are on distinct
positive-action endpoints. Both orientations are strong and uniform on a
fixed box, for the source preparation class. No new gauge is chosen. -/
def RD8362E5EBInput (hκ : 0 < κ) (F : HigherFlows L κ) (g : Gauge) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ)
      (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
      ∀ a b : ℤ,
        let z := w hκ F u R
        let c := fun t => z t a * conj (z t b)
        let v := fun t n => U hκ R t n (ψ n)
        let w₀ := (Def021ChartR41b.chart L κ hκ).Φ (physical u)
        StrongSymbols (TimeBox R lo hi) (fun n => E (L := L) hκ g n a b) c v ∧
        (a ≠ b → 0 < ‖w₀ a‖ ^ 2 → 0 < ‖w₀ b‖ ^ 2 →
          StrongSymbols (TimeBox R lo hi) (fun n => W (L := L) hκ g n a b)
            (fun t => c t / (Real.sqrt (‖z t a‖ ^ 2 * ‖z t b‖ ^ 2) : ℂ)) v)

/-- R-FAF88C8A, projective_reconstruction.tex:225–240. The chart, actual
physical flows and common gauge are fixed. A compact time box is a
particular compact subset of the same finite-dimensional time space. -/
def Reconstruction (hκ : 0 < κ) (F : HigherFlows L κ) (g : Gauge) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
      ∀ (ψ : ∀ n : ℕ, HN L (1 + n)), (∀ n, ‖ψ n‖ = 1) →
        Tendsto (fun n => ‖ψ n - product u n‖) atTop (𝓝 0) →
        Tendsto (fun n => ⨆ t : K,
          traceNorm (density hκ g n (U hκ R t.val n (ψ n)) -
            projector (w hκ F u R t.val))) atTop (𝓝 0)

end QuantumNLS.ReconstructionR33m
