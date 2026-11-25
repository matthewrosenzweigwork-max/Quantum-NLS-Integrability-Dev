import NlsGge.Atomic.IntervalZSAction

/-! The four source boundary conditions on the actual interval H1 graph.
Boundary cancellation, symmetry, smooth-test inclusion and L2 density are
theorem obligations; the domain definition assumes none of these conclusions. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.Interval
open NlsGge.Schur NlsGge.Atomic.LIB026

/-- The four source boundary conditions on the two interval components. -/
inductive ZSBoundaryCondition where
  | dirichlet
  | neumann
  | periodic
  | antiperiodic
  deriving DecidableEq

/-- Literal endpoint relations, using the unique continuous H1 representatives. -/
def HasZSBoundaryCondition (bc : ZSBoundaryCondition) (f : H1Pair) : Prop :=
  match bc with
  | .dirichlet =>
      traceLeft (f true) = traceLeft (f false) ∧
      traceRight (f true) = traceRight (f false)
  | .neumann =>
      traceLeft (f true) = -traceLeft (f false) ∧
      traceRight (f true) = -traceRight (f false)
  | .periodic => ∀ b : Bool, traceRight (f b) = traceLeft (f b)
  | .antiperiodic => ∀ b : Bool, traceRight (f b) = -traceLeft (f b)

/-- Actual L2 domain: values of interval H1 pairs satisfying the boundary relation. -/
def zsBoundaryDomain (bc : ZSBoundaryCondition) : Set SourcePairL2 :=
  h1PairValue '' {f : H1Pair | HasZSBoundaryCondition bc f}

end NlsGge.Atomic.Interval
