import QuantumNLS.Def044D1SpectralR51a
import QuantumNLS.Def021ChartR41b
import QuantumNLS.RootScalarPeriodR8
import QuantumNLS.Reg015Setting

/-!
DEF-044 clause (2). The global analytic strong canonical chart is the actual
DEF-021 chart carrier. All nonnegative Sobolev scales, action determination,
and the leading quantum logarithmic period on full open Hilbert neighborhoods
are explicit requirements. In particular the previously frozen Cauchy-period
result is not promoted to the logarithmic-period assertion.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.Def044ChartR51a
open PhysicalTensor QuantumFourierSpecification
open Def044D1SpectralR51a
variable {L κ : ℝ} [Fact (0 < L)]

/-- Physical indexed actions, at arbitrary mass including the zero field. -/
def action (hκ : 0 < κ) (u : L2T L) (n : ℤ) : ℝ :=
  (RootIndexedMasses.masses hκ u).1 n

/-- Exactly Z_j = sqrt(2) w_{-j}; this does not relabel quantum occupations. -/
def reflected (w : Coordinates) (j : ℤ) : ℂ := (Real.sqrt 2 : ℂ)*w (-j)

/-- Literal normalization on the actual coordinate carrier. -/
theorem reflected_action (w : Coordinates) (n : ℤ) :
    ‖reflected w (-n)‖^2/2 = ‖w n‖^2 := by
  simp only [reflected, neg_neg, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg (2 : ℝ)), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The same actual global chart and inverse restrict to homeomorphisms at
EVERY real nonnegative Sobolev order. Both embeddings are fixed explicitly. -/
def SobolevRestrictions (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : Prop :=
  ∀ s : ℝ, ∀ hs : 0 ≤ s, ∃ e : Sobolev.H02 L s ≃ₜ Sobolev.h02 L s,
    (∀ u, Reg015Setting.toBase s hs (e u) = C.Φ u.val) ∧
    (∀ z, (e.symm z).val = C.Ψ (Reg015Setting.toBase s hs z))

/-- Both the scalar transfer and its entire full-mass measure are determined
by all indexed actions, on the full physical Hilbert space. -/
def ActionDetermination (hκ : 0 < κ) : Prop :=
  ∀ u v : L2T L, (∀ n, action hκ u n = action hκ v n) →
    NormalizedTransfer.productSymbol L κ u = NormalizedTransfer.productSymbol L κ v ∧
    PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v

/-- Leading quantum period with its exact sign and coefficient. λ is the
local logarithm of the quadratic transfer inverse, constrained below. -/
def leadingPeriod (hκ : 0 < κ) (base : L2T L) (n : ℤ)
    (localLog : ℂ → ℂ → ℂ) (v : L2T L) : ℝ :=
  -(1/(2*Real.pi*κ)) * (∮ z in C((RootScalarPeriodR8.center hκ base n : ℂ),
    RootScalarPeriodR8.radius hκ base n), localLog z (NormalizedTransfer.productSymbol L κ v z)).re

/-- Fixed contour branch and identity on a FULL open Hilbert neighborhood.
The same open neighborhood works for every label in each fixed finite set;
zero actions and radial directions are included without a positivity premise. -/
def FullOpenPeriods (hκ : 0 < κ) : Prop :=
  ∀ base : L2T L, ∀ F : Finset ℤ, ∃ U : Set (L2T L), IsOpen U ∧ base ∈ U ∧
    ∀ n ∈ F, ∃ localLog : ℂ → ℂ → ℂ,
      0 < RootScalarPeriodR8.radius hκ base n ∧
      (∃ V : Set (ℂ × ℂ), IsOpen V ∧
        AnalyticOnNhd ℂ (fun p : ℂ × ℂ => localLog p.1 p.2) V ∧
        (∀ v ∈ U, ∀ z ∈ Metric.sphere (RootScalarPeriodR8.center hκ base n : ℂ)
          (RootScalarPeriodR8.radius hκ base n),
          (z, NormalizedTransfer.productSymbol L κ v z) ∈ V ∧
            z ∉ Complex.ofReal '' (PhysicalQuantumMeasure.measure hκ v).support) ∧
        ∀ p ∈ V, (Complex.exp (localLog p.1 p.2)^2 - p.2*Complex.exp (localLog p.1 p.2) +
          Complex.exp (Complex.I*L*p.1) = 0) ∧
            Complex.exp (localLog p.1 p.2) -
              Complex.exp (Complex.I*L*p.1)/Complex.exp (localLog p.1 p.2) ≠ 0) ∧
      (∀ v ∈ U, ∀ z ∈ Metric.sphere (RootScalarPeriodR8.center hκ base n : ℂ)
        (RootScalarPeriodR8.radius hκ base n),
        localLog z (NormalizedTransfer.productSymbol L κ v z) =
          Complex.I*κ*scalarG (PhysicalQuantumMeasure.measure hκ v) z) ∧
      (∀ v ∈ U, leadingPeriod hκ base n localLog v = action hκ v n) ∧
      (∀ v ∈ U, AnalyticAt ℝ (leadingPeriod hκ base n localLog) v) ∧
      (∀ v ∈ U, fderiv ℝ (leadingPeriod hκ base n localLog) v =
        fderiv ℝ (fun w => action hκ w n) v)

/-- The second source clause, with the quantum-derived analytic chart and its
exact inverse already built into the carrier, and the remaining requirements
kept as explicit dependencies. This definition asserts no existence. -/
structure ChartInterface (hκ : 0 < κ) where
  chart : Def021ChartR41b.Chart L κ hκ
  sobolev : SobolevRestrictions hκ chart
  action_determination : ActionDetermination (L := L) hκ
  full_open_periods : FullOpenPeriods (L := L) hκ

/-- Both printed action formulas follow from the chart's actual exact moduli. -/
theorem exact_actions {hκ : 0 < κ} (C : ChartInterface (L := L) hκ) (v : L2T L) (n : ℤ) :
    action hκ v n = ‖C.chart.Φ v n‖^2 ∧
    action hκ v n = ‖reflected (C.chart.Φ v) (-n)‖^2/2 := by
  have h := (C.chart.actions v n).symm
  exact ⟨h, h.trans (reflected_action (C.chart.Φ v) n).symm⟩

/-- The action identity identifies every real Hilbert direction, including
h=v. The quantifiers do not restrict directions to a tangent sphere. -/
theorem full_directions {hκ : 0 < κ} (hp : FullOpenPeriods (L := L) hκ)
    (base : L2T L) (F : Finset ℤ) :
    ∃ U : Set (L2T L), IsOpen U ∧ base ∈ U ∧ ∀ n ∈ F,
      ∃ localLog : ℂ → ℂ → ℂ, ∀ v ∈ U, ∀ h : L2T L,
        fderiv ℝ (leadingPeriod hκ base n localLog) v h =
          fderiv ℝ (fun w => action hκ w n) v h := by
  obtain ⟨U, hU, hb, hn⟩ := hp base F
  refine ⟨U, hU, hb, fun n hnF => ?_⟩
  obtain ⟨localLog, -, -, -, -, -, hd⟩ := hn n hnF
  exact ⟨localLog, fun v hv h => DFunLike.congr_fun (hd v hv) h⟩

end QuantumNLS.Def044ChartR51a
#print axioms QuantumNLS.Def044ChartR51a.reflected_action
#print axioms QuantumNLS.Def044ChartR51a.exact_actions
#print axioms QuantumNLS.Def044ChartR51a.full_directions

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def044ChartR51a." ||
        n.toString.startsWith "_private.QuantumNLS.Def044ChartR51a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round51 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
