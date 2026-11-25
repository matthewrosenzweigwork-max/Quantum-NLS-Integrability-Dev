import QuantumNLS.BetheSpectralCharges
import QuantumNLS.RapidityTransport

/-! DEF-034, DEFINITIONS_LEDGER.md:731–749; definitions.tex:205.
A finite normalized expansion and the predicate on ONE sequence serving
all FIXED charge/weight orders. No existence, diagonal-selection theorem,
charge limit, action limit, or growing-order estimate is asserted.
The classical charge values and action vector remain explicit parameters.
-/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.CommonBethePacket
open BetheLabels BetheCoefficientTransform PhysicalTensor Filter
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- Actual finite linear combination in the physical symmetric sector. -/
def synthesis {L : ℝ} [Fact (0 < L)] {N : ℕ} (b : BetheBasis L N)
    (a : MArr N →₀ ℂ) : HN L N := ∑ m ∈ a.support, a m • b m

/-- A finite Bethe packet means a normalized finite linear combination.
Normalization is the membership condition, not an assertion of existence. -/
structure Packet {L : ℝ} [Fact (0 < L)] {N : ℕ} (b : BetheBasis L N) where
  coefficients : MArr N →₀ ℂ
  normalized : ‖synthesis b coefficients‖ = 1

def vector {L : ℝ} [Fact (0 < L)] {N : ℕ} {b : BetheBasis L N}
    (P : Packet b) : HN L N := synthesis b P.coefficients

def support {L : ℝ} [Fact (0 < L)] {N : ℕ} {b : BetheBasis L N}
    (P : Packet b) : Finset (MArr N) := P.coefficients.support

/-- Nonnegative summable target A from DEF-012. Identifying it with the
indexed nonlinear action a_n(u) is a separate physical input. -/
structure ActionTarget where
  values : ℤ → ℝ
  nonnegative : ∀ n, 0 ≤ values n
  summable : Summable values

/-- The fixed intensive spectral-charge discrepancy uses the realized
DEF-008 eigenvalues on all complete arrays at coupling c. -/
def chargeError (L c : ℝ) (N r : ℕ) (target : ℝ) (m : MArr N) : ℝ :=
  |BetheSpectralCharges.eigenvalue L N c r m / N - target|

/-- Support-uniform convergence for a single fixed order r.
Only labels with nonzero packet coefficients are tested. -/
def ChargeLimit {L : ℝ} [Fact (0 < L)]
    {b : (n : ℕ) → BetheBasis L (n+1)} (P : (n : ℕ) → Packet (b n))
    (coupling : ℕ → ℝ) (r : ℕ) (target : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ m ∈ support (P n),
    chargeError L (coupling n) (n+1) r target m ≤ ε

/-- Support-uniform weighted error with the possibly infinite DEF-012
series. Using ENNReal prevents a divergent real series from reading as zero. -/
def WeightedActionLimit {L : ℝ} [Fact (0 < L)]
    {b : (n : ℕ) → BetheBasis L (n+1)} (P : (n : ℕ) → Packet (b n))
    (A : ActionTarget) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ m ∈ support (P n),
    RapidityTransport.weightedError a A.values (n+1) m ≤ ENNReal.ofReal ε

/-- One sequence indexed by the positive particle number N=n+1.
The sequence binder precedes EVERY fixed order. Classical charge targets
and A are explicit arguments. This predicate proves none of its clauses. -/
def IsCommon {L : ℝ} [Fact (0 < L)]
    {b : (n : ℕ) → BetheBasis L (n+1)} (P : (n : ℕ) → Packet (b n))
    (u : L2T L) (coupling : ℕ → ℝ) (chargeTarget : ℕ → ℝ)
    (A : ActionTarget) : Prop :=
  ‖u‖ = 1 ∧
  Tendsto (fun n => ‖vector (P n) - productVec L (n+1) u‖) atTop (𝓝 0) ∧
  (∀ r : ℕ, 1 ≤ r → ChargeLimit P coupling r (chargeTarget r)) ∧
  (∀ a : ℝ, 0 ≤ a → WeightedActionLimit P A a)

/-- Concrete Bethe family at the prescribed kappa/N, with EXT-001 exposed
as the same explicit hypothesis as frozen BCB1/BCH1. -/
def meanFieldBasis (hcont : BetheConditionalBasis.AbstractContinuity)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (n : ℕ) : BetheBasis L (n+1) :=
  BetheConditionalBasis.meanField_physicalBasis hcont L (n+1) (by omega) hκ

/-- Specialization of the predicate, not a claim that such a sequence
exists. The packet P and all unrealized classical targets are parameters. -/
def IsCommonMeanField (hcont : BetheConditionalBasis.AbstractContinuity)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (P : (n : ℕ) → Packet (meanFieldBasis hcont L κ hκ n))
    (u : L2T L) (chargeTarget : ℕ → ℝ) (A : ActionTarget) : Prop :=
  IsCommon P u (fun n => κ / (n+1)) chargeTarget A

end QuantumNLS.CommonBethePacket

#print axioms QuantumNLS.CommonBethePacket.synthesis
#print axioms QuantumNLS.CommonBethePacket.Packet
#print axioms QuantumNLS.CommonBethePacket.vector
#print axioms QuantumNLS.CommonBethePacket.support
#print axioms QuantumNLS.CommonBethePacket.ActionTarget
#print axioms QuantumNLS.CommonBethePacket.chargeError
#print axioms QuantumNLS.CommonBethePacket.ChargeLimit
#print axioms QuantumNLS.CommonBethePacket.WeightedActionLimit
#print axioms QuantumNLS.CommonBethePacket.IsCommon
#print axioms QuantumNLS.CommonBethePacket.meanFieldBasis
#print axioms QuantumNLS.CommonBethePacket.IsCommonMeanField

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.CommonBethePacket.synthesis,
    ``QuantumNLS.CommonBethePacket.Packet,
    ``QuantumNLS.CommonBethePacket.vector,
    ``QuantumNLS.CommonBethePacket.support,
    ``QuantumNLS.CommonBethePacket.ActionTarget,
    ``QuantumNLS.CommonBethePacket.chargeError,
    ``QuantumNLS.CommonBethePacket.ChargeLimit,
    ``QuantumNLS.CommonBethePacket.WeightedActionLimit,
    ``QuantumNLS.CommonBethePacket.IsCommon,
    ``QuantumNLS.CommonBethePacket.meanFieldBasis,
    ``QuantumNLS.CommonBethePacket.IsCommonMeanField]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.CommonBethePacket." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Definition nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.CommonBethePacket.synthesis,
    ``QuantumNLS.CommonBethePacket.Packet,
    ``QuantumNLS.CommonBethePacket.vector,
    ``QuantumNLS.CommonBethePacket.support,
    ``QuantumNLS.CommonBethePacket.ActionTarget,
    ``QuantumNLS.CommonBethePacket.chargeError,
    ``QuantumNLS.CommonBethePacket.ChargeLimit,
    ``QuantumNLS.CommonBethePacket.WeightedActionLimit,
    ``QuantumNLS.CommonBethePacket.IsCommon]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n == ``QuantumNLS.BetheConditionalBasis.AbstractContinuity then
        throwError "Generic definition reached EXT-001 premise: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"Definition aggregate audit PASS: {seen.size} transitive constants; {checked.size} generic constants independent of EXT-001. Concrete instantiations require its explicit Prop hypothesis only."
