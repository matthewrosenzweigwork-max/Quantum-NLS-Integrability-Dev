import QuantumNLS.Bind7B115CAA16H01

/-!
# Bind7B115CAA16H02: R-115CAA16 (`lem:audit-weighted`), conclusion exactly the printed lemma

PRINTED SOURCE: `source-text/chapters/core/weighted_actions_and_same_gauge_dynamics.tex`, lines 13-34
(`\begin{lemma}[Weighted occupation and common-packet replacement]` ... `\end{lemma}`; file SHA-256
`8ada30bedbeaf335578cee4f7d11546067040ac4f4e389b5358e0af1c40b8ea0`).  `scope.json` (SHA-256
`249499751e4947422c01f76e4560c80bb75f91ce24a9441bcab274bb5a937dba`) node `R-115CAA16`, label
`lem:audit-weighted`, `statement_location` = `chapters/core/weighted_actions_and_same_gauge_dynamics.tex`
line 13, offset 556.

Printed conclusion (lines 17-33): for a smooth unit vector `u` on the physical circle of length `L`, coupling
`kappa/N`, quantum-derived scalar measure `M_u` with indexed masses `I_n(u)`:
  (a) for every fixed real `p >= 0`, `sum_n (1+n^2)^(p/2) |m_n/N - I_n(u)| -> 0` in probability
      (Lean: `error hκ u p N m`, for every `ε > 0` the Born probability of `{ε < error}` tends to 0);
  (b) the conserved-value assertion for every fixed charge order (Lean: `TendstoInProbability` of
      `eigenvalue L N (κ/N) r m / N` to `(charge L κ f (r+1)).re`);
  (c) one sequence of normalized finite Bethe packets approximates `u^{⊗N}` in norm, has every fixed charge
      value, and has the same weighted occupation convergence uniformly over its supports.
Nothing else is printed (the last sentence of the lemma disclaims untruncated higher quantum moments in
expectation).

DERIVATION: by projection from the frozen `Bind7B115CAA16H01.audit_weighted_bound` (bfdfa948...), whose
conclusion has one additional last conjunct, `∀ N ev, vector (P N) ∈ (multiplier (physBasis L hκ N) ev).domain`
(every packet vector lies in every spectral multiplier domain).  That conjunct is not printed in the lemma
(it was noted as extra in terra_review r233 / review record r91).  Here it is deleted: `audit_weighted_printed`
proves the first six conjuncts, with the same hypotheses `hκ hf hu` and no other argument.

STATEMENT CORRESPONDENCE: the embedded `run_cmd` check verifies by `Expr` equality (and `isDefEq`) that the type
of `audit_weighted_printed` equals the type of H01 with exactly the last conjunct under the packet existential
deleted.

Remaining hypotheses: `hκ : 0 < κ`, `hf : SmoothPeriodic L f`, `hu : ‖smoothL2 hf‖ = 1` (the printed smooth unit
vector).  No acceptance claim; R-7B122087 is held for the owner ruling on the DEF-024 predecessor gate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.Bind7B115CAA16H02
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
open QuantumNLS.BetheCoefficientTransform
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.CommonBethePacket
open QuantumNLS.AuditWeightedProbabilityR49a QuantumNLS.AuditWeightedSeriesR49a
open QuantumNLS.AuditWeightedValuesR50a QuantumNLS.AuditWeightedTightR50a
open QuantumNLS.AuditWeightedSelectionR50a QuantumNLS.AuditWeightedCommonPacketR50a
variable {L κ : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- R-115CAA16 `lem:audit-weighted`, exactly the printed conclusion (no multiplier-domain conjunct). -/
theorem audit_weighted_printed (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) :
    (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
        {m | ε < error hκ (smoothL2 hf) p N m}) atTop (𝓝 0)) ∧
    (∀ r : ℕ, QuantumNLS.BornConvergence.TendstoInProbability
      (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu)
      (fun N m => QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ))
      (charge L κ f (r+1)).re) ∧
    ∃ P : (N : ℕ) → Packet (physBasis L hκ N),
      Tendsto (fun N => ‖vector (P N)-productVec L N (smoothL2 hf)‖) atTop (𝓝 0) ∧
      (∀ r ε, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        |QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ)-(charge L κ f (r+1)).re| ≤ ε) ∧
      (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        error hκ (smoothL2 hf) p N m ≤ ε) := by
  obtain ⟨h1, h2, P, hP1, hP2, hP3, -⟩ :=
    QuantumNLS.Bind7B115CAA16H01.audit_weighted_bound (L := L) hκ hf hu
  exact ⟨h1, h2, P, hP1, hP2, hP3⟩

open Lean Meta in
/-- Delete the last conjunct of a right-nested conjunction. -/
private partial def dropLastConj (e : Expr) : Expr :=
  match e.getAppFnArgs with
  | (``And, #[x, y]) =>
    match y.getAppFnArgs with
    | (``And, #[_, _]) => mkApp2 (mkConst ``And) x (dropLastConj y)
    | _ => x
  | _ => e

open Lean Meta in
/-- Under `A ∧ B ∧ ∃ P, C ∧ D ∧ E ∧ F`, delete `F`. -/
private def dropPacketConj (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``And, #[a, rest]) =>
    match rest.getAppFnArgs with
    | (``And, #[b, ex]) =>
      match ex with
      | .app (.app c ty) (.lam n d body bi) =>
        some (mkApp2 (mkConst ``And) a (mkApp2 (mkConst ``And) b
          (.app (.app c ty) (.lam n d (dropLastConj body) bi))))
      | _ => none
    | _ => none
  | _ => none

open Lean Meta in
/-- Statement correspondence with H01: same binders, conclusion = H01 conclusion minus the last packet conjunct. -/
private def projCorrespondence (oldN newN : Name) : MetaM (Bool × Bool) := do
  let env ← getEnv
  let some oldCi := env.find? oldN | throwError "missing {oldN}"
  let some newCi := env.find? newN | throwError "missing {newN}"
  forallTelescope oldCi.type fun xs told =>
    forallTelescope newCi.type fun ys tnew => do
      if xs.size != ys.size then throwError "telescope arity mismatch {xs.size} vs {ys.size}"
      let mut binders := true
      for i in [0:xs.size] do
        let tOld ← inferType xs[i]!
        let tNew ← inferType ys[i]!
        unless (tOld.replaceFVars xs ys) == tNew do binders := false
      let some dropped := dropPacketConj (told.replaceFVars xs ys)
        | throwError "unexpected shape of the H01 conclusion"
      let eqv := dropped == tnew
      let defeq ← isDefEq dropped tnew
      return (binders && eqv, binders && defeq)

open Lean Meta in
/-- Transitive closure of a root constant: held names and non-standard axioms are rejected. -/
private def transitiveAudit (root : Name) : MetaM (Nat × Nat) := do
  let env ← getEnv
  let mut pending : Array Name := #[root]
  let mut seen : Std.HashSet Name := {}
  let mut axioms : Nat := 0
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 || (n.toString.splitOn "RegularCut").length > 1 then
        throwError "held identifier in closure: {n}"
      let some ci := env.find? n | throwError "missing constant {n}"
      match ci with
      | .axiomInfo _ =>
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "nonstandard axiom in closure: {n}"
        axioms := axioms + 1
      | _ => pure ()
      pending := pending ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        pending := pending ++ v.getUsedConstants
  return (seen.size, axioms)

end QuantumNLS.Bind7B115CAA16H02

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let newN := ``QuantumNLS.Bind7B115CAA16H02.audit_weighted_printed
  let oldN := ``QuantumNLS.Bind7B115CAA16H01.audit_weighted_bound
  let (eqv, defeq) ← QuantumNLS.Bind7B115CAA16H02.projCorrespondence oldN newN
  unless eqv do throwError "statement correspondence FAILED (eqv={eqv}, defeq={defeq})"
  let (nConst, nAx) ← QuantumNLS.Bind7B115CAA16H02.transitiveAudit newN
  logInfo m!"Bind7B115CAA16H02 correspondence PASS: type = H01 type with the final multiplier-domain conjunct deleted (defeq {defeq}); closure {nConst} constants, {nAx} standard axioms, no held identifiers."

#print axioms QuantumNLS.Bind7B115CAA16H02.audit_weighted_printed

end
