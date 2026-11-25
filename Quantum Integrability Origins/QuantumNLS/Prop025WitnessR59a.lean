import QuantumNLS.Prop025OLow

/-! Open the existential introductions in the imported OPhase and OMain proof
terms. The elaborator emits ordinary Lean terms. It uses the constructor
witnesses when present and `Classical.choose_spec` for earlier existential
eliminations. The kernel checks the emitted terms at their new types. -/

set_option autoImplicit false

namespace QuantumNLS.Prop025WitnessR59a
open Lean Meta Elab Term

private def bodyOf (call : Expr) : MetaM Expr := do
  let .const name levels := call.getAppFn
    | throwError "Expected a fully applied frozen declaration, got {call}"
  let info ← getConstInfo name
  let some value := info.value? (allowOpaque := true)
    | throwError "Frozen declaration has no proof body: {name}"
  return (value.instantiateLevelParams info.levelParams levels).beta call.getAppArgs

/-- Walk only the prefix leading to the two exported witness introductions.
Keep preceding lets shared and drop unused lets on re-abstraction. -/
private partial def openPair (proof : Expr) (replace : Expr → MetaM Expr)
    (finish : Array Expr → Expr → MetaM Expr) (witnesses : Array Expr := #[])
    (boundLets : Array Expr := #[]) : MetaM Expr := do
  if witnesses.size == 2 then
    mkLetFVars boundLets (← finish witnesses proof) (generalizeNondepLet := false)
  else
    openStep proof.consumeMData
where
  openStep (proof : Expr) : MetaM Expr := do
    if let .letE name type value body _ := proof then
      return ← withLetDecl name type value fun localValue =>
        openPair (body.instantiate1 localValue) replace finish witnesses (boundLets.push localValue)
    let args := proof.getAppArgs
    let fn := proof.getAppFn.consumeMData
    if fn.isLambda then
      return ← openPair (fn.beta args) replace finish witnesses boundLets
    if let .letE name type value body _ := fn then
      return ← withLetDecl name type value fun localValue =>
        openPair (mkAppN (body.instantiate1 localValue) args)
          replace finish witnesses (boundLets.push localValue)
    let head := fn.constName?
    -- The frozen `set` steps insert casts between definitionally equal types.
    -- The resulting proof is checked again at the witness-specific type.
    if head == some ``Eq.mpr || head == some ``Eq.mp then
      return ← openPair args.back! replace finish witnesses boundLets
    if head == some ``Exists.intro then
      return ← openPair args[3]! replace finish (witnesses.push args[2]!) boundLets
    if head == some ``Exists.casesOn || head == some ``Exists.elim then
      let major := (← replace args[args.size - 2]!).consumeMData
      let next := args.back!
      if major.isAppOfArity ``Exists.intro 4 then
        let parts := major.getAppArgs
        return ← openPair (next.beta #[parts[2]!, parts[3]!]) replace finish witnesses boundLets
      -- Keep the potentially large existential predicate shared in the new term.
      return ← withLetDecl `existence (← inferType major) major fun existence => do
        let witness ← mkAppM ``Classical.choose #[existence]
        withLetDecl `witness (← inferType witness) witness fun w => do
          let spec ← mkAppM ``Classical.choose_spec #[existence]
          withLetDecl `spec (← inferType spec) spec fun hw =>
            openPair (next.beta #[w, hw]) replace finish witnesses (boundLets ++ #[existence, w, hw])
    if head == some ``And.casesOn || head == some ``And.elim then
      let pair := args[args.size - 2]!
      let left ← mkAppM ``And.left #[pair]
      let right ← mkAppM ``And.right #[pair]
      return ← openPair (args.back!.beta #[left, right]) replace finish witnesses boundLets
    throwError "Unexpected head before the fixed-contour witnesses (arity {args.size}): {fn}"

private def resultPair (witnesses : Array Expr) (_proof : Expr) : MetaM Expr :=
  mkAppM ``Prod.mk #[witnesses[0]!, witnesses[1]!]

/-- Open the proof with symbolic arguments, then abstract exactly the fixed
contour inputs. Any reference to a dropped argument makes elaboration fail. -/
elab "fixedContourPair%" : term => do
  let constant ← mkConstWithFreshMVarLevels ``Prop025OPhase.quantum_comparison
  let body ← bodyOf constant
  lambdaTelescope body fun args proof => do
    let names ← args.mapM fun arg => arg.fvarId!.getUserName
    let fixedNames := [`L, `κ, `hκ, `u, `hu, `μ, `hμ, `h, `hηh, `nI, `n]
    let fixed := args.zipIdx.filterMap fun (arg, i) =>
      if i == 1 || fixedNames.contains names[i]! then some arg else none
    unless fixed.size == 12 do
      throwError "OPhase fixed-contour binder list differs: {names}"
    -- OPhase obtained `0 < h` from its growing-window radius. Supply the
    -- same proposition directly from the fixed height condition. The old
    -- and new positivity proofs are definitionally equal by proof irrelevance.
    let fixedArg := fun name => args[(names.toList.idxOf name)]!
    let base := mkAppN (mkConst ``Prop017Quantum.eta0_pos) #[fixedArg `L, fixedArg `κ, fixedArg `hκ]
    let positiveHeight ← mkAppM ``lt_trans #[base, fixedArg `hηh]
    let proof := proof.replace fun term =>
      match term with
      | .letE `hh type _ body nondep => some (.letE `hh type positiveHeight body nondep)
      | _ => none
    let pair ← openPair proof pure resultPair
    let value ← mkLambdaFVars fixed pair
    if value.hasFVar then
      let used := collectFVars {} value
      let remaining ← used.fvarIds.mapM fun id => id.getUserName
      throwError "A fixed-contour witness depends on arguments outside the packet: {remaining}"
    return value

/-- Apply the first two existential predicates to the displayed sequence pair.
This is the unchanged tail of the frozen declaration's statement. -/
elab "packetTail% " source:term:max " using " pair:term:max : term => do
  let source ← elabTerm source none
  let pair ← elabTerm pair none
  let eta ← mkAppM ``Prod.fst #[pair]
  let rho ← mkAppM ``Prod.snd #[pair]
  let prop ← inferType source
  unless prop.isAppOfArity ``Exists 2 do
    throwError "Expected the first packet existential"
  let tail := prop.appArg!.beta #[eta]
  unless tail.isAppOfArity ``Exists 2 do
    throwError "Expected the second packet existential"
  return tail.appArg!.beta #[rho]

private def packetProof (source : Syntax) (replace : Expr → MetaM Expr) : TermElabM Expr := do
  let source ← elabTerm source none
  let source ← instantiateMVars source
  openPair (← bodyOf source) replace fun _ proof => pure proof

elab "packetProof% " source:term:max : term => packetProof source pure

/-- Reuse the frozen OMain proof tail, replacing its OPhase call with a proof
whose two existential introductions display the fixed witnesses explicitly. -/
elab "packetProofUsing% " source:term:max " replacing " old:ident " with " new:ident : term => do
  let fromName ← realizeGlobalConstNoOverloadWithInfo old
  let toName ← realizeGlobalConstNoOverloadWithInfo new
  packetProof source fun e => do
    if let .const n levels := e.getAppFn then
      if n == fromName then
        return ← bodyOf (mkAppN (mkConst toName levels) e.getAppArgs)
    return e

end QuantumNLS.Prop025WitnessR59a
