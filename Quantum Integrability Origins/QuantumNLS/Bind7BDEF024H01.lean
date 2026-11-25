import Mathlib
import QuantumNLS.Def024LossProfileR32m
import QuantumNLS.RB7BindFinal
import QuantumNLS.RB7HClauses45b
import QuantumNLS.HierarchyFlow

/-!
# Bind7BDEF024H01: DEF-024 (fixed smooth joint hierarchy flow), binding, ready to promote

Printed source: `source-text/chapters/definitions.tex:145-149` (`def:report-24`, DEF-024):
"For a fixed finite set of nonnegative orders `𝓡`, the joint classical flow is the composition of the
Hamiltonian flows of `I_{r+1}^{(κ)}`, and the quantum flow is `U_N(t) = exp(-i Σ_{r∈𝓡} t_r Q_{N,r})`.
The correspondence tests a fixed smooth unit initial field and a fixed compact box of times.
Existence and commutation of the higher classical flows are proved with finite loss."

Realization: `QuantumNLS.HierarchyFlow` (`HamFlows`, `jointClassicalFlow`, `quantumFlow`, `TestData`).

Conjuncts of `DEF024_bound`, each equal to a frozen theorem or frozen Prop (see `receipt.md` for the sentence map):
* (a) `RB7.Clause1 ∧ RB7.Clause2` for every `𝓡`: existence, uniqueness and group law of each higher flow,
  existence and uniqueness of the family, composition over every ordering, and commutation. This is the
  first two components of the frozen `RB7.HierarchyAll`, taken from `RB7HBridge.hierarchy_all_unconditional`.
* (b) finite loss at every order: `Def024LossR32m.finite_loss_all_orders`.
* (c) for every `𝓡`, a Hamiltonian family whose joint flow is `C^∞` in all times and space for every smooth
  datum, and every family has this property: `Def024LossR32m.joint_contDiff_ofInput`, whose single hierarchy
  binder `HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ` is supplied by
  `RB7BindFinal.hierarchyInputR25m_unconditional`.
* (d) every test box `TestData.box` is compact: `HierarchyFlow.TestData.isCompact_box`.
* (e) the quantum flow in a Bethe basis, with Bethe coefficients `exp(-i Σ_{r∈𝓡} t_r Λ_{N,r}(m))`:
  `HierarchyFlow.quantumFlow_coord`.

Hypotheses: only `hκ : 0 < κ` (with `Fact (0 < L)`), the standing period and coupling of the frozen chain.
The hierarchy input is discharged by `RB7BindFinal.hierarchyInputR25m_unconditional`.

Not promoted. R-7B122087 is HELD for the owner ruling on the DEF-024 mutual gate. This module makes no
acceptance claim and is not imported by any other module.
-/

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.Bind7BDEF024H01

variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 4000000 in
/-- **DEF-024 for every finite order set `𝓡`**, with the shared hierarchy input discharged. -/
theorem DEF024_bound (hκ : 0 < κ) :
    -- (a) existence, uniqueness and commutation of the higher classical flows, every finite 𝓡
    (∀ 𝓡 : Finset ℕ, QuantumNLS.RB7.Clause1 L κ 𝓡 ∧ QuantumNLS.RB7.Clause2 L κ 𝓡) ∧
    -- (b) finite loss, at every order
    (∃ C : QuantumNLS.RB7.ChartFacts (L := L) hκ, ∀ (r m : ℕ) (q : NNReal),
      QuantumNLS.Def024LossR32m.OrderFiniteLoss
        (QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ) C r m q) ∧
    -- (c) joint classical flow: composition of Hamiltonian flows, jointly C^∞ in all times and space
    (∀ 𝓡 : Finset ℕ,
      (∃ F : QuantumNLS.HierarchyFlow.HamFlows L κ 𝓡, ∀ u : ℝ → ℂ,
          QuantumNLS.ClassicalCharges.SmoothPeriodic L u → QuantumNLS.Def024LossR32m.JointContDiff F u) ∧
      ∀ (F : QuantumNLS.HierarchyFlow.HamFlows L κ 𝓡) (u : ℝ → ℂ),
          QuantumNLS.ClassicalCharges.SmoothPeriodic L u → QuantumNLS.Def024LossR32m.JointContDiff F u) ∧
    -- (d) the fixed compact box of joint times
    (∀ D : QuantumNLS.HierarchyFlow.TestData L, IsCompact D.box) ∧
    -- (e) the quantum flow U_N(t) = exp(-i Σ_{r∈𝓡} t_r Q_{N,r}) in a Bethe basis
    (∀ (N : ℕ) (b : QuantumNLS.BetheCoefficientTransform.BetheBasis L N) (c : ℝ) (𝓡 : Finset ℕ)
      (t : ℕ → ℝ) (ψ : QuantumNLS.BetheCoefficientTransform.HN L N)
      (m : QuantumNLS.BetheLabels.MArr N),
      ⟪b m, QuantumNLS.HierarchyFlow.quantumFlow b c 𝓡 t ψ⟫_ℂ =
        Complex.exp (-((∑ r ∈ 𝓡, t r * QuantumNLS.BetheSpectralCharges.eigenvalue L N (c / N) r m : ℝ) : ℂ)
          * Complex.I) * ⟪b m, ψ⟫_ℂ) := by
  have hier : ∀ 𝓡 : Finset ℕ, QuantumNLS.RB7.Clause1 L κ 𝓡 ∧ QuantumNLS.RB7.Clause2 L κ 𝓡 := by
    intro 𝓡
    have h := QuantumNLS.RB7HBridge.hierarchy_all_unconditional (L := L) hκ 𝓡
    unfold QuantumNLS.RB7.HierarchyAll at h
    exact ⟨h.1, h.2.1⟩
  exact ⟨hier,
    QuantumNLS.Def024LossR32m.finite_loss_all_orders (L := L) hκ,
    fun 𝓡 => QuantumNLS.Def024LossR32m.joint_contDiff_ofInput (L := L) hκ
      (QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ) 𝓡,
    fun D => QuantumNLS.HierarchyFlow.TestData.isCompact_box D,
    fun N b c 𝓡 t ψ m => QuantumNLS.HierarchyFlow.quantumFlow_coord b c 𝓡 t ψ m⟩

end QuantumNLS.Bind7BDEF024H01

namespace QuantumNLS.Bind7BDEF024H01

open Lean Meta

/-- Right-nested conjunction components: the left component of each `And` node, then the tail. -/
partial def andParts (e : Expr) : List Expr :=
  if e.isAppOfArity ``And 2 then e.appFn!.appArg! :: andParts e.appArg! else [e]

/-- Transitive closure of a root constant, through types and available values. It rejects held
identifiers and every axiom other than `propext`, `Classical.choice`, `Quot.sound`. It returns the number
of constants, the number of axioms, and the visited names. -/
def transitiveAudit (root : Name) : MetaM (Nat × Nat × Std.HashSet Name) := do
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
  return (seen.size, axioms, seen)

end QuantumNLS.Bind7BDEF024H01

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let mainCi ← getConstInfo ``QuantumNLS.Bind7BDEF024H01.DEF024_bound
  forallTelescope mainCi.type fun xs body => do
    unless xs.size == 4 do throwError "unexpected binder count {xs.size}"
    let Lf := xs[0]!
    let kf := xs[1]!
    let instf := xs[2]!
    let hk := xs[3]!
    let parts := QuantumNLS.Bind7BDEF024H01.andParts body
    unless parts.length == 5 do throwError "unexpected conjunct count {parts.length}"
    -- (a) `HierarchyAll` unfolds to `Clause1 ∧ Clause2 ∧ ...`; the first two components are the conjunct.
    let hT ← inferType (mkAppN (mkConst ``QuantumNLS.RB7HBridge.hierarchy_all_unconditional)
      #[Lf, kf, instf, hk])
    let okA ← forallTelescope hT fun ys hb => do
      let w ← whnfD hb
      unless w.isAppOfArity ``And 2 do throwError "HierarchyAll does not unfold to a conjunction"
      let c1 := w.appFn!.appArg!
      let r ← whnfD w.appArg!
      unless r.isAppOfArity ``And 2 do throwError "HierarchyAll has fewer than two conjuncts"
      let c2 := r.appFn!.appArg!
      isDefEq (← mkForallFVars ys (mkAppN (mkConst ``And) #[c1, c2])) parts[0]!
    -- (b) finite loss: the frozen statement, with its own binders instantiated by the main binders.
    let lossT ← getConstInfo ``QuantumNLS.Def024LossR32m.finite_loss_all_orders
    let okB ← isDefEq lossT.type (← mkForallFVars #[Lf, kf, instf, hk] parts[1]!)
    -- (c) joint flow: the shared hierarchy binder is the first binder after the four leading ones.
    let jT ← inferType (mkAppN (mkConst ``QuantumNLS.Def024LossR32m.joint_contDiff_ofInput)
      #[Lf, kf, instf, hk])
    unless jT.isForall do throwError "joint_contDiff_ofInput: no shared hierarchy binder"
    let sharedOk := jT.bindingDomain!.getAppFn.isConstOf
      ``QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input
    let hiW := mkAppN (mkConst ``QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional)
      #[Lf, kf, instf, hk]
    let okC0 ← isDefEq (← inferType hiW) jT.bindingDomain!
    let okC ← isDefEq (jT.bindingBody!.instantiate1 hiW) parts[2]!
    -- (d) the test box: `TestData.isCompact_box`.
    let tT ← getConstInfo ``QuantumNLS.HierarchyFlow.TestData.isCompact_box
    let okD ← isDefEq tT.type (← mkForallFVars #[Lf] parts[3]!)
    -- (e) the quantum flow coordinates: `quantumFlow_coord`, with its implicit `L` and instance.
    let qT ← getConstInfo ``QuantumNLS.HierarchyFlow.quantumFlow_coord
    let okE ← isDefEq qT.type (← mkForallFVars #[Lf, instf] parts[4]!)
    unless okA && okB && okC0 && okC && okD && okE && sharedOk do
      throwError "correspondence FAILED: (a)={okA} (b)={okB} (c-binder)={okC0} (c)={okC} (c-shared)={sharedOk} (d)={okD} (e)={okE}"
    let (nConst, nAx, seen) ← QuantumNLS.Bind7BDEF024H01.transitiveAudit
      ``QuantumNLS.Bind7BDEF024H01.DEF024_bound
    for n in [``QuantumNLS.RB7HBridge.hierarchy_all_unconditional,
        ``QuantumNLS.Def024LossR32m.finite_loss_all_orders,
        ``QuantumNLS.Def024LossR32m.joint_contDiff_ofInput,
        ``QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional,
        ``QuantumNLS.HierarchyFlow.TestData.isCompact_box,
        ``QuantumNLS.HierarchyFlow.quantumFlow_coord] do
      unless seen.contains n do throwError "provenance constant missing from closure: {n}"
    logInfo m!"Bind7BDEF024H01 correspondence PASS: each conjunct is definitionally the frozen statement (a) RB7HBridge.hierarchy_all_unconditional (Clause1 and Clause2 of HierarchyAll), (b) Def024LossR32m.finite_loss_all_orders, (c) Def024LossR32m.joint_contDiff_ofInput with its shared binder discharged by RB7BindFinal.hierarchyInputR25m_unconditional, (d) HierarchyFlow.TestData.isCompact_box, (e) HierarchyFlow.quantumFlow_coord; closure {nConst} constants, {nAx} standard axioms, no held identifiers."

#print axioms QuantumNLS.Bind7BDEF024H01.DEF024_bound
