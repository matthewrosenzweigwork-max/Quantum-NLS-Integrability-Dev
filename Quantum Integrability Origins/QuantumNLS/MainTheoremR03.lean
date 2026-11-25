import QuantumNLS.MainTheoremR03Count

/-!
# MainTheoremR03: R-AF8F7562 `thm:main`, the six correspondence clauses — FINAL ASSEMBLY (no named inputs)

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex` (sha256 `6008c7e6…da56`) lines 2-102;
proof `source-text/chapters/core/correspondence_theorem.tex` (sha256 `769e5f29…8b56`) lines 1-66;
`source-text/chapters/core/canonical_algebra.tex` (sha256 `b2a1e9c4…0395`) lines 37-57 (sec:algebra).

Extends the frozen `MainTheoremR02` assembly (source `9281c0d6…`) by gap G1 only:

* G1 (part (iii), printed lines 42-51): `MainTheoremR03Count.G1Clause hκ q` — ordered words mixing Cartesian,
  unit-phase, count-function `f(B_{N,J})` and balanced Wick letters with product symbols and expectation convergence
  (dynamic, at `G q`), static words (uniform on `𝒰_R`), eq:dirac-main with `sup_N ‖N[A_N,C_N]‖ < ∞` for the
  first-order class `Expr J` (dynamic and static), and the regularized relative phases.  Content: sonnet_fourier's
  frozen `CountFunctionsS01*`.  `PartIII hκ q := MainTheoremR02.PartIII hκ q ∧ G1Clause hκ q`.
* Every other part is the R02 constant itself (`MainTheoremR02.PartI`, `.PartII`, `.PartV`, `.Coherence`,
  `MainTheoremR01.PartIV`, `.PartVI`); `statement_unfold` checks this by `rfl` and `r03_iff_r02_and_g1` /
  `r03_implies_r02` relate the headline to `MainTheoremR02.MainStatement`.

REVIEWER NOTES (sonnet_fourier, carried over): (1) eq:finite-difference is proved in uniform `o(1)` form, not
`O(N⁻¹)`; this suffices for the printed conclusions. (2) Static words exclude unit-phase letters, matching printed
part (ii)'s restriction of unit-phase symbols to classes with a positive lower bound on both actions.

HEADLINE `MainTheoremR03.thm_main (hκ : 0 < κ) : MainStatementR03 hκ`.  No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace QuantumNLS.MainTheoremR03

open QuantumNLS.UniformStaticR49b (SectorGauge)

variable {L κ : ℝ} [Fact (0 < L)]

/-- **Part (iii) (R03).** The R02 part (iii) (R-8362E5EB input, ordered Cartesian words and expectations, dynamic
balanced polynomial quantization, scaled bound) and the G1 clause at the same gauge `G q`. -/
def PartIII (hκ : 0 < κ) (q : SectorGauge) : Prop :=
  MainTheoremR02.PartIII (L := L) hκ q ∧ MainTheoremR03Count.G1Clause (L := L) hκ q

/-- **R-AF8F7562 `thm:main` (R03).** One sequence of occupation gauges with its active schedule, chosen before every
profile and parameter, with parts (i)-(vi) (part (iii) extended by G1) and the coherence of the evolved state. -/
def MainStatementR03 (hκ : 0 < κ) : Prop :=
  ∃ (j : ℕ → ℕ) (q : SectorGauge),
    MainTheoremR02.PartI (L := L) hκ ∧ MainTheoremR02.PartII (L := L) hκ j q ∧ PartIII (L := L) hκ q ∧
      MainTheoremR01.PartIV (L := L) hκ ∧ MainTheoremR02.PartV (L := L) hκ q ∧ MainTheoremR01.PartVI (L := L) hκ ∧
      MainTheoremR02.Coherence (L := L) hκ q

/-! ### Type-level checks: the R02 parts are unchanged -/

/-- The R03 statement is, definitionally, the R02 conjunction with part (iii) conjoined with G1. -/
theorem statement_unfold (hκ : 0 < κ) :
    MainStatementR03 (L := L) hκ =
      ∃ (j : ℕ → ℕ) (q : SectorGauge),
        MainTheoremR02.PartI (L := L) hκ ∧ MainTheoremR02.PartII (L := L) hκ j q ∧
          (MainTheoremR02.PartIII (L := L) hκ q ∧ MainTheoremR03Count.G1Clause (L := L) hκ q) ∧
          MainTheoremR01.PartIV (L := L) hκ ∧ MainTheoremR02.PartV (L := L) hκ q ∧
          MainTheoremR01.PartVI (L := L) hκ ∧ MainTheoremR02.Coherence (L := L) hκ q :=
  rfl

/-- The R02 headline statement, unfolded, is the same conjunction without G1. -/
theorem r02_statement_unfold (hκ : 0 < κ) :
    MainTheoremR02.MainStatement (L := L) hκ =
      ∃ (j : ℕ → ℕ) (q : SectorGauge),
        MainTheoremR02.PartI (L := L) hκ ∧ MainTheoremR02.PartII (L := L) hκ j q ∧
          MainTheoremR02.PartIII (L := L) hκ q ∧
          MainTheoremR01.PartIV (L := L) hκ ∧ MainTheoremR02.PartV (L := L) hκ q ∧
          MainTheoremR01.PartVI (L := L) hκ ∧ MainTheoremR02.Coherence (L := L) hκ q :=
  rfl

/-- R03 = R02 with G1 added at the same witnesses `(j, q)`. -/
theorem r03_iff_r02_and_g1 (hκ : 0 < κ) :
    MainStatementR03 (L := L) hκ ↔
      ∃ (j : ℕ → ℕ) (q : SectorGauge),
        (MainTheoremR02.PartI (L := L) hκ ∧ MainTheoremR02.PartII (L := L) hκ j q ∧
          MainTheoremR02.PartIII (L := L) hκ q ∧
          MainTheoremR01.PartIV (L := L) hκ ∧ MainTheoremR02.PartV (L := L) hκ q ∧
          MainTheoremR01.PartVI (L := L) hκ ∧ MainTheoremR02.Coherence (L := L) hκ q) ∧
        MainTheoremR03Count.G1Clause (L := L) hκ q := by
  constructor
  · rintro ⟨j, q, h1, h2, ⟨h3, hg⟩, h4, h5, h6, h7⟩
    exact ⟨j, q, ⟨h1, h2, h3, h4, h5, h6, h7⟩, hg⟩
  · rintro ⟨j, q, ⟨h1, h2, h3, h4, h5, h6, h7⟩, hg⟩
    exact ⟨j, q, h1, h2, ⟨h3, hg⟩, h4, h5, h6, h7⟩

/-- The R03 statement strengthens the R02 statement. -/
theorem r03_implies_r02 (hκ : 0 < κ) : MainStatementR03 (L := L) hκ → MainTheoremR02.MainStatement (L := L) hκ :=
  fun h => by
    obtain ⟨j, q, h1, h2, ⟨h3, _⟩, h4, h5, h6, h7⟩ := h
    exact ⟨j, q, h1, h2, h3, h4, h5, h6, h7⟩

/-! ### The theorem -/

theorem partIII (hκ : 0 < κ) : PartIII (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨(MainTheoremR02.thm_main_named (L := L) hκ).2.2.1, MainTheoremR03Count.g1_clause hκ⟩

/-- **R-AF8F7562 `thm:main` (R03), named witness** at the R-D51987CA named pair; the R02 parts are taken from the
frozen `MainTheoremR02.thm_main_named`. -/
theorem thm_main_named (hκ : 0 < κ) :
    MainTheoremR02.PartI (L := L) hκ ∧
    MainTheoremR02.PartII (L := L) hκ (RetargetSelectionR49b.particleStage (L := L) hκ)
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧
    PartIII (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧ MainTheoremR01.PartIV (L := L) hκ ∧
    MainTheoremR02.PartV (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧
    MainTheoremR01.PartVI (L := L) hκ ∧
    MainTheoremR02.Coherence (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := MainTheoremR02.thm_main_named (L := L) hκ
  exact ⟨h1, h2, ⟨h3, MainTheoremR03Count.g1_clause hκ⟩, h4, h5, h6, h7⟩

/-- **R-AF8F7562 `thm:main` (R03, HEADLINE).** Fix `L, κ > 0`. There is one sequence of occupation gauges, chosen
before the profile and all tested parameters, with properties (i)-(vi) — part (iii) now including the count-function
words and eq:dirac-main for the first-order class — and one evolved state. -/
theorem thm_main (hκ : 0 < κ) : MainStatementR03 (L := L) hκ :=
  ⟨_, _, thm_main_named hκ⟩

open Lean Meta in
/-- Transitive closure of a root constant: held names and non-standard axioms are rejected. -/
private def transitiveAudit (root : Name) : MetaM (Nat × Nat × Std.HashSet Name) := do
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

end QuantumNLS.MainTheoremR03

set_option maxHeartbeats 40000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  -- (1) binders of the headline: exactly {L} [Fact (0 < L)] {κ} (hκ : 0 < κ); no named theorem input.
  for root in [``QuantumNLS.MainTheoremR03.thm_main, ``QuantumNLS.MainTheoremR03.thm_main_named] do
    let ci ← getConstInfo root
    let names ← forallTelescope ci.type fun xs _ => do
      let mut out : Array Name := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        out := out.push d.userName
      return out
    unless names.size == 4 do throwError "{root}: unexpected binder count {names.size}"
    let explicitTy ← forallTelescope ci.type fun xs _ => do
      let d ← xs[3]!.fvarId!.getDecl
      instantiateMVars d.type
    unless explicitTy.isAppOfArity ``LT.lt 4 do throwError "{root}: last binder is not `0 < κ`"
    let (nConst, nAx, seen) ← QuantumNLS.MainTheoremR03.transitiveAudit root
    -- (2) the R02 named theorem and the frozen G1 finals are in the closure
    for req in [``QuantumNLS.MainTheoremR02.thm_main_named,
        ``QuantumNLS.CountFunctionsS01Final.g1a_dynamic_words, ``QuantumNLS.CountFunctionsS01Final.g1a_dynamic_expectation,
        ``QuantumNLS.CountFunctionsS01Final.g1b_dynamic_dirac, ``QuantumNLS.CountFunctionsS01Final.g1b_dynamic_expr_pair,
        ``QuantumNLS.CountFunctionsS01Words.static_words, ``QuantumNLS.CountFunctionsS01Dirac.static_dirac,
        ``QuantumNLS.CountFunctionsS01Dirac.static_expr_pair, ``QuantumNLS.CountFunctionsS01Phase.regPhase_cl,
        ``QuantumNLS.CountFunctionsS01Phase.cutoff_exists, ``QuantumNLS.UniformStaticR49b.selected_uniform_static,
        ``QuantumNLS.DynamicGaugeFinalR35m.audit_dynamic_gauge] do
      unless seen.contains req do throwError "{root}: {req} not in closure"
    logInfo m!"{root}: binders {names}; closure {nConst} constants, {nAx} standard axioms, no held identifiers."
  -- (3) the existential headline is witnessed by the named form.
  let main ← getConstInfo ``QuantumNLS.MainTheoremR03.thm_main
  let some v := main.value? (allowOpaque := true) | throwError "no value"
  unless v.getUsedConstants.contains ``QuantumNLS.MainTheoremR03.thm_main_named do
    throwError "thm_main is not proved from thm_main_named"
  -- (4) the statement uses the R02/R01 part constants themselves (no restated copies), and R03 PartIII contains
  --     the R02 PartIII constant.
  let st ← getConstInfo ``QuantumNLS.MainTheoremR03.MainStatementR03
  let some sv := st.value? | throwError "no statement value"
  for req in [``QuantumNLS.MainTheoremR02.PartI, ``QuantumNLS.MainTheoremR02.PartII,
      ``QuantumNLS.MainTheoremR03.PartIII, ``QuantumNLS.MainTheoremR01.PartIV, ``QuantumNLS.MainTheoremR02.PartV,
      ``QuantumNLS.MainTheoremR01.PartVI, ``QuantumNLS.MainTheoremR02.Coherence] do
    unless sv.getUsedConstants.contains req do throwError "MainStatementR03 does not use {req}"
  let p3 ← getConstInfo ``QuantumNLS.MainTheoremR03.PartIII
  let some pv := p3.value? | throwError "no PartIII value"
  for req in [``QuantumNLS.MainTheoremR02.PartIII, ``QuantumNLS.MainTheoremR03Count.G1Clause] do
    unless pv.getUsedConstants.contains req do throwError "PartIII does not use {req}"
  logInfo m!"MAIN_THEOREM_R03 AUDIT PASS (R02 parts referenced as constants; G1 finals in closure)"

#print axioms QuantumNLS.MainTheoremR03.statement_unfold
#print axioms QuantumNLS.MainTheoremR03.r02_statement_unfold
#print axioms QuantumNLS.MainTheoremR03.r03_iff_r02_and_g1
#print axioms QuantumNLS.MainTheoremR03.r03_implies_r02
#print axioms QuantumNLS.MainTheoremR03.thm_main
#print axioms QuantumNLS.MainTheoremR03.thm_main_named
