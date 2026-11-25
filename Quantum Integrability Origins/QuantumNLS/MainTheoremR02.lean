import QuantumNLS.MainTheoremR02Phase
import QuantumNLS.MainTheoremR02Carrier
import QuantumNLS.MainTheoremR02Weights
import QuantumNLS.MainTheoremR02Wick
import QuantumNLS.SupportPersistH01Transfer

/-!
# MainTheoremR02: R-AF8F7562 `thm:main`, the six correspondence clauses — EXTENDED ASSEMBLY (no named inputs)

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex` (sha256 `6008c7e6…da56`) lines 2-102;
proof `source-text/chapters/core/correspondence_theorem.tex` (sha256 `769e5f29…8b56`) lines 1-66.
Extends the frozen `MainTheoremR01` assembly (source `46da0952…`) following review record r107:

* G3 (part (v), line 71, "determines the nonlinear Fourier ray at the prescribed mass, and loses exactly the
  common phase"): `MainTheoremR02Phase.CommonPhaseClause` (prop:obstruction formulation,
  projective_reconstruction.tex:392-398), conjoined to part (v).
* Carrier/propagator coherence (lines 36-38, 49-52, 65-71): `MainTheoremR02Carrier.CommonState` — the part (iv)
  propagator `chargeUnitary` on `HN L (N+1)` and the part (iii)/(v) propagator `ReconstructionR33m.U` on
  `HN L (1+n)` are intertwined by `castHN (Nat.add_comm n 1)`, the preparation classes correspond, every
  (iii)/(v) property transfers, and the (iii) symbols, (iv) marginals and (v) matrix conclusions hold
  simultaneously for one preparation and one evolved state.  New conjunct `Coherence`.
* Weight equivalence (lines 16-21): `MainTheoremR02Weights.WeightEquivalence`, conjoined to part (i).
* Full-wick (lines 31-33, 52-53): rebound to the frozen accepted final `FullWickFinalH15.thm_full_wick_Q06_final`
  (`MainTheoremR02Wick`), statements at the single gauge `G q`.
* G2 (part (ii), line 31, support persistence): the auxiliary construction's frozen `SupportPersistH01Transfer.support_persistence`
  (`selected_support_persistence` at the named witness), new conjunct `SupportPersistence` of part (ii).
* G1 (part (iii), lines 42-47, continuous count functions and the general `C²` Dirac statement): NOT included in
  this module (sonnet_fourier's `CountFunctionsS01*` not frozen at assembly time).

HEADLINE `MainTheoremR02.thm_main (hκ : 0 < κ) : MainStatement hκ`.  No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.MainTheoremR02

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.WickSymbols (Sym Balanced)
open QuantumNLS.WickBounds (labelsOf)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox)
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
open QuantumNLS.UniformStaticR49b (SectorGauge UniformStatic)
open QuantumNLS.MainTheoremR01 (G F)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ### Part (i): values, actions, and the weight equivalence -/

/-- **Part (i).** `MainTheoremR01.PartI` (packets, values, support-uniform statement, energy preparation,
eq:actions-main, the weight comparison and the `(1+|n|)^p` conclusion) and, for every smooth unit profile, the
weight equivalence: summability of both actual series, the two-sided comparison of the actual sums, and for each
fixed `p ≥ 0` the equivalence of the two weighted conclusions. -/
def PartI (hκ : 0 < κ) : Prop :=
  MainTheoremR01.PartI (L := L) hκ ∧
    ∀ (u : Smooth L) (hu : ‖physical u‖ = 1), MainTheoremR02Weights.WeightEquivalence (L := L) hκ u hu

/-! ### Part (ii): uniform static symbols, support persistence, full-wick static -/

/-- Persistence of the support conclusions (G2, line 31): for every family of preparations `ψ_N(u)` normalized on
`𝒰_R` and uniformly norm-close to `u^{⊗N}` (sup form), the missing initial and final Born support probabilities
vanish uniformly over `𝒰_R` and the eligible pairs of the active set with both actions `≥ α`. -/
def SupportPersistence (hκ : 0 < κ) (j : ℕ → ℕ) : Prop :=
  ∀ (ψ : ∀ n : ℕ, L2T L → HN L (n + 1)) {R : ℝ}, 0 < R → ∀ {α : ℝ}, 0 < α →
    SupportPersistH01Transfer.NormalizedOn (L := L) R ψ → SupportPersistH01Transfer.UniformlyClose (L := L) R ψ →
    Tendsto (fun n => UniformStaticR49b.supMax (RetargetRoughR48b.unitBall (L := L) R)
        (UniformStaticR49b.eligible hκ (j (n + 1)) α)
        (fun u p => SupportPersistH01Born.bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) p.1 (ψ n u)))
        atTop (𝓝 0) ∧
    Tendsto (fun n => UniformStaticR49b.supMax (RetargetRoughR48b.unitBall (L := L) R)
        (UniformStaticR49b.eligible hκ (j (n + 1)) α)
        (fun u p => SupportPersistH01Born.bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) p.2 (ψ n u)))
        atTop (𝓝 0)

/-- **Part (ii).** R-D2F4CE8F `UniformStatic`; eq:uniform-projective-main with its norm-close, column and inverse
conclusions (R-98833BEE); strong-symbol persistence; support persistence (G2); the static balanced polynomial
quantization (R-140AE34B, H15 conjuncts 1-6, 10-13) at the single gauge `G q`. -/
def PartII (hκ : 0 < κ) (j : ℕ → ℕ) (q : SectorGauge) : Prop :=
  UniformStatic (L := L) hκ j q ∧
  UniformProjR01.UniformProjectiveStatement98833BEE (L := L) hκ (UniformStaticBridgeR50b.toFullGauge q) ∧
  MainTheoremR01Static.StaticPersistence (L := L) hκ j q ∧
  SupportPersistence (L := L) hκ j ∧
  MainTheoremR02Wick.FullWickStatic (L := L) hκ (G q)

/-! ### Part (iii): dynamics -/

/-- **Part (iii).** R-8362E5EB (Cartesian all pairs incl. collapsed actions, positive-action phases, adjoints,
compact boxes, norm-close preparations); ordered Cartesian words with their adjoints and expectations; the dynamic
balanced polynomial quantization (H15 conjuncts 7, 8, 9, 14) at `G q`; `sup_N ‖N[A_N,C_N]‖ < ∞`. -/
def PartIII (hκ : 0 < κ) (q : SectorGauge) : Prop :=
  RD8362E5EBInput hκ (F (L := L) hκ) (G q) ∧
  (∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ → ∀ (w : List (ℤ × ℤ)),
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (w.map fun p => ReconstructionR33m.E (L := L) hκ (G q) n p.1 p.2).prod)
      (fun n => ((w.map fun p => (ReconstructionR33m.E (L := L) hκ (G q) n p.1 p.2).adjoint).reverse).prod)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        (w.map fun p => (ReconstructionR33m.w hκ (F hκ) u R t : ℤ → ℂ) p.1 *
          conj ((ReconstructionR33m.w hκ (F hκ) u R t : ℤ → ℂ) p.2)).prod) ∧
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ TimeBox R lo hi,
      ‖⟪ReconstructionR33m.U (L := L) hκ R t n (ψ n),
          (w.map fun p => ReconstructionR33m.E (L := L) hκ (G q) n p.1 p.2).prod
            (ReconstructionR33m.U (L := L) hκ R t n (ψ n))⟫_ℂ -
        (w.map fun p => (ReconstructionR33m.w hκ (F hκ) u R t : ℤ → ℂ) p.1 *
          conj ((ReconstructionR33m.w hκ (F hκ) u R t : ℤ → ℂ) p.2)).prod‖ ≤ ε) ∧
  MainTheoremR02Wick.FullWickDynamic (L := L) hκ (G q) ∧
  (∀ {f h : Sym}, Balanced f → Balanced h → ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf h ⊆ S →
    ∃ M : ℝ, ∀ n : ℕ,
      ‖((1 + n : ℕ) : ℂ) •
        (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) f *
            BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) h -
          BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) h *
            BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) f)‖ ≤ M)

/-! ### Part (v) with the exact common-phase characterization -/

/-- **Part (v).** `MainTheoremR01.PartV` (positivity, trace one, entries, eq:projective-main, columns,
normalized-column inverse at `G q`) and the G3 clause `CommonPhaseClause` for the same flows and chart. -/
def PartV (hκ : 0 < κ) (q : SectorGauge) : Prop :=
  MainTheoremR01.PartV (L := L) hκ q ∧ MainTheoremR02Phase.CommonPhaseClause (L := L) hκ (F (L := L) hκ)

/-! ### Coherence: one preparation, one propagator, one evolved state -/

/-- **Coherence of parts (iii)-(v)** at the single gauge `G q` and the actual flows. -/
def Coherence (hκ : 0 < κ) (q : SectorGauge) : Prop :=
  MainTheoremR02Carrier.CommonState (L := L) hκ (F (L := L) hκ) (G q)

/-! ### The theorem -/

/-- **R-AF8F7562 `thm:main` (R02).** One sequence of occupation gauges with its active schedule, chosen before every
profile and parameter, with parts (i)-(vi) and the coherence of the evolved state. -/
def MainStatement (hκ : 0 < κ) : Prop :=
  ∃ (j : ℕ → ℕ) (q : SectorGauge),
    PartI (L := L) hκ ∧ PartII (L := L) hκ j q ∧ PartIII (L := L) hκ q ∧ MainTheoremR01.PartIV (L := L) hκ ∧
      PartV (L := L) hκ q ∧ MainTheoremR01.PartVI (L := L) hκ ∧ Coherence (L := L) hκ q

theorem partI (hκ : 0 < κ) : PartI (L := L) hκ :=
  ⟨MainTheoremR01.partI hκ, fun u hu => MainTheoremR02Weights.weight_equivalence hκ u hu⟩

theorem partII (hκ : 0 < κ) :
    PartII (L := L) hκ (RetargetSelectionR49b.particleStage (L := L) hκ)
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨UniformStaticR49b.selected_uniform_static hκ, UniformProjFinalR02.uniform_projective_final hκ,
    MainTheoremR01Static.static_persistence hκ (UniformStaticR49b.selected_uniform_static hκ),
    fun ψ _ hR _ hα hn hc => SupportPersistH01Transfer.selected_support_persistence hκ ψ hR hα hn hc,
    (MainTheoremR02Wick.fullWick_G hκ).1⟩

theorem partIII (hκ : 0 < κ) : PartIII (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) := by
  have D : RD8362E5EBInput hκ (F (L := L) hκ) (G (RetargetSelectionR49b.sectorGauge (L := L) hκ)) :=
    DynamicGaugeFinalR35m.audit_dynamic_gauge hκ
  have hW := MainTheoremR02Wick.fullWick_G (L := L) hκ
  refine ⟨D, fun u hu R lo hi ψ hψ w =>
      ⟨MainTheoremR02Wick.cartesian_words_of hκ _ hW.2.2.2.1 u hu R lo hi ψ hψ w,
        MainTheoremR02Wick.cartesian_word_expectation_of hκ _ hW.2.2.2.1 u hu R lo hi ψ hψ w⟩,
    hW.2, fun hf hh S hSf hSh => MainTheoremR01Algebra.dirac_scaled_bound hκ _ hf hh hSf hSh⟩

theorem partV (hκ : 0 < κ) : PartV (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨MainTheoremR01.partV hκ,
    MainTheoremR02Phase.common_phase_clause hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)
      (F (L := L) hκ)⟩

theorem coherence (hκ : 0 < κ) : Coherence (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  MainTheoremR02Carrier.common_state hκ _ (DynamicGaugeFinalR35m.audit_dynamic_gauge hκ)
    (MainTheoremR01Physical.physical_marginal hκ) (ReconstructionFinalR35m.reconstruction hκ)

/-- **R-AF8F7562 `thm:main` (R02), named witness** at the R-D51987CA named pair. -/
theorem thm_main_named (hκ : 0 < κ) :
    PartI (L := L) hκ ∧
    PartII (L := L) hκ (RetargetSelectionR49b.particleStage (L := L) hκ)
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧
    PartIII (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧ MainTheoremR01.PartIV (L := L) hκ ∧
    PartV (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧ MainTheoremR01.PartVI (L := L) hκ ∧
    Coherence (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨partI hκ, partII hκ, partIII hκ, MainTheoremR01.partIV hκ, partV hκ, MainTheoremR01.partVI hκ, coherence hκ⟩

/-- **R-AF8F7562 `thm:main` (R02, HEADLINE).** Fix `L, κ > 0`. There is one sequence of occupation gauges, chosen
before the profile and all tested parameters, with properties (i)-(vi) (extended as above) and one evolved state. -/
theorem thm_main (hκ : 0 < κ) : MainStatement (L := L) hκ :=
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

end QuantumNLS.MainTheoremR02

set_option maxHeartbeats 40000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  -- (1) binders of the headline: exactly {L} [Fact (0 < L)] {κ} (hκ : 0 < κ); no named theorem input.
  for root in [``QuantumNLS.MainTheoremR02.thm_main, ``QuantumNLS.MainTheoremR02.thm_main_named] do
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
    let (nConst, nAx, seen) ← QuantumNLS.MainTheoremR02.transitiveAudit root
    -- (2) the rebinding and integration targets are in the closure
    for req in [``QuantumNLS.FullWickFinalH15.thm_full_wick_Q06_final, ``QuantumNLS.SupportPersistH01Transfer.support_persistence,
        ``QuantumNLS.MainTheoremR02Phase.common_phase_clause, ``QuantumNLS.MainTheoremR02Carrier.common_state,
        ``QuantumNLS.MainTheoremR02Weights.weight_equivalence] do
      unless seen.contains req do throwError "{root}: {req} not in closure"
    logInfo m!"{root}: binders {names}; closure {nConst} constants, {nAx} standard axioms, no held identifiers."
  -- (3) the existential headline is witnessed by the named form.
  let main ← getConstInfo ``QuantumNLS.MainTheoremR02.thm_main
  let some v := main.value? (allowOpaque := true) | throwError "no value"
  unless v.getUsedConstants.contains ``QuantumNLS.MainTheoremR02.thm_main_named do
    throwError "thm_main is not proved from thm_main_named"
  -- (4) no R02 module proof term refers directly to the v3 full-wick clause terms or to the R01 full-wick proofs.
  let env ← getEnv
  let banned : List Name := [``QuantumNLS.FullWickH10.static_clause, ``QuantumNLS.FullWickH10.static_normClose_clause,
    ``QuantumNLS.FullWickH10.dynamic_clause, ``QuantumNLS.FullWickH10.dynamic_dirac_clause,
    ``QuantumNLS.FullWickH10.dynamic_word_clause, ``QuantumNLS.FullWickH13.dynamic_poly_product_clause,
    ``QuantumNLS.FullWickH14.thm_full_wick_printed_v3, ``QuantumNLS.MainTheoremR01.fullWickStatic,
    ``QuantumNLS.MainTheoremR01.partII, ``QuantumNLS.MainTheoremR01.partIII,
    ``QuantumNLS.MainTheoremR01Algebra.cartesian_words, ``QuantumNLS.MainTheoremR01Algebra.cartesian_word_expectation]
  let mut own : Nat := 0
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if s.startsWith "QuantumNLS.MainTheoremR02" || s.startsWith "_private.QuantumNLS.MainTheoremR02" then
      own := own + 1
      if let some v := ci.value? (allowOpaque := true) then
        for b in banned do
          if v.getUsedConstants.contains b then throwError "{n} uses {b} directly"
  logInfo m!"MAIN_THEOREM_R02 AUDIT PASS ({own} own R02 constants; no direct v3 full-wick term)"

#print axioms QuantumNLS.MainTheoremR02.thm_main
#print axioms QuantumNLS.MainTheoremR02.thm_main_named
