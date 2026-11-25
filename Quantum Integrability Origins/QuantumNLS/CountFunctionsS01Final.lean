import QuantumNLS.CountFunctionsS01Phase
import QuantumNLS.DynamicGaugeFinalR35m

/-!
# CountFunctionsS01Final: gap G1 of R-AF8F7562 `thm:main` part (iii), discharged at the final R-8362E5EB input

PRINTED STATEMENT (`source-text/chapters/principal_correspondence.tex` lines 42-47, sha256 `6008c7e6…da56`):
  "Every fixed ordered word in these bounded observables, their adjoints, and continuous functions of finitely many
   intensive counts has the product of the corresponding scalar symbols, in the same strong and compact-time-uniform
   sense. In particular, its expectation converges. For finite expressions made from the Cartesian transfers and `C²`
   functions of finitely many counts, with classical expressions `A,C`, (eq:dirac-main) ... The precise `C²` class and
   regularized relative phases are given in Section sec:algebra."
PROOF SOURCE: `source-text/chapters/core/canonical_algebra.tex` lines 37-57 (sec:algebra) and
`source-text/chapters/core/correspondence_theorem.tex` lines 33-36.

The four theorems below instantiate the generic theorems of `CountFunctionsS01Words` and `CountFunctionsS01Dirac` at
the FINAL binding of R-8362E5EB, `DynamicGaugeFinalR35m.audit_dynamic_gauge hκ : RD8362E5EBInput hκ F G` with
`F = flows hκ hierarchy` and `G = DynamicGaugeFinalR35m.gauge hκ` (the gauge of the R-D51987CA named pair, the one
`MainTheoremR01.gauge_named` identifies with `G (sectorGauge hκ)`).  No new named theorem input; the only hypotheses
are `hκ`, the profile `u` with its unit norm, the finite index set, the compact box and the norm-close preparation.
No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace
open QuantumNLS CountFunctionsS01Ops CountFunctionsS01Calc CountFunctionsS01Poisson CountFunctionsS01Class
open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.ReconstructionR33m (Preparation TimeBox)

namespace QuantumNLS.CountFunctionsS01Final

variable {L κ : ℝ} [Fact (0 < L)]

/-- **G1(a), dynamic: ordered words with count functions.** -/
theorem g1a_dynamic_words (hκ : 0 < κ) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (l : List CountFunctionsS01Words.WLetter)
    (hl : ∀ ℓ ∈ l, CountFunctionsS01Words.Adm hκ u ℓ.base) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (l.map fun ℓ => CountFunctionsS01Words.wOp hκ (DynamicGaugeFinalR35m.gauge (L := L) hκ) n ℓ).prod)
      (fun n => ((l.map fun ℓ =>
        (CountFunctionsS01Words.wOp hκ (DynamicGaugeFinalR35m.gauge (L := L) hκ) n ℓ).adjoint).reverse).prod)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        (l.map fun ℓ => CountFunctionsS01Words.wSym
          (ReconstructionR33m.w hκ (ReconstructionR33m.flows hκ (DynamicGaugeFinalR35m.hierarchy (L := L) hκ))
            u R t : ℤ → ℂ) ℓ).prod) :=
  CountFunctionsS01Words.dynamic_words hκ _ _ (DynamicGaugeFinalR35m.audit_dynamic_gauge (L := L) hκ) u hu R lo hi
    ψ hψ l hl

/-- **G1(a), dynamic: the expectation of such a word converges** ("In particular, its expectation converges"). -/
theorem g1a_dynamic_expectation (hκ : 0 < κ) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (l : List CountFunctionsS01Words.WLetter)
    (hl : ∀ ℓ ∈ l, CountFunctionsS01Words.Adm hκ u ℓ.base) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ TimeBox R lo hi,
      ‖⟪ReconstructionR33m.U (L := L) hκ R t n (ψ n),
          (l.map fun ℓ => CountFunctionsS01Words.wOp hκ (DynamicGaugeFinalR35m.gauge (L := L) hκ) n ℓ).prod
            (ReconstructionR33m.U (L := L) hκ R t n (ψ n))⟫_ℂ -
        (l.map fun ℓ => CountFunctionsS01Words.wSym
          (ReconstructionR33m.w hκ (ReconstructionR33m.flows hκ (DynamicGaugeFinalR35m.hierarchy (L := L) hκ))
            u R t : ℤ → ℂ) ℓ).prod‖ ≤ ε :=
  CountFunctionsS01Words.dynamic_word_expectation hκ _ _
    (DynamicGaugeFinalR35m.audit_dynamic_gauge (L := L) hκ) u hu R lo hi ψ hψ l hl

/-- **G1(b), dynamic: eq:dirac-main for the first-order class.** -/
theorem g1b_dynamic_dirac (hκ : 0 < κ) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) {J : Finset ℤ} (A C : Expr J) :
    HasUniformStrongT (H := fun n => HN L (1 + n))
      (fun n => (-Complex.I * ((1 + n : ℕ) : ℂ)) •
        (A.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ) *
            C.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ) -
          C.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ) *
            A.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ)))
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        poisson A.cl C.cl (CountFunctionsS01Dirac.res J
          (ReconstructionR33m.w hκ (ReconstructionR33m.flows hκ (DynamicGaugeFinalR35m.hierarchy (L := L) hκ))
            u R t : ℤ → ℂ))) ∧
    ∃ M : ℝ, ∀ n : ℕ,
      ‖((1 + n : ℕ) : ℂ) •
        (A.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ) *
            C.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ) -
          C.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ) *
            A.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ))‖ ≤ M :=
  CountFunctionsS01Dirac.dynamic_dirac hκ _ _ (DynamicGaugeFinalR35m.audit_dynamic_gauge (L := L) hκ) u hu R lo hi
    ψ hψ A C

/-- **G1(b), dynamic: every expression of the first-order class has its classical expression as strong symbol.** -/
theorem g1b_dynamic_expr_pair (hκ : 0 < κ) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) {J : Finset ℤ} (A : Expr J) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => A.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ))
      (fun n => (A.op (ReconstructionR33m.basis (L := L) hκ n) (DynamicGaugeFinalR35m.gauge (L := L) hκ)).adjoint)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        A.cl (CountFunctionsS01Dirac.res J
          (ReconstructionR33m.w hκ (ReconstructionR33m.flows hκ (DynamicGaugeFinalR35m.hierarchy (L := L) hκ))
            u R t : ℤ → ℂ))) :=
  CountFunctionsS01Dirac.dynamic_expr_pair hκ _ _ (DynamicGaugeFinalR35m.audit_dynamic_gauge (L := L) hκ) u hu R lo hi
    ψ hψ A

end QuantumNLS.CountFunctionsS01Final

#print axioms QuantumNLS.CountFunctionsS01Ops.cntH_comm_E
#print axioms QuantumNLS.CountFunctionsS01Ops.countOp_comm_E
#print axioms QuantumNLS.CountFunctionsS01Ops.physical_comm
#print axioms QuantumNLS.CountFunctionsS01Ops.countOp_sub_le
#print axioms QuantumNLS.CountFunctionsS01Calc.fd_scaled_close_H
#print axioms QuantumNLS.CountFunctionsS01Sym.count_strong
#print axioms QuantumNLS.CountFunctionsS01Sym.count_pair
#print axioms QuantumNLS.CountFunctionsS01Words.dynamic_words
#print axioms QuantumNLS.CountFunctionsS01Words.dynamic_word_expectation
#print axioms QuantumNLS.CountFunctionsS01Words.static_words
#print axioms QuantumNLS.CountFunctionsS01Poisson.poisson_genF_genF
#print axioms QuantumNLS.CountFunctionsS01Poisson.poisson_cntF_genF
#print axioms QuantumNLS.CountFunctionsS01Poisson.poisson_cntF_cntF
#print axioms QuantumNLS.CountFunctionsS01Engine.pairOK
#print axioms QuantumNLS.CountFunctionsS01Engine.diracOK_all
#print axioms QuantumNLS.CountFunctionsS01Dirac.dynamic_dirac
#print axioms QuantumNLS.CountFunctionsS01Dirac.dynamic_expr_pair
#print axioms QuantumNLS.CountFunctionsS01Dirac.static_dirac
#print axioms QuantumNLS.CountFunctionsS01Dirac.static_expr_pair
#print axioms QuantumNLS.CountFunctionsS01Phase.regPhase_c2
#print axioms QuantumNLS.CountFunctionsS01Phase.regPhase_cl
#print axioms QuantumNLS.CountFunctionsS01Phase.cutoff_exists
#print axioms QuantumNLS.CountFunctionsS01Final.g1a_dynamic_words
#print axioms QuantumNLS.CountFunctionsS01Final.g1a_dynamic_expectation
#print axioms QuantumNLS.CountFunctionsS01Final.g1b_dynamic_dirac
#print axioms QuantumNLS.CountFunctionsS01Final.g1b_dynamic_expr_pair

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.CountFunctionsS01" ||
        name.toString.startsWith "_private.QuantumNLS.CountFunctionsS01" then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          name.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"CountFunctionsS01 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard axioms only; no HeldGP14Tonelli / RegularCut. Closure contains audit_dynamic_gauge: {seen.contains ``QuantumNLS.DynamicGaugeFinalR35m.audit_dynamic_gauge}."
