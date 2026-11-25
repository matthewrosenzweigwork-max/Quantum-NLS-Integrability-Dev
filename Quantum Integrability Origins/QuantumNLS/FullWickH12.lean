import QuantumNLS.FullWickH10
import QuantumNLS.FullWickH11

/-! FullWickH12 (haiku_inventory, R-140AE34B `thm:full-wick`, addendum 6: headline v2 with norm-close static clauses).

Headline `FullWickH12.thm_full_wick_printed_v2` is the frozen headline `FullWickH10.thm_full_wick_printed`
(ten conjuncts, unchanged, read-only import) followed by two new conjuncts:

  StaticWordNormCloseClause  norm-close versions of StaticWordClause: every fixed ordered product of Cartesian
                             generators keeps its static pair on every uniformly norm-close normalized preparation
                             (printed wick_calculus.tex:84-86 for "norm-close" and the ordered products; line 89
                             "uniformly norm-close preparations preserve the static uniform statements").
  StaticDiracNormCloseClause norm-close version of StaticDiracClause: the scaled Dirac commutator has symbol
                             {f,g}(w(u)) = evalSym (pb S f g) on every such preparation (printed lines 84-86, 89).

Proofs are in FullWickH11 (static_word_normClose, static_dirac_normClose). The two new Props quantify over
the same parameters as their reference clauses, and take the norm-close hypothesis
`IsNormClosePrepT ψ' (product) (UR R) Tb` of FullWickH7 (the static analogue of the polynomial clause
`FullWickH8.static_poly_normClose`).

Named inputs (exactly as in FullWickH10): the parameter predicate `UniformStaticR49b.UniformStatic hκ j q`
(printed R-D2F4CE8F) is the only hypothesis of the static clauses. No new hypothesis is introduced.
Nothing about the dynamic gauge or the basis index `n+1` versus `1+n` is addressed here (those are items (a) and (b),
owned by FullWickO3+).

Standard dependencies only (audit at the end of the file).
-/

noncomputable section
open Filter Topology
open scoped ComplexConjugate BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH12

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH7 (IsNormClosePrepT)
open QuantumNLS.FullWickO1 (staticGauge)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.FullWickS1 (orderedWord)
open QuantumNLS.WickSymbols (Sym Balanced pb)
open QuantumNLS.WickBounds (gensym wordSym labelsOf)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.UniformStaticR49b (UniformStatic)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.FullWickH10 (Stage1Clause Stage2Clause StaticClause StaticSelectedClause StaticNormCloseClause
  StaticDiracClause StaticWordClause DynamicClause DynamicDiracClause DynamicWordClause)

variable (L κ : ℝ) [Fact (0 < L)]

/-! ### The two new clauses (norm-close preparations of the static word and Dirac statements) -/

/-- **Norm-close static words (new conjunct).** Every fixed ordered product of Cartesian generators
`E_{a_1b_1} ⋯ E_{a_kb_k}` (`orderedWord`) on the Q06 static gauge has, on every uniformly norm-close normalized
preparation `ψ'` of the reference product state, the uniform strong pair with symbol `∏ z_{a_j} conj z_{b_j}`
(`evalSym (chart Φ u) (wordSym w)`) and the conjugate companion; parameter predicate `UniformStatic hκ j q`. -/
def StaticWordNormCloseClause (hκ : 0 < κ) : Prop :=
  ∀ {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}, UniformStatic (L := L) hκ j q →
    ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ)) {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)},
      IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
        (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb →
      HasUniformPairT (H := fun n => HN L (n + 1))
        (fun n => orderedWord (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) w)
        (fun n => ((w.map fun p => BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (gensym p.2 p.1)).reverse).prod)
        (UR (L := L) R) Tb ψ'
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w))

/-- **Norm-close scaled Dirac commutator (new conjunct).** For balanced `f, g` with labels in `S`, the scaled
commutator `-iN[W^q_N(f), W^q_N(g)]` (`N = n + 1`) has, on every uniformly norm-close normalized preparation `ψ'`
of the reference product state, the uniform strong symbol `{f,g}(w(u)) = evalSym (chart Φ u) (pb S f g)`;
parameter predicate `UniformStatic hκ j q`. -/
def StaticDiracNormCloseClause (hκ : 0 < κ) : Prop :=
  ∀ {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}, UniformStatic (L := L) hκ j q →
    ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f g : Sym}, Balanced f → Balanced g →
      ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf g ⊆ S →
      ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)},
        IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
          (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb →
        HasUniformStrongT (H := fun n => HN L (n + 1))
          (fun n => (-(Complex.I) * ((n + 1 : ℕ) : ℂ)) •
            (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f
              * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
              - BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
              * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f))
          (UR (L := L) R) Tb ψ'
          (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (pb S f g))

/-! ### Proofs of the new clauses (from FullWickH11) -/

theorem static_word_normClose_clause (hκ : 0 < κ) : StaticWordNormCloseClause L κ hκ := by
  intro j q hU Θ Tb R w ψ' hprep
  exact FullWickH11.static_word_normClose hκ hU Tb R w hprep

theorem static_dirac_normClose_clause (hκ : 0 < κ) : StaticDiracNormCloseClause L κ hκ := by
  intro j q hU Θ Tb R f g hf hg S hSf hSg ψ' hprep
  exact FullWickH11.static_dirac_normClose hκ hU Tb R hf hg hSf hSg hprep

/-! ### The headline v2 -/

/-- **The printed theorem `thm:full-wick` (R-140AE34B), headline v2.** The frozen ten-conjunct headline
`FullWickH10.thm_full_wick_printed` (unchanged), followed by the norm-close static word clause and the norm-close
static Dirac clause (printed wick_calculus.tex:84-86 and 89). Same named inputs as the frozen headline:
`RD8362E5EBInput` for the dynamic clauses and `UniformStatic` for the static clauses. -/
theorem thm_full_wick_printed_v2 (hκ : 0 < κ) :
    Stage1Clause L ∧ Stage2Clause L ∧ StaticClause L κ hκ ∧ StaticSelectedClause L κ hκ
      ∧ StaticNormCloseClause L κ hκ ∧ StaticDiracClause L κ hκ ∧ StaticWordClause L κ hκ
      ∧ DynamicClause L κ hκ ∧ DynamicDiracClause L κ hκ ∧ DynamicWordClause L κ hκ
      ∧ StaticWordNormCloseClause L κ hκ ∧ StaticDiracNormCloseClause L κ hκ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := FullWickH10.thm_full_wick_printed L κ hκ
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    static_word_normClose_clause L κ hκ, static_dirac_normClose_clause L κ hκ⟩

end QuantumNLS.FullWickH12

#print axioms QuantumNLS.FullWickH12.static_word_normClose_clause
#print axioms QuantumNLS.FullWickH12.static_dirac_normClose_clause
#print axioms QuantumNLS.FullWickH12.thm_full_wick_printed_v2

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickH12." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickH12." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          (name.toString.splitOn "RB7BindFinal").length > 1 ||
          (name.toString.splitOn "DEF033_package").length > 1 ||
          name.components.any (fun c => c.toString == "RegularCut") ||
          name == ``QuantumNLS.UniformStaticR31m.GaugeRetargetingRD51987CAInput ||
          name == ``QuantumNLS.UniformStaticR31m.uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.retarget_and_uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.uniform_static_intermediate then
        throwError "Excluded dependency: {name}"
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
  Lean.logInfo m!"FullWickH12 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
