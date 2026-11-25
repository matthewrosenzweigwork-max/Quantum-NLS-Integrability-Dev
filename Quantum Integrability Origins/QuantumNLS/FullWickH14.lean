import QuantumNLS.FullWickH12
import QuantumNLS.FullWickH13
import QuantumNLS.FullWickO3
import QuantumNLS.FullWickO4

/-! FullWickH14 (haiku_inventory, R-140AE34B `thm:full-wick`, addendum 7: headline v3 with polynomial products).

Headline `FullWickH14.thm_full_wick_printed_v3` is the headline v2 `FullWickH12.thm_full_wick_printed_v2` (twelve
conjuncts, read-only import, unchanged) followed by three new conjuncts from FullWickH13:

  StaticPolyProductClause          ordered products of balanced polynomials `W^q_N(f_1) ⋯ W^q_N(f_k)` on `𝒰_R`,
                                   with symbol `f_1(w(u)) ⋯ f_k(w(u))` (printed wick_calculus.tex:86-88).
  StaticPolyProductNormCloseClause the same on every uniformly norm-close normalized preparation (printed 88-89).
  DynamicPolyProductClause         the same along hierarchy trajectories, every norm-close preparation (`Preparation`)
                                   and every compact joint-time box (printed 84-88), with the gauge `G` and the input
                                   `D : RD8362E5EBInput hκ F G` of the frozen dynamic clauses.

Q06 one family (not conjuncts): on the dynamic index `1+n`, for the one operator family `W^q_N(f)` at the Q06 gauge
`staticGauge (sectorGauge hκ)`, `static_poly_product_at_Q06_one_family` (static products on `𝒰_R`, from
`FullWickO4.static_pair_one_add`) and `dynamic_poly_product_at_Q06` (dynamic products, with the R-8362E5EB input
supplied by `FullWickO3.rd8362_at_Q06` from the remaining inputs only, as in `FullWickO4.full_wick_Q06_one_family`).

Named inputs: exactly those of the frozen headline (`UniformStatic hκ j q` on the static clauses, and the
`RD8362E5EBInput hκ F G` hypothesis `D` on the dynamic clauses). The Q06 instance adds the four R-8362E5EB inputs.

Standard dependencies only (audit at the end of the file).
-/

noncomputable section
open Filter Topology
open scoped ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH14

open QuantumNLS.FullWickH4 (HasUniformPairT)
open QuantumNLS.FullWickO1 (staticGauge)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.WickSymbols (Sym Balanced coeffNorm)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.ReconstructionR33m (Preparation TimeBox flows)
open QuantumNLS.FullWickH10 (Stage1Clause Stage2Clause StaticClause StaticSelectedClause StaticNormCloseClause
  StaticDiracClause StaticWordClause DynamicClause DynamicDiracClause DynamicWordClause)
open QuantumNLS.FullWickH12 (StaticWordNormCloseClause StaticDiracNormCloseClause)
open Def033HierarchyR24m (Smooth physical)

variable (L κ : ℝ) [Fact (0 < L)]

/-! ### The headline v3 -/

/-- **The printed theorem `thm:full-wick` (R-140AE34B), headline v3.** The headline v2 (twelve conjuncts, unchanged),
followed by the static polynomial products on `𝒰_R`, their norm-close version, and the dynamic polynomial products
along hierarchy trajectories (printed wick_calculus.tex:84-89). Same named inputs as v2. -/
theorem thm_full_wick_printed_v3 (hκ : 0 < κ) :
    Stage1Clause L ∧ Stage2Clause L ∧ StaticClause L κ hκ ∧ StaticSelectedClause L κ hκ
      ∧ StaticNormCloseClause L κ hκ ∧ StaticDiracClause L κ hκ ∧ StaticWordClause L κ hκ
      ∧ DynamicClause L κ hκ ∧ DynamicDiracClause L κ hκ ∧ DynamicWordClause L κ hκ
      ∧ StaticWordNormCloseClause L κ hκ ∧ StaticDiracNormCloseClause L κ hκ
      ∧ FullWickH13.StaticPolyProductClause L κ hκ
      ∧ FullWickH13.StaticPolyProductNormCloseClause L κ hκ
      ∧ FullWickH13.DynamicPolyProductClause L κ hκ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    FullWickH12.thm_full_wick_printed_v2 L κ hκ
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    FullWickH13.static_poly_product_clause L κ hκ,
    FullWickH13.static_poly_product_normClose_clause L κ hκ,
    FullWickH13.dynamic_poly_product_clause L κ hκ⟩

/-! ### Q06 one family: static products on the dynamic index `1+n` -/

/-- One balanced polynomial on the dynamic index `1+n`, static parameter pair `(j, q)`: the static pair of
`FullWickO4.static_pair_one_add` with the coefficient bound at `N = 1+n` (`C = K = coeffNorm f`). -/
theorem static_one_add_good (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStaticR49b.UniformStatic (L := L) hκ j q) {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}
    (hf : Balanced f) :
    FullWickH6.GoodFactor (H := fun n => HN L (1 + n))
      (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) g)
      (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) g).adjoint)
      (fun (g : Sym) (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (coeffNorm f) (coeffNorm f) f := by
  refine ⟨Filter.Eventually.of_forall fun n => FullWickH1.quantization_coeff_bound (N := 1 + n)
      (by omega) (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) hf,
    Filter.Eventually.of_forall fun n => (FullWickH8.norm_adjoint_eq _).trans_le
      (FullWickH1.quantization_coeff_bound (N := 1 + n) (by omega)
        (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) hf),
    fun u hu t _ => FullWickH8.chart_evalSym_norm_le hκ hu.1 f,
    FullWickO4.static_pair_one_add hκ hU Tb R hf⟩

/-- **Static ordered products of balanced polynomials on the dynamic index `1+n`** (the one family of the Q06
dynamic statements). Same symbol and constants as `FullWickH13.static_prod_pair`, on `HN L (1+n)`. -/
theorem static_one_add_prod (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStaticR49b.UniformStatic (L := L) hκ j q) {Θ : Type} (Tb : Set Θ) (R : ℝ) (fs : List Sym)
    (hfs : ∀ g ∈ fs, Balanced g) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (fs.map fun g => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) g).prod)
      (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) g).adjoint).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (fun (u : L2T L) (_ : Θ) => (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod) := by
  obtain ⟨C, K, hC, hK, hgood⟩ := FullWickH13.exists_common_good (H := fun n => HN L (1 + n))
    (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) g)
    (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) g).adjoint)
    (fun (g : Sym) (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g)
    (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))) fs
    (fun g hg => ⟨coeffNorm g, coeffNorm g, FullWickH13.coeffNorm_nonneg' g,
      FullWickH13.coeffNorm_nonneg' g, static_one_add_good L κ hκ hU Tb R (hfs g hg)⟩)
  exact (FullWickH6.pair_list_prod (H := fun n => HN L (1 + n))
    (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) g)
    (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) g).adjoint)
    (fun (g : Sym) (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g)
    (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
    C K hC hK fs hgood).1

/-- **Static polynomial products for `W^q_N` at the Q06 gauge, on the dynamic index `1+n`** (the static half of the
one-family statement; the parameter pair is the selected Q06 witness `UniformStaticR49b.selected_uniform_static`). -/
theorem static_poly_product_at_Q06_one_family (hκ : 0 < κ) {Θ : Type} (Tb : Set Θ) (R : ℝ)
    (fs : List Sym) (hfs : ∀ g ∈ fs, Balanced g) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (fs.map fun g => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n)
        (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) g).prod)
      (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n)
        (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) g).adjoint).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (fun (u : L2T L) (_ : Θ) => (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod) :=
  static_one_add_prod L κ hκ (UniformStaticR49b.selected_uniform_static (L := L) hκ) Tb R fs hfs

/-! ### Q06 instance of the dynamic polynomial products (dynamic gauge and index) -/

/-- **Dynamic polynomial products for `W^q_N` at the Q06 gauge, on the dynamic index `1+n`.** The gauge is
`staticGauge (sectorGauge hκ)`, the R-8362E5EB input is `FullWickO3.rd8362_at_Q06` (discharged), and the only
remaining hypotheses are the four R-8362E5EB inputs of `FullWickO4.full_wick_Q06_one_family`. -/
theorem dynamic_poly_product_at_Q06 (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (RE679E41DInput : TerraMultiRound88Input.RE679E41DInput hκ HierarchyR7B122087Input)
    (DynftFullTorusInput : ∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ),
      DynSeedInputR47b.DynftFullTorusInput hκ (flows hκ HierarchyR7B122087Input) u R)
    (R300B8640Input : DynamicGaugeR34m.R300B8640Input hκ (flows hκ HierarchyR7B122087Input)) :
    ∀ (u : Def033HierarchyR24m.Smooth L), ‖Def033HierarchyR24m.physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ (fs : List Sym), (∀ g ∈ fs, Balanced g) →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => (fs.map fun g => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n)
          (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) g).prod)
        (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n)
          (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) g).adjoint).reverse).prod)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          (fs.map fun g => evalSym ((ReconstructionR33m.w hκ (flows hκ HierarchyR7B122087Input) u R t :
            ℤ → ℂ)) g).prod) :=
  fun u hu R lo hi ψ hψ fs hfs =>
    FullWickH13.dyn_prod_pair hκ (flows hκ HierarchyR7B122087Input)
      (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ))
      (FullWickO3.rd8362_at_Q06 hκ HierarchyR7B122087Input RE679E41DInput DynftFullTorusInput
        R300B8640Input)
      u hu R lo hi ψ hψ fs hfs

end QuantumNLS.FullWickH14

#print axioms QuantumNLS.FullWickH14.thm_full_wick_printed_v3
#print axioms QuantumNLS.FullWickH14.dynamic_poly_product_at_Q06

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickH14." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickH14." ||
        name.toString.startsWith "QuantumNLS.FullWickH13." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickH13." then
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
  Lean.logInfo m!"FullWickH13+H14 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
