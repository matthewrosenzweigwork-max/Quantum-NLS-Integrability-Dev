import QuantumNLS.MainTheoremR01Values
import QuantumNLS.MainTheoremR01Static
import QuantumNLS.MainTheoremR01Physical
import QuantumNLS.MainTheoremR01Algebra
import QuantumNLS.UniformProjFinalR02
import QuantumNLS.InverseFinalR02
import QuantumNLS.AuditGapsFinalS02

/-!
# MainTheoremR01: R-AF8F7562 `thm:main`, the six correspondence clauses — ASSEMBLY (no named theorem inputs)

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex` lines 2-102 (statement, `\ReportID{R-AF8F7562}`,
`\label{thm:main}`); proof `source-text/chapters/core/correspondence_theorem.tex` lines 1-66.

HEADLINE `MainTheoremR01.thm_main (hκ : 0 < κ) : MainStatement hκ`. Only hypotheses: the period fact `0 < L` and
`κ > 0` ("Fix L, κ > 0"). `MainStatement` is: there is ONE sequence of occupation gauges `q` (with its active
schedule `j`), chosen before every profile and tested parameter, such that parts (i)-(vi) hold, with every
gauge-dependent object of parts (ii), (iii) and (v) built from that single `q`
(`G q = DynamicGaugePhysicalR34m.physicalGauge q` on the physical Bethe sectors; the static objects of R-D2F4CE8F
and R-98833BEE take `q` itself; `G q = FullWickO1.staticGauge q` by `FullWickO3.physicalGauge_eq_staticGauge`).

The named form `thm_main_named` fixes the witness: `j = RetargetSelectionR49b.particleStage hκ`,
`q = RetargetSelectionR49b.sectorGauge hκ` (the R-D51987CA named pair), so `G q` is
`DynamicGaugeFinalR35m.gauge hκ` definitionally (`gauge_named`).

Clause-to-predecessor map: see the docstrings of `PartI` ... `PartVI` and the review record.
No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.MainTheoremR01

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH7 (IsNormClosePrepT)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.WickSymbols (Sym Balanced)
open QuantumNLS.WickBounds (labelsOf)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox)
open QuantumNLS.OccupationUnitary (oneBasis)
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
open QuantumNLS.UniformStaticR49b (SectorGauge UniformStatic)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ### The fixed objects -/

/-- The single gauge, as the phase function on the physical Bethe sectors. -/
abbrev G (q : SectorGauge) : Gauge :=
  DynamicGaugePhysicalR34m.physicalGauge (UniformStaticBridgeR50b.toFullGauge q)

/-- The actual higher flows `Φ_t` (accepted hierarchy R-7B122087, binding `RB7BindFinal`). -/
abbrev F (hκ : 0 < κ) : ActualModelTargetR53a.HigherFlows L κ :=
  ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)

/-- The independently constructed chart `w = Φ^q_{L,κ}` (R-F5355ABD/R-C05E2420, DEF-021). -/
abbrev C (κ : ℝ) (hκ : 0 < κ) : Def021ChartR41b.Chart L κ hκ := Def021ChartR41b.chart L κ hκ

/-! ### Part (i): values and actions (R-115CAA16; same packets as R-568BCDF8) -/

/-- **Part (i).** For every smooth unit profile `u`: one sequence of normalized finite Bethe packets with
`‖Φ_N - u^{⊗N}‖ → 0`, `Φ_N ∈ ⋂_s D(Q_{N,s})`, `‖(N⁻¹Q_{N,r} - I_{r+1}(u))Φ_N‖ → 0` for every `r`, the original
support-uniform statement on the common packets, and their DEF-031 energy preparation
(`MainTheoremR01Values.PacketClause`); eq:actions-main in probability under `p_{N,u}`, the weight comparison
`(1+n²)^{p/2} ≤ (1+|n|)^p ≤ 2^{p/2}(1+n²)^{p/2}`, and the original `(1+|n|)^p` conclusion
(`MainTheoremR01Values.ActionsClause`). -/
def PartI (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L) (hu : ‖physical u‖ = 1),
    MainTheoremR01Values.PacketClause hκ u ∧ MainTheoremR01Values.ActionsClause hκ u hu

/-! ### Part (ii): uniform static symbols (R-D2F4CE8F, R-98833BEE, R-140AE34B) -/

/-- The static clauses of the balanced polynomial quantization at the single gauge (R-140AE34B; `FullWickH10`
`Stage1Clause`, `Stage2Clause`, `StaticClause` and `StaticNormCloseClause` with the parameter pair fixed to `(j, q)`
and the gauge written as `G q`). -/
def FullWickStatic (hκ : 0 < κ) (q : SectorGauge) : Prop :=
  FullWickH10.Stage1Clause L ∧ FullWickH10.Stage2Clause L ∧
  (∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) f)
      (fun n => (BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) f).adjoint)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) => evalSym ((C κ hκ).Φ u) f)) ∧
  (∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
    ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)},
      IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
        (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb →
      HasUniformPairT (H := fun n => HN L (n + 1))
        (fun n => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) f)
        (fun n => (BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) f).adjoint)
        (UR (L := L) R) Tb ψ'
        (fun (u : L2T L) (_ : Θ) => evalSym ((C κ hκ).Φ u) f))

/-- **Part (ii).** Uniform Cartesian symbols and adjoints over `𝒰_R` simultaneously on the active set, the
positive-action phase, support, affinity and defect limits (R-D2F4CE8F `UniformStatic`); eq:uniform-projective-main
with its norm-close, column and inverse conclusions (R-98833BEE); persistence of the strong symbols under uniformly
norm-close normalized preparations; the static polynomial quantization (R-140AE34B). -/
def PartII (hκ : 0 < κ) (j : ℕ → ℕ) (q : SectorGauge) : Prop :=
  UniformStatic (L := L) hκ j q ∧
  UniformProjR01.UniformProjectiveStatement98833BEE (L := L) hκ (UniformStaticBridgeR50b.toFullGauge q) ∧
  MainTheoremR01Static.StaticPersistence (L := L) hκ j q ∧
  FullWickStatic (L := L) hκ q

/-! ### Part (iii): dynamics (R-8362E5EB, R-140AE34B, sec:algebra) -/

/-- **Part (iii).** Strong Cartesian symbols (all pairs, collapsed actions included) and positive-action unit
phases with adjoints, uniformly on every compact box, for every norm-close preparation (R-8362E5EB); ordered words
in the Cartesian transfers and their adjoints with the product symbol, and their expectations; the polynomial
quantization's dynamic symbols, products and scaled Dirac commutators (R-140AE34B), with `sup_N ‖N[A_N,C_N]‖ < ∞`. -/
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
  (∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    (∀ {f : Sym}, Balanced f →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) f)
        (fun n => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (G q) f).adjoint)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ (F hκ) u R t : ℤ → ℂ)) f)) ∧
    (∀ (fs : List Sym), (∀ g ∈ fs, Balanced g) →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => (fs.map fun g => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (G q) g).prod)
        (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (G q) g).adjoint).reverse).prod)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          (fs.map fun g => evalSym ((ReconstructionR33m.w hκ (F hκ) u R t : ℤ → ℂ)) g).prod)) ∧
    (∀ {f h : Sym}, Balanced f → Balanced h → ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf h ⊆ S →
      HasUniformStrongT (H := fun n => HN L (1 + n))
        (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
          (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) f
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) h
            - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) h
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) f))
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          evalSym ((ReconstructionR33m.w hκ (F hκ) u R t : ℤ → ℂ)) (WickSymbols.pb S f h)))) ∧
  (∀ {f h : Sym}, Balanced f → Balanced h → ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf h ⊆ S →
    ∃ M : ℝ, ∀ n : ℕ,
      ‖((1 + n : ℕ) : ℂ) •
        (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) f *
            BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) h -
          BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) h *
            BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (G q) f)‖ ≤ M)

/-! ### Part (iv): physical marginals (R-E679E41D, R-568BCDF8) -/

/-- **Part (iv).** eq:physical-main for every normalized norm-close preparation and every compact `K`; and
eq:allorder-energy-main under both preparation hypotheses, with exact products energy-prepared (the common packets
of part (i) are energy-prepared by `PartI`). -/
def PartIV (hκ : 0 < κ) : Prop :=
  MainTheoremR01Physical.PhysicalMarginal (L := L) hκ ∧ MainTheoremR01Physical.EnergyClause (L := L) hκ

/-! ### Part (v): the auxiliary matrix (R-FAF88C8A, R-AA5864B7, R-154AFD4C) -/

/-- **Part (v).** `Γ_N(t)` is positive with trace one and `Γ_N(t)_{ab} = ⟨U_N(t)ψ_N, E^q_{N,ab}U_N(t)ψ_N⟩`;
eq:projective-main (R-FAF88C8A); the column representatives (R-AA5864B7) and the normalized-column inverse
(R-154AFD4C), all at the single gauge and the same quantum-derived target `w`. -/
def PartV (hκ : 0 < κ) (q : SectorGauge) : Prop :=
  (∀ (n : ℕ) (φ : HN L (1 + n)), ‖φ‖ = 1 →
    (ReconstructionR33m.density hκ (G q) n φ).IsPositive ∧
    TraceClass.posTrace (ReconstructionR33m.density hκ (G q) n φ) = 1 ∧
    ∀ a b : ℤ, ⟪oneBasis a, ReconstructionR33m.density hκ (G q) n φ (oneBasis b)⟫_ℂ =
      ⟪φ, ReconstructionR33m.E (L := L) hκ (G q) n a b φ⟫_ℂ) ∧
  ReconstructionR33m.Reconstruction hκ (F (L := L) hκ) (G q) ∧
  ColumnR01.ColumnAA5864B7Statement hκ (C κ hκ) (G q)
    (ActualModelTargetR53a.flowMap (F (L := L) hκ)) (ActualModelTargetR53a.flow_isHam (F (L := L) hκ)) ∧
  InverseR01.InverseStatement154AFD4C hκ (C κ hκ) (G q)
    (ActualModelTargetR53a.flowMap (F (L := L) hκ)) (ActualModelTargetR53a.flow_isHam (F (L := L) hκ))

/-! ### Part (vi): adjacent differences (R-10EE6421) -/

/-- **Part (vi).** For every fixed positive-action donor-receiver pair and order `r`, under the original law,
`Λ_{N,r}(m - e_a + e_b) - Λ_{N,r}(m) → ω_{r,b}(u) - ω_{r,a}(u)` in probability (any missing-donor convention),
jointly for every finite family. -/
def PartVI (hκ : 0 < κ) : Prop :=
  (∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (r : ℕ) (a b : ℤ),
    0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 a →
    0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 b →
    ∀ (missing : ∀ N, BetheLabels.MArr (N + 1) → ℝ),
      Def033CoreR24m.DifferenceLimit hκ (physical u) hu r a b ((AuditGapsFinalS02.D (L := L) hκ).ω r u)
        missing) ∧
  (∀ (u : Smooth L) (hu : ‖physical u‖ = 1) {ι : Type} [Fintype ι] (r : ι → ℕ) (a b : ι → ℤ),
    (∀ i, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 (a i)) →
    (∀ i, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 (b i)) →
    ∀ (missing : ι → ∀ N, BetheLabels.MArr (N + 1) → ℝ) (ε : ℝ), 0 < ε →
      Tendsto (fun N => Def033CoreR24m.originalBorn hκ (physical u) hu N
        {m | ∃ i, ε < |Def033CoreR24m.withMissing L κ (N + 1) (r i) (a i) (b i) (missing i N) m -
          Def033CoreR24m.target ((AuditGapsFinalS02.D (L := L) hκ).ω (r i) u) (a i) (b i)|}) atTop (𝓝 0))

/-! ### The theorem -/

/-- **R-AF8F7562 `thm:main`.** There is one sequence of occupation gauges (with its active schedule), chosen before
the profile and all tested parameters, with properties (i)-(vi). -/
def MainStatement (hκ : 0 < κ) : Prop :=
  ∃ (j : ℕ → ℕ) (q : SectorGauge),
    PartI (L := L) hκ ∧ PartII (L := L) hκ j q ∧ PartIII (L := L) hκ q ∧ PartIV (L := L) hκ ∧
      PartV (L := L) hκ q ∧ PartVI (L := L) hκ

/-- The named gauge is the gauge of the accepted R-8362E5EB/R-FAF88C8A/R-AA5864B7/R-154AFD4C/R-10EE6421 finals. -/
theorem gauge_named (hκ : 0 < κ) :
    G (RetargetSelectionR49b.sectorGauge (L := L) hκ) = DynamicGaugeFinalR35m.gauge (L := L) hκ := rfl

/-- The same gauge is the static Wick gauge of R-140AE34B. -/
theorem gauge_static (q : SectorGauge) : G q = FullWickO1.staticGauge q :=
  FullWickO3.physicalGauge_eq_staticGauge q

theorem partI (hκ : 0 < κ) : PartI (L := L) hκ := fun u hu =>
  ⟨MainTheoremR01Values.packet_clause hκ u hu, MainTheoremR01Values.actions_clause hκ u hu⟩

theorem fullWickStatic {j : ℕ → ℕ} {q : SectorGauge} (hκ : 0 < κ) (hU : UniformStatic (L := L) hκ j q) :
    FullWickStatic (L := L) hκ q := by
  refine ⟨FullWickH10.stage1_clause L, FullWickH10.stage2_clause L, ?_, ?_⟩
  · intro Θ Tb R f hf
    rw [gauge_static q]
    exact FullWickH10.static_clause L κ hκ hU Tb R hf
  · intro Θ Tb R f hf ψ' hψ'
    rw [gauge_static q]
    exact FullWickH10.static_normClose_clause L κ hκ hU Tb R hf hψ'

theorem partII (hκ : 0 < κ) :
    PartII (L := L) hκ (RetargetSelectionR49b.particleStage (L := L) hκ)
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨UniformStaticR49b.selected_uniform_static hκ, UniformProjFinalR02.uniform_projective_final hκ,
    MainTheoremR01Static.static_persistence hκ (UniformStaticR49b.selected_uniform_static hκ),
    fullWickStatic hκ (UniformStaticR49b.selected_uniform_static hκ)⟩

theorem partIII (hκ : 0 < κ) : PartIII (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) := by
  have D : RD8362E5EBInput hκ (F (L := L) hκ) (G (RetargetSelectionR49b.sectorGauge (L := L) hκ)) :=
    DynamicGaugeFinalR35m.audit_dynamic_gauge hκ
  refine ⟨D, fun u hu R lo hi ψ hψ w => ⟨MainTheoremR01Algebra.cartesian_words hκ _ _ D u hu R lo hi ψ hψ w,
      MainTheoremR01Algebra.cartesian_word_expectation hκ _ _ D u hu R lo hi ψ hψ w⟩,
    fun u hu R lo hi ψ hψ => ⟨fun hf => FullWickH10.dynamic_clause L κ hκ _ _ D u hu R lo hi ψ hψ hf,
      FullWickH13.dynamic_poly_product_clause L κ hκ _ _ D u hu R lo hi ψ hψ,
      fun hf hh S hSf hSh => FullWickH10.dynamic_dirac_clause L κ hκ _ _ D u hu R lo hi ψ hψ hf hh hSf hSh⟩,
    fun hf hh S hSf hSh => MainTheoremR01Algebra.dirac_scaled_bound hκ _ hf hh hSf hSh⟩

theorem partIV (hκ : 0 < κ) : PartIV (L := L) hκ :=
  ⟨MainTheoremR01Physical.physical_marginal hκ, MainTheoremR01Physical.energy_clause hκ⟩

theorem partV (hκ : 0 < κ) : PartV (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨fun n φ hφ => MainTheoremR01Algebra.density_facts hκ _ n φ hφ,
    ReconstructionFinalR35m.reconstruction hκ, ColumnFinalR02.column_final hκ, InverseFinalR02.inverse_final hκ⟩

theorem partVI (hκ : 0 < κ) : PartVI (L := L) hκ :=
  ⟨fun u hu r a b ha hb missing => AuditGapsFinalS02.audit_gaps_final hκ u hu r a b ha hb missing,
    fun u hu _ _ r a b ha hb missing ε hε =>
      AuditGapsFinalS02.audit_gaps_final_joint hκ u hu r a b ha hb missing ε hε⟩

/-- **R-AF8F7562 `thm:main`, named witness**: the six parts at the R-D51987CA named pair. -/
theorem thm_main_named (hκ : 0 < κ) :
    PartI (L := L) hκ ∧
    PartII (L := L) hκ (RetargetSelectionR49b.particleStage (L := L) hκ)
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧
    PartIII (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧ PartIV (L := L) hκ ∧
    PartV (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧ PartVI (L := L) hκ :=
  ⟨partI hκ, partII hκ, partIII hκ, partIV hκ, partV hκ, partVI hκ⟩

/-- **R-AF8F7562 `thm:main` (HEADLINE).** Fix `L, κ > 0`. There is one sequence of occupation gauges, chosen
before the profile and all tested parameters, with properties (i)-(vi). -/
theorem thm_main (hκ : 0 < κ) : MainStatement (L := L) hκ :=
  ⟨_, _, thm_main_named hκ⟩


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

end QuantumNLS.MainTheoremR01

set_option maxHeartbeats 40000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  -- (1) binders of the headline: exactly {L} [Fact (0 < L)] {κ} (hκ : 0 < κ); no named theorem input.
  for root in [``QuantumNLS.MainTheoremR01.thm_main, ``QuantumNLS.MainTheoremR01.thm_main_named] do
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
    let (nConst, nAx) ← QuantumNLS.MainTheoremR01.transitiveAudit root
    logInfo m!"{root}: binders {names}; closure {nConst} constants, {nAx} standard axioms, no held identifiers."
  -- (2) the existential headline is witnessed by the named form.
  let main ← getConstInfo ``QuantumNLS.MainTheoremR01.thm_main
  let some v := main.value? (allowOpaque := true) | throwError "no value"
  unless v.getUsedConstants.contains ``QuantumNLS.MainTheoremR01.thm_main_named do
    throwError "thm_main is not proved from thm_main_named"
  logInfo "MAIN_THEOREM_R01 AUDIT PASS"

#print axioms QuantumNLS.MainTheoremR01.thm_main
#print axioms QuantumNLS.MainTheoremR01.thm_main_named
