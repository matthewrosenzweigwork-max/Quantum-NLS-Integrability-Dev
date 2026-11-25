import QuantumNLS.FullWickH9
import QuantumNLS.FullWickH2
import QuantumNLS.FullWickH3

/-! FullWickH10 (haiku_inventory, R-140AE34B `thm:full-wick`, assembly stage C: the printed theorem).

Headline `FullWickH10.thm_full_wick_printed`: the conjunction of the clauses of the printed
`thm:full-wick` (source-text/chapters/core/wick_calculus.tex:49-203), each clause a named Prop below.

  Stage1Clause        eq:full-product, eq:full-product-bound, eq:full-Dirac-bound, eq:full-coefficient-bound
                      (re-exported from FullWickH1.fullWick_stage1, for every N ≥ 1, basis and gauge)
  Stage2Clause        eq:full-norm-limit: lim ‖W_N(f)‖ = max_{‖z‖≤1, z∈ℂ^I} |f(z)|, and the ℓ² identification
                      of the maximum with the unit-ball supremum (FullWickH2, FullWickH3)
  StaticClause        STATIC clause: for every balanced f, `W^q_N(f)` has uniform strong symbol `f(w(u))` on 𝒰_R,
                      and its adjoint the conjugate. Parameter predicate `UniformStaticR49b.UniformStatic hκ j q`
                      (R-D2F4CE8F, used as a hypothesis on the parameters (j, q)).
  StaticSelectedClause  the same at the selected Q06 witnesses (separate statement; unconditional)
  StaticNormCloseClause uniformly norm-close preparations preserve the static statements
  StaticDiracClause   scaled Dirac commutator has symbol {f,g}(w(u)) (static)
  StaticWordClause    every fixed ordered product of generators has the product symbol (static)
  DynamicClause       DYNAMIC clause along hierarchy trajectories, via `ReconstructionR33m.RD8362E5EBInput`
                      (every `Preparation u ψ`, i.e. every norm-close preparation, on every compact joint-time box)
  DynamicDiracClause  dynamic scaled Dirac commutator symbol
  DynamicWordClause   dynamic ordered products

Named inputs (exactly): `ReconstructionR33m.RD8362E5EBInput hκ F G` (printed R-8362E5EB) enters the dynamic clauses
as the hypothesis `D`, and `UniformStaticR49b.UniformStatic hκ j q` (printed R-D2F4CE8F) enters the static
clauses as the hypothesis `hU` on parameters. Nothing else is assumed.

GAUGE REQUIREMENT (not assumed, see `dynamic_clause_at_Q06`): the printed W^q is ONE operator for the Q06 gauge, and
the dynamic statements are printed "for the Q06 gauge" too. The Lean dynamic clauses are stated for the gauge `G` of
the supplied input `D`. The printed dynamic statement for the Q06 gauge is the instance `G = staticGauge q`, and it
requires the R-8362E5EB input `D` to be supplied at that gauge. Equality of the R-8362E5EB gauge with the static
gauge is therefore a requirement on the input, not a consequence proved here.

Standard axioms only (audit at the end of the file).
-/

noncomputable section
open Filter Topology
open scoped ComplexConjugate BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH10

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH7 (IsNormClosePrepT)
open QuantumNLS.FullWickO1 (bilinear staticGauge)
open QuantumNLS.WickSymbols (Sym Balanced coeffNorm)
open QuantumNLS.WickBounds (gensym wordSym labelsOf Cfg balanced_pb)
open QuantumNLS.WickSpectralBridge (evalSym zext LabelsIn)
open QuantumNLS.UniformStaticR49b (UniformStatic)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox)
open QuantumNLS.FullWickS1 (orderedWord monomialWord)

variable (L κ : ℝ) [Fact (0 < L)]

/-! ### The clauses of the printed theorem (named Props) -/

/-- Stage 1 (algebra), `eq:full-product`, `eq:full-product-bound`, `eq:full-Dirac-bound`,
`eq:full-coefficient-bound`, for every `N ≥ 1`, Bethe basis and gauge, balanced polynomial cylinders `f, f'`. -/
def Stage1Clause : Prop :=
  ∀ {N : ℕ} (hN : 0 < N) (b : BetheBasis L N) (G : Gauge) (f f' : BalancedWickDefinition.Polynomial),
    (∀ Γ : Finset (ℤ →₀ ℕ), (∀ p ∈ f.symbol.coeff.support, Finset.Iic p.1 ⊆ Γ) →
        BalancedWickDefinition.wick b G f * BalancedWickDefinition.wick b G f'
          = ∑ γ ∈ Γ, WickSymbols.wickWeight N γ •
              BalancedWickDefinition.quantization b G (WickSymbols.dz γ f.symbol * WickSymbols.dzb γ f'.symbol))
    ∧ ‖BalancedWickDefinition.wick b G f‖ ≤ coeffNorm f.symbol
    ∧ (∀ S : Finset ℤ, labelsOf f.symbol ⊆ S →
        ‖BalancedWickDefinition.wick b G f * BalancedWickDefinition.wick b G f'
            - BalancedWickDefinition.quantization b G (f.symbol * f'.symbol)
            - (N : ℂ)⁻¹ • BalancedWickDefinition.quantization b G
                (WickSymbols.S1 S f.symbol f'.symbol
                  + (Complex.I / 2) • WickSymbols.pb S f.symbol f'.symbol)‖
          ≤ Cfg f.symbol f'.symbol * ((N : ℝ)⁻¹) ^ 2)
    ∧ (∀ S : Finset ℤ, labelsOf f.symbol ⊆ S → labelsOf f'.symbol ⊆ S →
        ‖(-(Complex.I) * (N : ℂ)) • (BalancedWickDefinition.wick b G f * BalancedWickDefinition.wick b G f'
              - BalancedWickDefinition.wick b G f' * BalancedWickDefinition.wick b G f)
            - BalancedWickDefinition.quantization b G (WickSymbols.pb S f.symbol f'.symbol)‖
          ≤ (Cfg f.symbol f'.symbol + Cfg f'.symbol f.symbol) * (N : ℝ)⁻¹)

/-- Stage 2, `eq:full-norm-limit`: for every family of Bethe bases and gauges, the norm of `W_N(f)` converges to the
unit-ball maximum over `ℂ^I`, and that maximum is the supremum over the ℓ² unit ball (attained). -/
def Stage2Clause : Prop :=
  (∀ (b : ∀ N : ℕ, BetheBasis L N) (G : ∀ N : ℕ, Gauge) (I : Finset ℤ) {f : Sym},
      Balanced f → LabelsIn I f →
      Tendsto (fun N => ‖BalancedWickDefinition.quantization (b N) (G N) f‖) atTop
        (nhds (SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f))))
  ∧ (∀ (I : Finset ℤ) {f : Sym}, Balanced f → LabelsIn I f →
      (∀ ξ : QuantumNLS.OccupationUnitary.OneParticle, ‖ξ‖ ≤ 1 →
        ‖evalSym (ξ : ℤ → ℂ) f‖ ≤ SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f))
      ∧ (∃ ξ : QuantumNLS.OccupationUnitary.OneParticle, ‖ξ‖ ≤ 1 ∧
          ‖evalSym (ξ : ℤ → ℂ) f‖ = SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f)))

/-- The static pair (STATIC clause) for `W^q_N(f)` at a fixed parameter pair `(j, q)` satisfying the static predicate. -/
def StaticClause (hκ : 0 < κ) : Prop :=
  ∀ {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}, UniformStatic (L := L) hκ j q →
    ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
      HasUniformPairT (H := fun n => HN L (n + 1))
        (fun n => BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f)
        (fun n => (BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f).adjoint)
        (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)

/-- Selected-witness corollary of the static clause (Q06 gauge `RetargetSelectionR49b.sectorGauge`). -/
def StaticSelectedClause (hκ : 0 < κ) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
      HasUniformPairT (H := fun n => HN L (n + 1))
        (fun n => BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n)
          (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) f)
        (fun n => (BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n)
          (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) f).adjoint)
        (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)

/-- Uniformly norm-close normalized preparations preserve the static statements. -/
def StaticNormCloseClause (hκ : 0 < κ) : Prop :=
  ∀ {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}, UniformStatic (L := L) hκ j q →
    ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
      ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)},
        IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
          (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb →
        HasUniformPairT (H := fun n => HN L (n + 1))
          (fun n => BalancedWickDefinition.quantization
            (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f)
          (fun n => (BalancedWickDefinition.quantization
            (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f).adjoint)
          (UR (L := L) R) Tb ψ'
          (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)

/-- Scaled Dirac commutator (static): symbol `{f,g}(w(u)) = evalSym (pb S f g)`. -/
def StaticDiracClause (hκ : 0 < κ) : Prop :=
  ∀ {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}, UniformStatic (L := L) hκ j q →
    ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f g : Sym}, Balanced f → Balanced g →
      ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf g ⊆ S →
      HasUniformStrongT (H := fun n => HN L (n + 1))
        (fun n => (-(Complex.I) * ((n + 1 : ℕ) : ℂ)) •
          (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f
            * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
            - BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g
            * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) f))
        (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (WickSymbols.pb S f g))

/-- Every fixed ordered product of generators (static): product symbol `∏ z_{a_j} conj z_{b_j}`. -/
def StaticWordClause (hκ : 0 < κ) : Prop :=
  ∀ {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}, UniformStatic (L := L) hκ j q →
    ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ)),
      HasUniformPairT (H := fun n => HN L (n + 1))
        (fun n => orderedWord (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) w)
        (fun n => ((w.map fun p => BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) (gensym p.2 p.1)).reverse).prod)
        (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w))

/-- **DYNAMIC clause** (named input `RD8362E5EBInput hκ F G`, printed R-8362E5EB): along every fixed smooth
hierarchy trajectory `u` with `‖physical u‖ = 1`, on every compact joint-time box `TimeBox R lo hi`, and for
every norm-close preparation `ψ` (`Preparation u ψ`), `W^G_N(f)` has the strong symbol `f(w(u,t))` and its adjoint
the conjugate. The gauge is the one of the supplied input `D`. -/
def DynamicClause (hκ : 0 < κ) : Prop :=
  ∀ (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge) (D : RD8362E5EBInput hκ F G)
    (u : Def033HierarchyR24m.Smooth L), ‖Def033HierarchyR24m.physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ {f : Sym}, Balanced f →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f)
        (fun n => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) G f).adjoint)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) f)

/-- Dynamic scaled Dirac commutator: symbol `{f,h}(w(u,t)) = evalSym (pb S f h)`. -/
def DynamicDiracClause (hκ : 0 < κ) : Prop :=
  ∀ (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge) (D : RD8362E5EBInput hκ F G)
    (u : Def033HierarchyR24m.Smooth L), ‖Def033HierarchyR24m.physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ {f h : Sym}, Balanced f → Balanced h →
      ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf h ⊆ S →
      HasUniformStrongT (H := fun n => HN L (1 + n))
        (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
          (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G h
            - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G h
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f))
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (WickSymbols.pb S f h))

/-- Dynamic ordered products of generators: product symbol `∏ z_{a_j} conj z_{b_j}`. -/
def DynamicWordClause (hκ : 0 < κ) : Prop :=
  ∀ (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge) (D : RD8362E5EBInput hκ F G)
    (u : Def033HierarchyR24m.Smooth L), ‖Def033HierarchyR24m.physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ (w : List (ℤ × ℤ)),
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) G w)
        (fun n => ((w.map fun p => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) G (gensym p.2 p.1)).reverse).prod)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (wordSym w))

/-! ### Proofs of the clauses (from the stage modules) -/

theorem stage1_clause : Stage1Clause L := by
  intro N hN b G f f'
  exact FullWickH1.fullWick_stage1 hN b G f f'

theorem stage2_clause : Stage2Clause L := by
  refine ⟨?_, ?_⟩
  · intro b G I f hb hI
    exact FullWickH2.quantization_norm_limit b G I hb hI
  · intro I f hb hI
    exact FullWickH3.unitBallSup_eq_l2_max I hb hI

theorem static_clause (hκ : 0 < κ) : StaticClause L κ hκ := by
  intro j q hU Θ Tb R f hf
  exact FullWickH8.static_poly_pair hκ hU Tb R hf

theorem static_selected_clause (hκ : 0 < κ) : StaticSelectedClause L κ hκ := by
  intro Θ Tb R f hf
  exact FullWickH8.static_poly_pair_selected hκ Tb R hf

theorem static_normClose_clause (hκ : 0 < κ) : StaticNormCloseClause L κ hκ := by
  intro j q hU Θ Tb R f hf ψ' hprep
  exact FullWickH8.static_poly_normClose hκ hU Tb R hf hprep

theorem static_dirac_clause (hκ : 0 < κ) : StaticDiracClause L κ hκ := by
  intro j q hU Θ Tb R f g hf hg S hSf hSg
  exact FullWickH8.static_dirac hκ hU Tb R hf hg hSf hSg

theorem static_word_clause (hκ : 0 < κ) : StaticWordClause L κ hκ := by
  intro j q hU Θ Tb R w
  exact FullWickH8.static_word_pair hκ hU Tb R w

theorem dynamic_clause (hκ : 0 < κ) : DynamicClause L κ hκ := by
  intro F G D u hu R lo hi ψ hψ f hf
  exact FullWickH9.dyn_poly_pair hκ F G D u hu R lo hi ψ hψ hf

theorem dynamic_dirac_clause (hκ : 0 < κ) : DynamicDiracClause L κ hκ := by
  intro F G D u hu R lo hi ψ hψ f h hf hh S hSf hSh
  exact FullWickH9.dyn_dirac hκ F G D u hu R lo hi ψ hψ hf hh hSf hSh

theorem dynamic_word_clause (hκ : 0 < κ) : DynamicWordClause L κ hκ := by
  intro F G D u hu R lo hi ψ hψ w
  exact FullWickH9.dyn_word_pair hκ F G D u hu R lo hi ψ hψ w

/-- **The printed theorem `thm:full-wick` (R-140AE34B), full statement, as a pre-start intermediate.**
Stage 1 and Stage 2 (unconditional), the STATIC clause with parameter predicate `UniformStatic hκ j q`,
its selected-witness corollary, norm-close preparations, the static scaled Dirac commutator and ordered
products, and the DYNAMIC clauses along hierarchy trajectories via the named input `RD8362E5EBInput`. -/
theorem thm_full_wick_printed (hκ : 0 < κ) :
    Stage1Clause L ∧ Stage2Clause L ∧ StaticClause L κ hκ ∧ StaticSelectedClause L κ hκ
      ∧ StaticNormCloseClause L κ hκ ∧ StaticDiracClause L κ hκ ∧ StaticWordClause L κ hκ
      ∧ DynamicClause L κ hκ ∧ DynamicDiracClause L κ hκ ∧ DynamicWordClause L κ hκ :=
  ⟨stage1_clause L, stage2_clause L, static_clause L κ hκ, static_selected_clause L κ hκ,
    static_normClose_clause L κ hκ, static_dirac_clause L κ hκ, static_word_clause L κ hκ,
    dynamic_clause L κ hκ, dynamic_dirac_clause L κ hκ, dynamic_word_clause L κ hκ⟩

/-- **Q06 gauge instance of the dynamic clause (the printed dynamic statement for W^q).** This is the dynamic
clause for the gauge `staticGauge q`; it is available exactly when the R-8362E5EB input `D` is supplied at that
gauge. It does not identify the supplied gauge of an arbitrary input with the static one. -/
theorem dynamic_clause_at_Q06 (hκ : 0 < κ) (q : UniformStaticR49b.SectorGauge)
    (F : ActualModelTargetR53a.HigherFlows L κ) (D : RD8362E5EBInput hκ F (staticGauge q)) :
    ∀ (u : Def033HierarchyR24m.Smooth L), ‖Def033HierarchyR24m.physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ {f : Sym}, Balanced f →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f)
        (fun n => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f).adjoint)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) f) :=
  by
    intro u hu R lo hi ψ hψ f hf
    exact dynamic_clause L κ hκ F (staticGauge q) D u hu R lo hi ψ hψ hf

end QuantumNLS.FullWickH10

#print axioms QuantumNLS.FullWickH10.stage1_clause
#print axioms QuantumNLS.FullWickH10.stage2_clause
#print axioms QuantumNLS.FullWickH10.static_clause
#print axioms QuantumNLS.FullWickH10.static_selected_clause
#print axioms QuantumNLS.FullWickH10.static_normClose_clause
#print axioms QuantumNLS.FullWickH10.static_dirac_clause
#print axioms QuantumNLS.FullWickH10.static_word_clause
#print axioms QuantumNLS.FullWickH10.dynamic_clause
#print axioms QuantumNLS.FullWickH10.dynamic_dirac_clause
#print axioms QuantumNLS.FullWickH10.dynamic_word_clause
#print axioms QuantumNLS.FullWickH10.thm_full_wick_printed
#print axioms QuantumNLS.FullWickH10.dynamic_clause_at_Q06

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickH10." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickH10." then
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
  Lean.logInfo m!"FullWickH10 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
