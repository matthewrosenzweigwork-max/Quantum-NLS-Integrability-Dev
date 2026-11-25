import QuantumNLS.MainTheoremR02
import QuantumNLS.CountFunctionsS01Final

/-!
# MainTheoremR03Count: gap G1 of R-AF8F7562 `thm:main` part (iii) as clauses at the thm:main gauge `G q`

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex` (sha256 `6008c7e6…da56`) lines 42-51:
```
Every fixed ordered word in these bounded observables, their adjoints, and continuous functions of finitely many
intensive counts has the product of the corresponding scalar symbols, in the same strong and compact-time-uniform
sense. In particular, its expectation converges. For finite expressions made from the Cartesian transfers and C²
functions of finitely many counts, with classical expressions A,C,
  sup_{t∈K} ‖(N/i [A_N,C_N] - {A,C}(Φ_t(u))) U_N(t)ψ_N‖ → 0,   sup_N ‖N[A_N,C_N]‖ < ∞.      (eq:dirac-main)
The precise C² class and regularized relative phases are given in Section sec:algebra. Raw unit-phase generators are
not included in this general first-order algebra.
```
and `source-text/chapters/core/canonical_algebra.tex` (sha256 `b2a1e9c4…0395`) lines 37-57 (the first-order class,
eq:finite-difference, eq:words, regularized relative phases).

All content is sonnet_fourier's FROZEN `CountFunctionsS01{Ops,Calc,Sym,Prod,Poisson,Class,Words,Engine,Dirac,Phase,
Final}` (review records/sonnet_fourier.md, section "R-AF8F7562 gap G1"); this module only restates the statements at the
thm:main gauge `G q` and actual flows `F hκ` of `MainTheoremR01`, and discharges them at the named witness
`q = sectorGauge hκ`:

* dynamic words/expectations: `CountFunctionsS01Final.g1a_dynamic_words`, `g1a_dynamic_expectation` (stated there at
  `DynamicGaugeFinalR35m.gauge hκ`, which is `G (sectorGauge hκ)` by `MainTheoremR01.gauge_named`, `rfl`);
* static words: `CountFunctionsS01Words.static_words` at the selected witness
  `UniformStaticR49b.selected_uniform_static hκ`;
* eq:dirac-main for the first-order class `Expr J`: `CountFunctionsS01Final.g1b_dynamic_dirac`,
  `g1b_dynamic_expr_pair`; static `CountFunctionsS01Dirac.static_dirac`, `static_expr_pair` (gauge
  `FullWickO1.staticGauge q = G q` by `MainTheoremR01.gauge_static`);
* regularized relative phases: `CountFunctionsS01Phase.regPhaseExpr` (`E^q_{N,ab} f(B_{N,J})`, an element of the class),
  `regPhase_cl` (symbol `χ_a(a_a)χ_b(a_b)ζ_ab`), `cutoff_exists`.

REVIEWER NOTES (carried over from sonnet_fourier):
1. canonical_algebra.tex:45 states eq:finite-difference with an `O(N⁻¹)` remainder; the frozen Lean proves the uniform
   `o(1)` form (`CountFunctionsS01Calc.fd_scaled_close_H`), which suffices for the printed conclusions (strong
   convergence in eq:dirac-main and the uniform scaled bound).  No statement here is narrowed by this.
2. Static words exclude unit-phase letters (`CountFunctionsS01Words.AdmS (.phase _ _) = False`), matching printed
   part (ii), which gives unit-phase symbols only on classes with a fixed positive lower bound on both actions.
   Dynamic words include unit-phase letters under the printed hypothesis `a ≠ b`, `a_a(u) a_b(u) > 0` (`Adm`).
No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.MainTheoremR03Count

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (Preparation TimeBox)
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
open QuantumNLS.UniformStaticR49b (SectorGauge)
open QuantumNLS.MainTheoremR01 (G F)
open QuantumNLS.CountFunctionsS01Words (WLetter Adm AdmS wOp wSym sOp)
open QuantumNLS.CountFunctionsS01Class (Expr)
open QuantumNLS.CountFunctionsS01Poisson (poisson)
open QuantumNLS.CountFunctionsS01Dirac (res)
open QuantumNLS.CountFunctionsS01Phase (regPhase regPhaseExpr)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ### G1(a): ordered words with count functions -/

/-- **Dynamic ordered words** (printed lines 42-43) at gauge `g` and the actual flows `F hκ`: every fixed word of
admissible letters — Cartesian transfers `E^g_{N,ab}`, unit-phase transfers `W^g_{N,ab}` (`a ≠ b`, both initial actions
positive), continuous functions `f(B_{N,J})` of finitely many intensive counts, balanced Wick quantizations — and their
adjoints has, along `U_N(t)ψ_N` for every normalized norm-close preparation and uniformly on every compact box, the
product of the letter symbols (the reversed product of adjoints the conjugate), and its expectation converges. -/
def DynamicCountWords (hκ : 0 < κ) (g : Gauge) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ → ∀ (l : List WLetter), (∀ ℓ ∈ l, Adm hκ u ℓ.base) →
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (l.map fun ℓ => wOp (L := L) hκ g n ℓ).prod)
      (fun n => ((l.map fun ℓ => (wOp (L := L) hκ g n ℓ).adjoint).reverse).prod)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        (l.map fun ℓ => wSym (ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ) ℓ).prod) ∧
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ TimeBox R lo hi,
      ‖⟪ReconstructionR33m.U (L := L) hκ R t n (ψ n),
          (l.map fun ℓ => wOp (L := L) hκ g n ℓ).prod (ReconstructionR33m.U (L := L) hκ R t n (ψ n))⟫_ℂ -
        (l.map fun ℓ => wSym (ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ) ℓ).prod‖ ≤ ε

/-- **Static ordered words** (uniform on `𝒰_R`, product preparations, the static input at `q`): every fixed word of
Cartesian transfers, continuous count functions, balanced Wick quantizations and adjoints has the product symbol.
Unit-phase letters are excluded (reviewer note 2). -/
def StaticCountWords (hκ : 0 < κ) (q : SectorGauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (l : List WLetter), (∀ ℓ ∈ l, AdmS ℓ.base) →
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => (l.map fun ℓ => sOp (L := L) hκ q n ℓ).prod)
      (fun n => ((l.map fun ℓ => (sOp (L := L) hκ q n ℓ).adjoint).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) =>
        (l.map fun ℓ => wSym ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) ℓ).prod)

/-! ### G1(b): eq:dirac-main for the first-order class -/

/-- **eq:dirac-main for the first-order class, dynamic** (printed lines 44-51) at gauge `g`: for every finite label
set `J` and all `A, C : Expr J` (finite sums, products, scalar multiples and adjoints of the Cartesian transfers and of
`C²` functions of the counts `B_{N,J}`), `A_N` has the strong symbol `A(Φ_t u)` (adjoint: conjugate),
`(N/i)[A_N,C_N] → {A,C}(Φ_t u)` strongly along `U_N(t)ψ_N` uniformly on the box, and `sup_N ‖N[A_N,C_N]‖ < ∞`
(`N = 1 + n`). -/
def DynamicDiracClass (hκ : 0 < κ) (g : Gauge) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ → ∀ {J : Finset ℤ} (A C : Expr J),
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => A.op (ReconstructionR33m.basis (L := L) hκ n) g)
      (fun n => (A.op (ReconstructionR33m.basis (L := L) hκ n) g).adjoint)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) => A.cl (res J (ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ))) ∧
    HasUniformStrongT (H := fun n => HN L (1 + n))
      (fun n => (-Complex.I * ((1 + n : ℕ) : ℂ)) •
        (A.op (ReconstructionR33m.basis (L := L) hκ n) g * C.op (ReconstructionR33m.basis (L := L) hκ n) g -
          C.op (ReconstructionR33m.basis (L := L) hκ n) g * A.op (ReconstructionR33m.basis (L := L) hκ n) g))
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        poisson A.cl C.cl (res J (ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ))) ∧
    ∃ M : ℝ, ∀ n : ℕ,
      ‖((1 + n : ℕ) : ℂ) •
        (A.op (ReconstructionR33m.basis (L := L) hκ n) g * C.op (ReconstructionR33m.basis (L := L) hκ n) g -
          C.op (ReconstructionR33m.basis (L := L) hκ n) g * A.op (ReconstructionR33m.basis (L := L) hκ n) g)‖ ≤ M

/-- **eq:dirac-main for the first-order class, static form** (uniform on `𝒰_R`, product preparations,
`N = n + 1`) at the gauge `G q`. -/
def StaticDiracClass (hκ : 0 < κ) (q : SectorGauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {J : Finset ℤ} (A C : Expr J),
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q))
      (fun n => (A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q)).adjoint)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) => A.cl (res J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ))) ∧
    HasUniformStrongT (H := fun n => HN L (n + 1))
      (fun n => (-Complex.I * ((n + 1 : ℕ) : ℂ)) •
        (A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) *
            C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) -
          C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) *
            A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q)))
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) => poisson A.cl C.cl (res J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ))) ∧
    ∃ M : ℝ, ∀ n : ℕ,
      ‖((n + 1 : ℕ) : ℂ) •
        (A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) *
            C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) -
          C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q) *
            A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (G q))‖ ≤ M

/-! ### Regularized relative phases (canonical_algebra.tex:56-57) -/

/-- **Regularized relative phases** at gauge `g`: for `C²` cutoffs `χ_a, χ_b` vanishing on `(-δ, δ)`, the operator
`E^g_{N,ab} f(B_{N,J})`, `f(x) = χ_a(x_a)χ_b(x_b)/√(x_a x_b)` (zero near the excluded faces), is the element
`regPhaseExpr` of the first-order class (so `DynamicDiracClass`/`StaticDiracClass` apply to every expression in
these phases); its classical symbol is `χ_a(a_a)χ_b(a_b) ζ_ab`; along the dynamics it has the strong symbol
`χ_a(|w_a|²)χ_b(|w_b|²) ζ_ab(w(Φ_t u))` (adjoint: conjugate); and at a positive action `α` there are `C²` cutoffs
vanishing near zero and equal to one on a neighborhood of `α`. -/
def RegPhaseClause (hκ : 0 < κ) (g : Gauge) : Prop :=
  (∀ {J : Finset ℤ} (a b : ↥J) {χa χb : ℝ → ℝ} (ha : ContDiff ℝ 2 χa) (hb : ContDiff ℝ 2 χb) {δ : ℝ}
      (hδ : 0 < δ) (hza : ∀ x, |x| < δ → χa x = 0) (hzb : ∀ x, |x| < δ → χb x = 0),
    (∀ {N : ℕ} (B : BetheCoefficientTransform.BetheBasis L N),
      (regPhaseExpr a b ha hb hδ hza hzb).op B g =
        CartesianOccupationTransfer.physical B g (a : ℤ) (b : ℤ) *
          CountFunctionsS01Ops.countOp B g J (regPhase a b χa χb)) ∧
    (∀ z : CountFunctionsS01Poisson.CPt J, (regPhaseExpr a b ha hb hδ hza hzb).cl z =
      ((χa (‖z a‖ ^ 2) * χb (‖z b‖ ^ 2) : ℝ) : ℂ) *
        ((z a * conj (z b)) / ((Real.sqrt (‖z a‖ ^ 2 * ‖z b‖ ^ 2) : ℝ) : ℂ))) ∧
    (∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ)
      (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => (regPhaseExpr a b ha hb hδ hza hzb).op (ReconstructionR33m.basis (L := L) hκ n) g)
        (fun n => ((regPhaseExpr a b ha hb hδ hza hzb).op (ReconstructionR33m.basis (L := L) hκ n) g).adjoint)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          ((χa (‖(ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ) (a : ℤ)‖ ^ 2) *
              χb (‖(ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ) (b : ℤ)‖ ^ 2) : ℝ) : ℂ) *
            (((ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ) (a : ℤ) *
                conj ((ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ) (b : ℤ))) /
              ((Real.sqrt (‖(ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ) (a : ℤ)‖ ^ 2 *
                ‖(ReconstructionR33m.w hκ (F (L := L) hκ) u R t : ℤ → ℂ) (b : ℤ)‖ ^ 2) : ℝ) : ℂ))))) ∧
  (∀ {α : ℝ}, 0 < α →
    ∃ χ : ℝ → ℝ, ContDiff ℝ 2 χ ∧ (∀ x, |x| < α / 2 → χ x = 0) ∧ (∀ x, |x - α| ≤ α / 4 → χ x = 1))

/-! ### The G1 clause and its discharge at the named witness -/

/-- **G1**: everything printed in part (iii) lines 42-51 that R02 did not carry, at the single gauge `G q`. -/
def G1Clause (hκ : 0 < κ) (q : SectorGauge) : Prop :=
  DynamicCountWords (L := L) hκ (G q) ∧ StaticCountWords (L := L) hκ q ∧
    DynamicDiracClass (L := L) hκ (G q) ∧ StaticDiracClass (L := L) hκ q ∧ RegPhaseClause (L := L) hκ (G q)

theorem dynamic_count_words (hκ : 0 < κ) :
    DynamicCountWords (L := L) hκ (G (RetargetSelectionR49b.sectorGauge (L := L) hκ)) :=
  fun u hu R lo hi ψ hψ l hl =>
    ⟨CountFunctionsS01Final.g1a_dynamic_words hκ u hu R lo hi ψ hψ l hl,
      CountFunctionsS01Final.g1a_dynamic_expectation hκ u hu R lo hi ψ hψ l hl⟩

theorem static_count_words (hκ : 0 < κ) :
    StaticCountWords (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  fun Tb R l hl => CountFunctionsS01Words.static_words hκ (UniformStaticR49b.selected_uniform_static hκ) Tb R l hl

theorem dynamic_dirac_class (hκ : 0 < κ) :
    DynamicDiracClass (L := L) hκ (G (RetargetSelectionR49b.sectorGauge (L := L) hκ)) := by
  intro u hu R lo hi ψ hψ J A C
  exact ⟨CountFunctionsS01Final.g1b_dynamic_expr_pair hκ u hu R lo hi ψ hψ A,
    CountFunctionsS01Final.g1b_dynamic_dirac hκ u hu R lo hi ψ hψ A C⟩

theorem static_dirac_class (hκ : 0 < κ) :
    StaticDiracClass (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) := by
  intro Θ Tb R J A C
  rw [MainTheoremR01.gauge_static]
  exact ⟨CountFunctionsS01Dirac.static_expr_pair hκ (UniformStaticR49b.selected_uniform_static hκ) Tb R A,
    CountFunctionsS01Dirac.static_dirac hκ (UniformStaticR49b.selected_uniform_static hκ) Tb R A C⟩

theorem reg_phase_clause (hκ : 0 < κ) :
    RegPhaseClause (L := L) hκ (G (RetargetSelectionR49b.sectorGauge (L := L) hκ)) := by
  refine ⟨?_, fun hα => CountFunctionsS01Phase.cutoff_exists hα⟩
  intro J a b χa χb ha hb δ hδ hza hzb
  refine ⟨fun B => rfl, fun z => CountFunctionsS01Phase.regPhase_cl a b ha hb hδ hza hzb z, ?_⟩
  intro u hu R lo hi ψ hψ
  have h := CountFunctionsS01Final.g1b_dynamic_expr_pair hκ u hu R lo hi ψ hψ (regPhaseExpr a b ha hb hδ hza hzb)
  simp only [CountFunctionsS01Phase.regPhase_cl] at h
  exact h

/-- **G1 at the named witness** `q = sectorGauge hκ`. -/
theorem g1_clause (hκ : 0 < κ) : G1Clause (L := L) hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨dynamic_count_words hκ, static_count_words hκ, dynamic_dirac_class hκ, static_dirac_class hκ,
    reg_phase_clause hκ⟩

/-- The dynamic G1 clauses at the named witness are literally the frozen `CountFunctionsS01Final` statements
(the gauge `G (sectorGauge hκ)` is `DynamicGaugeFinalR35m.gauge hκ` and `F hκ` is
`flows hκ (DynamicGaugeFinalR35m.hierarchy hκ)`, both by `rfl`). -/
theorem gauge_and_flows_named (hκ : 0 < κ) :
    G (RetargetSelectionR49b.sectorGauge (L := L) hκ) = DynamicGaugeFinalR35m.gauge (L := L) hκ ∧
      F (L := L) hκ = ReconstructionR33m.flows hκ (DynamicGaugeFinalR35m.hierarchy (L := L) hκ) :=
  ⟨rfl, rfl⟩

end QuantumNLS.MainTheoremR03Count

#print axioms QuantumNLS.MainTheoremR03Count.dynamic_count_words
#print axioms QuantumNLS.MainTheoremR03Count.static_count_words
#print axioms QuantumNLS.MainTheoremR03Count.dynamic_dirac_class
#print axioms QuantumNLS.MainTheoremR03Count.static_dirac_class
#print axioms QuantumNLS.MainTheoremR03Count.reg_phase_clause
#print axioms QuantumNLS.MainTheoremR03Count.g1_clause
