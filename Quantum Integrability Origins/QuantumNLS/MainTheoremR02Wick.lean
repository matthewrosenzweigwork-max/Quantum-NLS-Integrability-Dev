import QuantumNLS.MainTheoremR01
import QuantumNLS.FullWickFinalH15

/-!
# MainTheoremR02Wick: the R-140AE34B `thm:full-wick` content of parts (ii)/(iii), REBOUND to the auxiliary construction's frozen final
`FullWickFinalH15.thm_full_wick_Q06_final` (source sha256 `89d9204b…edead`, accepted terra_review r274)

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex` (sha256 `6008c7e6…da56`) lines 31-33 (part (ii):
"The balanced polynomial quantization … has uniform static symbols for every fixed polynomial, the exact contraction
formula, an operator-norm product remainder of order `N^{-2}` …, a scaled Dirac remainder of order `N^{-1}`, and
convergence of its norm to the classical supremum norm") and lines 52-53 (part (iii): "The fixed balanced polynomial
quantization … has the same strong dynamical symbols, adjoints and norm-close stability").

The twelve family conjunct statements of `FullWickFinalH15` (`Q06Static` … `Q06DynamicPolyProduct`) are copied here
verbatim with the Q06 gauge `FullWickFinalH15.q06 L κ hκ` replaced by a gauge parameter `gq` (and `q06Flows` written
as `MainTheoremR01.F hκ`, the same term).  `same_statements_q06` checks by `Iff.rfl` that at `g = q06` each copy IS
the corresponding H15 statement.  The thm:main gauge `G q` equals `q06` at the named witness by
`MainTheoremR01.gauge_static` (`FullWickO3.physicalGauge_eq_staticGauge`), so the clauses at `G q` are proved from
the H15 headline only (`fullWick_G`); the FullWickH10/H12/H13 v3 clause terms of MainTheoremR01 are no longer used
by the assembly.  The ordered Cartesian words of part (iii) are re-derived from the H15 dynamic word conjunct
(`cartesian_words_of`).  No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.MainTheoremR02Wick

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH7 (IsNormClosePrepT)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.WickSymbols (Sym Balanced)
open QuantumNLS.WickBounds (gensym wordSym labelsOf)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (Preparation TimeBox RD8362E5EBInput)
open QuantumNLS.FullWickS1 (orderedWord)
open Def033HierarchyR24m (Smooth physical)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ### The H15 conjunct statements at a gauge parameter (verbatim copies, `q06 ↦ gq`) -/

/-- Conjunct 3: static strong symbol on `𝒰_R` (printed wick_calculus.tex:82-83). -/
def WStatic (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq f)
      (fun n => (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n)
        gq f).adjoint)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)

/-- Conjunct 4: uniformly norm-close preparations preserve the static strong symbol. -/
def WStaticNormClose (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
    ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (1 + n)},
      IsNormClosePrepT (H := fun n => HN L (1 + n)) ψ'
        (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))) (UR (L := L) R) Tb →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq f)
        (fun n => (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n)
          gq f).adjoint)
        (UR (L := L) R) Tb ψ' (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)

/-- Conjunct 5: static scaled Dirac commutator, symbol `{f,g}(w(u))`. -/
def WStaticDirac (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f g : Sym}, Balanced f → Balanced g →
    ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf g ⊆ S →
      HasUniformStrongT (H := fun n => HN L (1 + n))
        (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
          (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq f
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq g
            - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq g
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq f))
        (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (WickSymbols.pb S f g))

/-- Conjunct 6: static ordered products of generators, symbol `∏ z_{a_j} conj z_{b_j}`. -/
def WStaticWord (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ)),
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) gq w)
      (fun n => ((w.map fun p => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) gq (gensym p.2 p.1)).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w))

/-- Conjunct 7: dynamic strong symbol along every hierarchy trajectory, time box and norm-close preparation. -/
def WDynamic (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ {f : Sym}, Balanced f →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq f)
        (fun n => (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n)
          gq f).adjoint)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ (MainTheoremR01.F (L := L) hκ) u R t : ℤ → ℂ)) f)

/-- Conjunct 8: dynamic scaled Dirac commutator. -/
def WDynamicDirac (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ {f h : Sym}, Balanced f → Balanced h →
      ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf h ⊆ S →
      HasUniformStrongT (H := fun n => HN L (1 + n))
        (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
          (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq f
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq h
            - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq h
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq f))
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          evalSym ((ReconstructionR33m.w hκ (MainTheoremR01.F (L := L) hκ) u R t : ℤ → ℂ)) (WickSymbols.pb S f h))

/-- Conjunct 9: dynamic ordered products of generators. -/
def WDynamicWord (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ (w : List (ℤ × ℤ)),
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) gq w)
        (fun n => ((w.map fun p => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) gq (gensym p.2 p.1)).reverse).prod)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ (MainTheoremR01.F (L := L) hκ) u R t : ℤ → ℂ)) (wordSym w))

/-- Conjunct 10: norm-close static ordered products. -/
def WStaticWordNormClose (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ)) {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (1 + n)},
    IsNormClosePrepT (H := fun n => HN L (1 + n)) ψ'
      (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))) (UR (L := L) R) Tb →
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) gq w)
      (fun n => ((w.map fun p => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) gq (gensym p.2 p.1)).reverse).prod)
      (UR (L := L) R) Tb ψ'
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w))

/-- Conjunct 11: norm-close static scaled Dirac commutator. -/
def WStaticDiracNormClose (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f g : Sym}, Balanced f → Balanced g →
    ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf g ⊆ S →
    ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (1 + n)},
      IsNormClosePrepT (H := fun n => HN L (1 + n)) ψ'
        (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))) (UR (L := L) R) Tb →
      HasUniformStrongT (H := fun n => HN L (1 + n))
        (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
          (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq f
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq g
            - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq g
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) gq f))
        (UR (L := L) R) Tb ψ'
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (WickSymbols.pb S f g))

/-- Conjunct 12: static ordered products of balanced polynomials on `𝒰_R`. -/
def WStaticPolyProduct (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (fs : List Sym), (∀ g ∈ fs, Balanced g) →
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (fs.map fun g => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) gq g).prod)
      (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) gq g).adjoint).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (fun (u : L2T L) (_ : Θ) => (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod)

/-- Conjunct 13: norm-close static ordered products of balanced polynomials. -/
def WStaticPolyProductNormClose (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (fs : List Sym), (∀ g ∈ fs, Balanced g) →
    ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (1 + n)},
      IsNormClosePrepT (H := fun n => HN L (1 + n)) ψ'
        (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))) (UR (L := L) R) Tb →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => (fs.map fun g => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) gq g).prod)
        (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) gq g).adjoint).reverse).prod)
        (UR (L := L) R) Tb ψ'
        (fun (u : L2T L) (_ : Θ) => (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod)

/-- Conjunct 14: dynamic ordered products of balanced polynomials along hierarchy trajectories. -/
def WDynamicPolyProduct (hκ : 0 < κ) (gq : Gauge) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ (fs : List Sym), (∀ g ∈ fs, Balanced g) →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => (fs.map fun g => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) gq g).prod)
        (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) gq g).adjoint).reverse).prod)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          (fs.map fun g => evalSym ((ReconstructionR33m.w hκ (MainTheoremR01.F (L := L) hκ) u R t : ℤ → ℂ)) g).prod)

/-! ### Grouping, identification with H15, and the proof from the H15 headline -/

/-- The static part (printed part (ii)): H15 conjuncts 1-6 and 10-13 at gauge `g`. -/
def FullWickStatic (hκ : 0 < κ) (g : Gauge) : Prop :=
  FullWickH10.Stage1Clause L ∧ FullWickH10.Stage2Clause L ∧ WStatic (L := L) hκ g ∧ WStaticNormClose (L := L) hκ g ∧
    WStaticDirac (L := L) hκ g ∧ WStaticWord (L := L) hκ g ∧ WStaticWordNormClose (L := L) hκ g ∧ WStaticDiracNormClose (L := L) hκ g ∧
    WStaticPolyProduct (L := L) hκ g ∧ WStaticPolyProductNormClose (L := L) hκ g

/-- The dynamic part (printed part (iii)): H15 conjuncts 7, 8, 9, 14 at gauge `g`. -/
def FullWickDynamic (hκ : 0 < κ) (g : Gauge) : Prop :=
  WDynamic (L := L) hκ g ∧ WDynamicDirac (L := L) hκ g ∧ WDynamicWord (L := L) hκ g ∧ WDynamicPolyProduct (L := L) hκ g

/-- At the Q06 gauge each copied statement is literally the H15 statement. -/
theorem same_statements_q06 (hκ : 0 < κ) :
    (WStatic (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06Static L κ hκ) ∧
    (WStaticNormClose (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06StaticNormClose L κ hκ) ∧
    (WStaticDirac (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06StaticDirac L κ hκ) ∧
    (WStaticWord (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06StaticWord L κ hκ) ∧
    (WDynamic (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06Dynamic L κ hκ) ∧
    (WDynamicDirac (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06DynamicDirac L κ hκ) ∧
    (WDynamicWord (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06DynamicWord L κ hκ) ∧
    (WStaticWordNormClose (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06StaticWordNormClose L κ hκ) ∧
    (WStaticDiracNormClose (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔
      FullWickFinalH15.Q06StaticDiracNormClose L κ hκ) ∧
    (WStaticPolyProduct (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06StaticPolyProduct L κ hκ) ∧
    (WStaticPolyProductNormClose (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔
      FullWickFinalH15.Q06StaticPolyProductNormClose L κ hκ) ∧
    (WDynamicPolyProduct (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ↔ FullWickFinalH15.Q06DynamicPolyProduct L κ hκ) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Both parts at the Q06 gauge, from the H15 headline only. -/
theorem fullWick_q06 (hκ : 0 < κ) :
    FullWickStatic (L := L) hκ (FullWickFinalH15.q06 L κ hκ) ∧
      FullWickDynamic (L := L) hκ (FullWickFinalH15.q06 L κ hκ) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ :=
    FullWickFinalH15.thm_full_wick_Q06_final L κ hκ
  exact ⟨⟨c1, c2, c3, c4, c5, c6, c10, c11, c12, c13⟩, ⟨c7, c8, c9, c14⟩⟩

/-- **The full-wick clauses at the thm:main gauge `G q`**, at the named witness `q = sectorGauge hκ`. -/
theorem fullWick_G (hκ : 0 < κ) :
    FullWickStatic (L := L) hκ (MainTheoremR01.G (RetargetSelectionR49b.sectorGauge (L := L) hκ)) ∧
      FullWickDynamic (L := L) hκ (MainTheoremR01.G (RetargetSelectionR49b.sectorGauge (L := L) hκ)) := by
  rw [MainTheoremR01.gauge_static]
  exact fullWick_q06 hκ

/-! ### Ordered Cartesian words (part (iii)) from the H15 dynamic word conjunct -/

/-- Dynamic strong symbols of every fixed ordered word in the Cartesian transfers `E^g_{ab}` and their adjoints,
with the product symbol, from `WDynamicWord` at the same gauge. -/
theorem cartesian_words_of (hκ : 0 < κ) (g : Gauge) (hW : WDynamicWord (L := L) hκ g)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (w : List (ℤ × ℤ)) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (w.map fun p => ReconstructionR33m.E (L := L) hκ g n p.1 p.2).prod)
      (fun n => ((w.map fun p => (ReconstructionR33m.E (L := L) hκ g n p.1 p.2).adjoint).reverse).prod)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        (w.map fun p => (ReconstructionR33m.w hκ (MainTheoremR01.F (L := L) hκ) u R t : ℤ → ℂ) p.1 *
          conj ((ReconstructionR33m.w hκ (MainTheoremR01.F (L := L) hκ) u R t : ℤ → ℂ) p.2)).prod) := by
  have h := hW u hu R lo hi ψ hψ w
  simp only [MainTheoremR01Algebra.orderedWord_eq_E, MainTheoremR01Algebra.orderedWord_adj_eq_E,
    WickSpectralBridge.evalSym_wordSym] at h
  exact h

/-- Expectations of the Cartesian words converge uniformly on the box. -/
theorem cartesian_word_expectation_of (hκ : 0 < κ) (g : Gauge) (hW : WDynamicWord (L := L) hκ g)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (w : List (ℤ × ℤ)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ TimeBox R lo hi,
      ‖⟪ReconstructionR33m.U (L := L) hκ R t n (ψ n),
          (w.map fun p => ReconstructionR33m.E (L := L) hκ g n p.1 p.2).prod
            (ReconstructionR33m.U (L := L) hκ R t n (ψ n))⟫_ℂ -
        (w.map fun p => (ReconstructionR33m.w hκ (MainTheoremR01.F (L := L) hκ) u R t : ℤ → ℂ) p.1 *
          conj ((ReconstructionR33m.w hκ (MainTheoremR01.F (L := L) hκ) u R t : ℤ → ℂ) p.2)).prod‖ ≤ ε := by
  intro ε hε
  have h := (cartesian_words_of hκ g hW u hu R lo hi ψ hψ w).1 ε hε
  filter_upwards [h] with n hn
  intro t ht
  have hv : ‖ReconstructionR33m.U (L := L) hκ R t n (ψ n)‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hψ.1 n
  exact (MainTheoremR01Algebra.expectation_le _ _ _ hv).trans (hn () (Set.mem_univ _) t ht)

end QuantumNLS.MainTheoremR02Wick

#print axioms QuantumNLS.MainTheoremR02Wick.same_statements_q06
#print axioms QuantumNLS.MainTheoremR02Wick.fullWick_G
#print axioms QuantumNLS.MainTheoremR02Wick.cartesian_words_of
#print axioms QuantumNLS.MainTheoremR02Wick.cartesian_word_expectation_of
