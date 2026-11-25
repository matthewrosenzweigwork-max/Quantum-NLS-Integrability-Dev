import QuantumNLS.FullWickH14
import QuantumNLS.FullWickO3
import QuantumNLS.FullWickO4
import QuantumNLS.RB7BindFinal
import QuantumNLS.ActualModelCorollaryR60a
import QuantumNLS.ActualModelBindingR53a
import QuantumNLS.TerraMultiFinalR94
import QuantumNLS.TerraMultiRound93Flow
import QuantumNLS.DynSeedR47b

/-! FullWickFinalH15 (haiku_inventory, R-140AE34B `thm:full-wick`, final binding at the Q06 gauge).

Headline `FullWickFinalH15.thm_full_wick_Q06_final L κ hκ`: the printed theorem at the Q06 gauge
`staticGauge (sectorGauge hκ)`, stated for ONE operator family
`W_n(f) = quantization (ReconstructionR33m.basis hκ n) (staticGauge (sectorGauge hκ)) f` on `HN L (1+n)`.
Its only hypothesis is the printed one, `0 < κ` (with `Fact (0 < L)`).

Fourteen conjuncts, in the order of the v3 headline `FullWickH14.thm_full_wick_printed_v3`
(which has fifteen; its second conjunct `StaticSelectedClause` coincides with the first static conjunct after
instantiation at the selected witness, so it is not repeated):

  1  Stage1Clause                    unchanged (family-free, FullWickH10)
  2  Stage2Clause                    unchanged (family-free, FullWickH10)
  3  Q06Static                       v3 StaticClause at the selected pair; = FullWickO4 full_wick_Q06_one_family (1)
  4  Q06StaticNormClose              v3 StaticNormCloseClause, norm-close transport
  5  Q06StaticDirac                  v3 StaticDiracClause, strong transport
  6  Q06StaticWord                   v3 StaticWordClause, pair transport
  7  Q06Dynamic                      FullWickO4 full_wick_Q06_one_family (2) = v3 DynamicClause instance
  8  Q06DynamicDirac                 FullWickO4 full_wick_Q06_one_family (3) = v3 DynamicDiracClause instance
  9  Q06DynamicWord                  FullWickO4 full_wick_Q06_one_family (4) = v3 DynamicWordClause instance
  10 Q06StaticWordNormClose          v3 StaticWordNormCloseClause, norm-close transport
  11 Q06StaticDiracNormClose         v3 StaticDiracNormCloseClause, norm-close transport
  12 Q06StaticPolyProduct            v3 StaticPolyProductClause, pair transport
  13 Q06StaticPolyProductNormClose   v3 StaticPolyProductNormCloseClause, norm-close transport
  14 Q06DynamicPolyProduct           v3 DynamicPolyProductClause instance

The static conjuncts are stated on the dynamic index `1+n`. The transport is along `castHN (Nat.add_comm n 1)`
(`eH` below), which carries the static operators `W^{q}_{n+1}` to the dynamic operators `W^{q}_{1+n}`
(`FullWickO4.static_dynamic_same_operator`, `FullWickO4.static_dynamic_same_adjoint`) and the static preparation
`UniformStaticR49b.product n u` to `HighMomentsOps.wvec (1+n) u` (`FullWickO4.castHN_wvec`).

The R-8362E5EB input at the Q06 gauge is `FullWickO3.rd8362_at_Q06`, supplied with its four inputs:
  HierarchyR7B122087Input  `RB7BindFinal.hierarchyInputR25m_unconditional`        (R-7B122087, accepted)
  RE679E41DInput           `ActualModelCorollaryR60a.actual_model`, second part   (R-E679E41D, accepted)
  DynftFullTorusInput      `TerraMultiFinalR94.full_torus_r47`                    (R-B2E70586, accepted)
  R300B8640Input           `TerraMultiFinalR94.chain_named_final`, first part     (R-300B8640, accepted)
The static predicate `UniformStatic` is discharged by `UniformStaticR49b.selected_uniform_static` (R-D2F4CE8F).
No gauge hypothesis and no `RD8362E5EBInput` hypothesis remain.

Standard dependencies only (audit at the end of the file).
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section

open Filter Topology
open scoped ComplexConjugate

namespace QuantumNLS.FullWickFinalH15

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH7 (IsNormClosePrepT)
open QuantumNLS.FullWickO1 (staticGauge)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.WickSymbols (Sym Balanced)
open QuantumNLS.WickBounds (gensym wordSym labelsOf)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (Preparation TimeBox flows RD8362E5EBInput)
open QuantumNLS.FullWickS1 (orderedWord)
open Def033HierarchyR24m (Smooth physical)

/-! ### Generic transport along a family of isometric identifications -/

section Transport

variable {H H' : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
  [∀ N, NormedAddCommGroup (H' N)] [∀ N, NormedSpace ℂ (H' N)]

theorem strong_transport {X Θ : Type*} (e : ∀ N, H N ≃ₗᵢ[ℂ] H' N)
    {A : ∀ N, H N →L[ℂ] H N} {A' : ∀ N, H' N →L[ℂ] H' N}
    (hA : ∀ N (x : H N), A' N (e N x) = e N (A N x))
    {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N} {ψ' : X → Θ → ∀ N, H' N} {a : X → Θ → ℂ}
    (hψ : ∀ u t N, e N (ψ u t N) = ψ' u t N) (h : HasUniformStrongT A S Tb ψ a) :
    HasUniformStrongT A' S Tb ψ' a := by
  intro ε hε
  filter_upwards [h ε hε] with N hN
  intro u hu t ht
  have key : (A' N - a u t • ContinuousLinearMap.id ℂ (H' N)) (ψ' u t N)
      = e N ((A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)) := by
    rw [← hψ u t N]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_sub, map_smul, hA]
  rw [key, LinearIsometryEquiv.norm_map]
  exact hN u hu t ht

theorem pair_transport {X Θ : Type*} (e : ∀ N, H N ≃ₗᵢ[ℂ] H' N)
    {A A₂ : ∀ N, H N →L[ℂ] H N} {B B₂ : ∀ N, H' N →L[ℂ] H' N}
    (hA : ∀ N (x : H N), B N (e N x) = e N (A N x))
    (hA₂ : ∀ N (x : H N), B₂ N (e N x) = e N (A₂ N x))
    {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N} {ψ' : X → Θ → ∀ N, H' N} {a : X → Θ → ℂ}
    (hψ : ∀ u t N, e N (ψ u t N) = ψ' u t N) (h : HasUniformPairT A A₂ S Tb ψ a) :
    HasUniformPairT B B₂ S Tb ψ' a :=
  ⟨strong_transport e hA hψ h.1, strong_transport e hA₂ hψ h.2⟩

theorem normClose_transport {X Θ : Type*} (e : ∀ N, H N ≃ₗᵢ[ℂ] H' N)
    {ψ φ : X → Θ → ∀ N, H N} {ψ' φ' : X → Θ → ∀ N, H' N} {S : Set X} {Tb : Set Θ}
    (hψ : ∀ u t N, e N (ψ u t N) = ψ' u t N) (hφ : ∀ u t N, e N (φ u t N) = φ' u t N)
    (h : IsNormClosePrepT ψ φ S Tb) : IsNormClosePrepT ψ' φ' S Tb := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun u hu t ht N => ?_, fun ε hε => ?_⟩
  · rw [← hψ u t N, LinearIsometryEquiv.norm_map]
    exact h1 u hu t ht N
  · filter_upwards [h2 ε hε] with N hN
    intro u hu t ht
    rw [← hψ u t N, ← hφ u t N, ← map_sub (e N), LinearIsometryEquiv.norm_map]
    exact hN u hu t ht

end Transport

/-- Products of operators along an isometric identification. -/
theorem list_prod_intertwine {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F)
    (A : ι → E →L[ℂ] E) (A' : ι → F →L[ℂ] F) (hA : ∀ i (x : E), A' i (e x) = e (A i x))
    (l : List ι) (x : E) : (l.map A').prod (e x) = e ((l.map A).prod x) := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply, hA, ih]

/-- The reversed product, through `List.reverse`. -/
theorem list_rev_prod_intertwine {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F)
    (A : ι → E →L[ℂ] E) (A' : ι → F →L[ℂ] F) (hA : ∀ i (x : E), A' i (e x) = e (A i x))
    (l : List ι) (x : E) : ((l.map A').reverse).prod (e x) = e (((l.map A).reverse).prod x) := by
  have h := list_prod_intertwine e A A' hA l.reverse x
  simpa using h

/-! ### The identification of the static and dynamic index -/

/-- The cast `HN L (N+1) ≃ HN L (1+N)` along `N+1 = 1+N`. -/
def eH (L : ℝ) [Fact (0 < L)] (N : ℕ) : HN L (N + 1) ≃ₗᵢ[ℂ] HN L (1 + N) :=
  FullWickO4.castHN (L := L) (Nat.add_comm N 1)

theorem eH_wvec (L : ℝ) [Fact (0 < L)] (N : ℕ) (u : L2T L) :
    eH L N (HighMomentsOps.wvec (N + 1) u) = HighMomentsOps.wvec (1 + N) u :=
  FullWickO4.castHN_wvec (L := L) (Nat.add_comm N 1) u

theorem eH_symm_wvec (L : ℝ) [Fact (0 < L)] (N : ℕ) (u : L2T L) :
    (eH L N).symm (HighMomentsOps.wvec (1 + N) u) = HighMomentsOps.wvec (N + 1) u := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  exact (eH_wvec L N u).symm

theorem quant_eH (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (G : Gauge) (f : Sym) (N : ℕ)
    (x : HN L (N + 1)) :
    BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ N) G f (eH L N x)
      = eH L N (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ N) G f x) :=
  FullWickO4.static_dynamic_same_operator hκ G f N x

theorem quant_eH_adj (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (G : Gauge) (f : Sym) (N : ℕ)
    (x : HN L (N + 1)) :
    (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ N) G f).adjoint (eH L N x)
      = eH L N ((BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ N) G f).adjoint x) :=
  FullWickO4.static_dynamic_same_adjoint hκ G f N x

theorem orderedWord_eH (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (G : Gauge) (N : ℕ)
    (w : List (ℤ × ℤ)) (x : HN L (N + 1)) :
    orderedWord (ReconstructionR33m.basis (L := L) hκ N) G w (eH L N x)
      = eH L N (orderedWord (Def044D1SpectralR51a.basis (L := L) hκ N) G w x) := by
  unfold orderedWord
  exact list_prod_intertwine (ι := ℤ × ℤ) (eH L N) (fun p => BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ N) G (gensym p.1 p.2))
    (fun p => BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ N) G (gensym p.1 p.2))
    (fun p y => quant_eH L κ hκ G (gensym p.1 p.2) N y) w x

theorem orderedWord_rev_eH (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (G : Gauge) (N : ℕ)
    (w : List (ℤ × ℤ)) (x : HN L (N + 1)) :
    ((w.map fun p => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ N) G (gensym p.2 p.1)).reverse).prod (eH L N x)
      = eH L N (((w.map fun p => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ N) G (gensym p.2 p.1)).reverse).prod x) := by
  exact list_rev_prod_intertwine (ι := ℤ × ℤ) (eH L N)
    (fun p => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ N) G (gensym p.2 p.1))
    (fun p => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ N) G (gensym p.2 p.1))
    (fun p y => quant_eH L κ hκ G (gensym p.2 p.1) N y) w x

theorem poly_eH (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (G : Gauge) (N : ℕ) (fs : List Sym)
    (x : HN L (N + 1)) :
    (fs.map fun g => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ N) G g).prod (eH L N x)
      = eH L N ((fs.map fun g => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ N) G g).prod x) :=
  list_prod_intertwine (eH L N)
    (fun g => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ N) G g)
    (fun g => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ N) G g)
    (fun g y => quant_eH L κ hκ G g N y) fs x

theorem poly_adj_eH (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (G : Gauge) (N : ℕ) (fs : List Sym)
    (x : HN L (N + 1)) :
    ((fs.map fun g => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ N) G g).adjoint).reverse).prod (eH L N x)
      = eH L N (((fs.map fun g => (BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ N) G g).adjoint).reverse).prod x) :=
  list_rev_prod_intertwine (eH L N)
    (fun g => (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ N) G g).adjoint)
    (fun g => (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ N) G g).adjoint)
    (fun g y => quant_eH_adj L κ hκ G g N y) fs x

/-- The scaled Dirac commutator intertwines, with the scalars `-i(1+N)` (dynamic) and `-i(N+1)` (static). -/
theorem dirac_eH (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (G : Gauge) (f g : Sym) (N : ℕ)
    (x : HN L (N + 1)) :
    (-(Complex.I) * ((1 + N : ℕ) : ℂ)) •
        (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ N) G f
          * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ N) G g
          - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ N) G g
          * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ N) G f) (eH L N x)
      = eH L N ((-(Complex.I) * ((N + 1 : ℕ) : ℂ)) •
        (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ N) G f
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ N) G g
          - BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ N) G g
          * BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ N) G f) x) := by
  have hcN : ((1 + N : ℕ) : ℂ) = ((N + 1 : ℕ) : ℂ) := by rw [Nat.add_comm]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, quant_eH L κ hκ G f N, quant_eH L κ hκ G g N, map_sub, map_smul, hcN]

/-! ### The Q06 gauge, the hierarchy flows, and the four R-8362E5EB inputs -/

/-- The Q06 gauge: `staticGauge (sectorGauge hκ)`. -/
abbrev q06 (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Gauge :=
  staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)

/-- The hierarchy flows of R-7B122087 (accepted), at the unconditional hierarchy input. -/
abbrev q06Flows (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) :=
  flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)

/-- R-E679E41D, discharged by the accepted R60a actual-model theorem. -/
theorem re679_at (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) :
    TerraMultiRound88Input.RE679E41DInput hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ) := by
  intro u hu I R k Θ T hΘ hT
  exact (ActualModelCorollaryR60a.actual_model hκ u hu I R k Θ T hΘ hT).2

/-- The full-torus input, discharged by the accepted R94 final. -/
theorem fullTorus_at (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) :
    ∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ),
      DynSeedInputR47b.DynftFullTorusInput hκ (q06Flows L κ hκ) u R :=
  fun u hu R => TerraMultiFinalR94.full_torus_r47 hκ u hu R

/-- The seed input R-300B8640, discharged by the accepted R94 chain (named final). -/
theorem seed_at (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) :
    DynamicGaugeR34m.R300B8640Input hκ (q06Flows L κ hκ) := by
  intro u hu R lo hi a b hab _
  let C := ActualModelBindingR53a.chart (L := L) hκ
  have hC := ActualModelBindingR53a.printed_chart (L := L) hκ
  have h := (TerraMultiFinalR94.chain_named_final hκ C.Φ hC u hu R lo hi a b hab).1
  simpa only [DynSeedR47b.SeedStatement, DynSeedR47b.boxResidual,
    TerraMultiRound93Flow.selected_orbit_eq hκ C.Φ hC u R] using h

/-- R-8362E5EB at the Q06 gauge, from the four inputs above only (`FullWickO3.rd8362_at_Q06`). -/
theorem rd8362_Q06 (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) :
    RD8362E5EBInput hκ (q06Flows L κ hκ) (q06 L κ hκ) :=
  FullWickO3.rd8362_at_Q06 (L := L) hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)
    (re679_at L κ hκ) (fullTorus_at L κ hκ) (seed_at L κ hκ)

/-! ### The fourteen one-family conjuncts at the Q06 gauge (family `W_n = quantization (basis (1+n)) q06`) -/

/-- Conjunct 3: static strong symbol on `𝒰_R` (printed wick_calculus.tex:82-83). -/
def Q06Static (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) f)
      (fun n => (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n)
        (q06 L κ hκ) f).adjoint)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)

/-- Conjunct 4: uniformly norm-close preparations preserve the static strong symbol. -/
def Q06StaticNormClose (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
    ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (1 + n)},
      IsNormClosePrepT (H := fun n => HN L (1 + n)) ψ'
        (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))) (UR (L := L) R) Tb →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) f)
        (fun n => (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n)
          (q06 L κ hκ) f).adjoint)
        (UR (L := L) R) Tb ψ' (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)

/-- Conjunct 5: static scaled Dirac commutator, symbol `{f,g}(w(u))`. -/
def Q06StaticDirac (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f g : Sym}, Balanced f → Balanced g →
    ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf g ⊆ S →
      HasUniformStrongT (H := fun n => HN L (1 + n))
        (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
          (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) f
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g
            - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) f))
        (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (WickSymbols.pb S f g))

/-- Conjunct 6: static ordered products of generators, symbol `∏ z_{a_j} conj z_{b_j}`. -/
def Q06StaticWord (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ)),
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) w)
      (fun n => ((w.map fun p => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) (gensym p.2 p.1)).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w))

/-- Conjunct 7: dynamic strong symbol along every hierarchy trajectory, time box and norm-close preparation. -/
def Q06Dynamic (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ {f : Sym}, Balanced f →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) f)
        (fun n => (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n)
          (q06 L κ hκ) f).adjoint)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ (q06Flows L κ hκ) u R t : ℤ → ℂ)) f)

/-- Conjunct 8: dynamic scaled Dirac commutator. -/
def Q06DynamicDirac (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ {f h : Sym}, Balanced f → Balanced h →
      ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf h ⊆ S →
      HasUniformStrongT (H := fun n => HN L (1 + n))
        (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
          (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) f
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) h
            - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) h
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) f))
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          evalSym ((ReconstructionR33m.w hκ (q06Flows L κ hκ) u R t : ℤ → ℂ)) (WickSymbols.pb S f h))

/-- Conjunct 9: dynamic ordered products of generators. -/
def Q06DynamicWord (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ (w : List (ℤ × ℤ)),
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) w)
        (fun n => ((w.map fun p => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) (gensym p.2 p.1)).reverse).prod)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ (q06Flows L κ hκ) u R t : ℤ → ℂ)) (wordSym w))

/-- Conjunct 10: norm-close static ordered products. -/
def Q06StaticWordNormClose (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (w : List (ℤ × ℤ)) {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (1 + n)},
    IsNormClosePrepT (H := fun n => HN L (1 + n)) ψ'
      (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))) (UR (L := L) R) Tb →
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) w)
      (fun n => ((w.map fun p => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) (gensym p.2 p.1)).reverse).prod)
      (UR (L := L) R) Tb ψ'
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (wordSym w))

/-- Conjunct 11: norm-close static scaled Dirac commutator. -/
def Q06StaticDiracNormClose (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f g : Sym}, Balanced f → Balanced g →
    ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf g ⊆ S →
    ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (1 + n)},
      IsNormClosePrepT (H := fun n => HN L (1 + n)) ψ'
        (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))) (UR (L := L) R) Tb →
      HasUniformStrongT (H := fun n => HN L (1 + n))
        (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
          (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) f
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g
            - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g
            * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) f))
        (UR (L := L) R) Tb ψ'
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) (WickSymbols.pb S f g))

/-- Conjunct 12: static ordered products of balanced polynomials on `𝒰_R`. -/
def Q06StaticPolyProduct (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (fs : List Sym), (∀ g ∈ fs, Balanced g) →
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (fs.map fun g => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g).prod)
      (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g).adjoint).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (fun (u : L2T L) (_ : Θ) => (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod)

/-- Conjunct 13: norm-close static ordered products of balanced polynomials. -/
def Q06StaticPolyProductNormClose (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (fs : List Sym), (∀ g ∈ fs, Balanced g) →
    ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (1 + n)},
      IsNormClosePrepT (H := fun n => HN L (1 + n)) ψ'
        (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n))) (UR (L := L) R) Tb →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => (fs.map fun g => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g).prod)
        (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g).adjoint).reverse).prod)
        (UR (L := L) R) Tb ψ'
        (fun (u : L2T L) (_ : Θ) => (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod)

/-- Conjunct 14: dynamic ordered products of balanced polynomials along hierarchy trajectories. -/
def Q06DynamicPolyProduct (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ (fs : List Sym), (∀ g ∈ fs, Balanced g) →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => (fs.map fun g => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g).prod)
        (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (q06 L κ hκ) g).adjoint).reverse).prod)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          (fs.map fun g => evalSym ((ReconstructionR33m.w hκ (q06Flows L κ hκ) u R t : ℤ → ℂ)) g).prod)

/-! ### The headline: the printed theorem at the Q06 gauge, one family, printed hypotheses only -/

/-- **The printed theorem `thm:full-wick` (R-140AE34B) at the Q06 gauge, as one operator family.** No named theorem
input: the R-D2F4CE8F predicate is discharged by `UniformStaticR49b.selected_uniform_static`, and the R-8362E5EB input
by `FullWickO3.rd8362_at_Q06` from the accepted finals (see the module comment). -/
theorem thm_full_wick_Q06_final (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) :
    FullWickH10.Stage1Clause L ∧ FullWickH10.Stage2Clause L ∧ Q06Static L κ hκ
      ∧ Q06StaticNormClose L κ hκ ∧ Q06StaticDirac L κ hκ ∧ Q06StaticWord L κ hκ
      ∧ Q06Dynamic L κ hκ ∧ Q06DynamicDirac L κ hκ ∧ Q06DynamicWord L κ hκ
      ∧ Q06StaticWordNormClose L κ hκ ∧ Q06StaticDiracNormClose L κ hκ
      ∧ Q06StaticPolyProduct L κ hκ ∧ Q06StaticPolyProductNormClose L κ hκ
      ∧ Q06DynamicPolyProduct L κ hκ := by
  obtain ⟨v1, v2, -, -, v5, v6, v7, -, -, -, v11, v12, v13, v14, v15⟩ :=
    FullWickH14.thm_full_wick_printed_v3 L κ hκ
  obtain ⟨o1, o2, o3, o4⟩ :=
    FullWickO4.full_wick_Q06_one_family (L := L) hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)
      (re679_at L κ hκ) (fullTorus_at L κ hκ) (seed_at L κ hκ)
  have sel := UniformStaticR49b.selected_uniform_static (L := L) hκ
  refine ⟨v1, v2, o1, ?_, ?_, ?_, o2, o3, o4, ?_, ?_, ?_, ?_, ?_⟩
  · -- Conjunct 4: norm-close static strong symbol.
    intro Θ Tb R f hf ψd hprep
    have hs : IsNormClosePrepT (H := fun n => HN L (n + 1))
        (fun (u : L2T L) (t : Θ) N => (eH L N).symm (ψd u t N))
        (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb :=
      normClose_transport (fun N => (eH L N).symm) (fun _ _ _ => rfl)
        (fun u t N => eH_symm_wvec L N u) hprep
    have hc := v5 sel Tb R hf hs
    exact pair_transport (fun N => eH L N)
      (fun N x => quant_eH L κ hκ (q06 L κ hκ) f N x)
      (fun N x => quant_eH_adj L κ hκ (q06 L κ hκ) f N x)
      (fun u t N => (eH L N).apply_symm_apply (ψd u t N)) hc
  · -- Conjunct 5: static scaled Dirac commutator.
    intro Θ Tb R f g hf hg S hSf hSg
    have hc := v6 sel Tb R hf hg hSf hSg
    exact strong_transport (fun N => eH L N)
      (fun N x => dirac_eH L κ hκ (q06 L κ hκ) f g N x)
      (fun u t N => eH_wvec L N u) hc
  · -- Conjunct 6: static ordered products of generators.
    intro Θ Tb R w
    exact pair_transport (fun N => eH L N)
      (fun N x => orderedWord_eH L κ hκ (q06 L κ hκ) N w x)
      (fun N x => orderedWord_rev_eH L κ hκ (q06 L κ hκ) N w x)
      (fun u t N => eH_wvec L N u) (v7 sel Tb R w)
  · -- Conjunct 10: norm-close static ordered products.
    intro Θ Tb R w ψd hprep
    have hs : IsNormClosePrepT (H := fun n => HN L (n + 1))
        (fun (u : L2T L) (t : Θ) N => (eH L N).symm (ψd u t N))
        (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb :=
      normClose_transport (fun N => (eH L N).symm) (fun _ _ _ => rfl)
        (fun u t N => eH_symm_wvec L N u) hprep
    have hc := v11 sel Tb R w hs
    exact pair_transport (fun N => eH L N)
      (fun N x => orderedWord_eH L κ hκ (q06 L κ hκ) N w x)
      (fun N x => orderedWord_rev_eH L κ hκ (q06 L κ hκ) N w x)
      (fun u t N => (eH L N).apply_symm_apply (ψd u t N)) hc
  · -- Conjunct 11: norm-close static scaled Dirac commutator.
    intro Θ Tb R f g hf hg S hSf hSg ψd hprep
    have hs : IsNormClosePrepT (H := fun n => HN L (n + 1))
        (fun (u : L2T L) (t : Θ) N => (eH L N).symm (ψd u t N))
        (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb :=
      normClose_transport (fun N => (eH L N).symm) (fun _ _ _ => rfl)
        (fun u t N => eH_symm_wvec L N u) hprep
    have hc := v12 sel Tb R hf hg hSf hSg hs
    exact strong_transport (fun N => eH L N)
      (fun N x => dirac_eH L κ hκ (q06 L κ hκ) f g N x)
      (fun u t N => (eH L N).apply_symm_apply (ψd u t N)) hc
  · -- Conjunct 12: static ordered products of balanced polynomials.
    intro Θ Tb R fs hfs
    exact pair_transport (fun N => eH L N)
      (fun N x => poly_eH L κ hκ (q06 L κ hκ) N fs x)
      (fun N x => poly_adj_eH L κ hκ (q06 L κ hκ) N fs x)
      (fun u t N => eH_wvec L N u) (v13 sel Tb R fs hfs)
  · -- Conjunct 13: norm-close static ordered products of balanced polynomials.
    intro Θ Tb R fs hfs ψd hprep
    have hs : IsNormClosePrepT (H := fun n => HN L (n + 1))
        (fun (u : L2T L) (t : Θ) N => (eH L N).symm (ψd u t N))
        (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb :=
      normClose_transport (fun N => (eH L N).symm) (fun _ _ _ => rfl)
        (fun u t N => eH_symm_wvec L N u) hprep
    have hc := v14 sel Tb R fs hfs hs
    exact pair_transport (fun N => eH L N)
      (fun N x => poly_eH L κ hκ (q06 L κ hκ) N fs x)
      (fun N x => poly_adj_eH L κ hκ (q06 L κ hκ) N fs x)
      (fun u t N => (eH L N).apply_symm_apply (ψd u t N)) hc
  · -- Conjunct 14: dynamic ordered products, the v3 dynamic polynomial clause at the Q06 gauge.
    exact v15 (q06Flows L κ hκ) (q06 L κ hκ) (rd8362_Q06 L κ hκ)

/-! ### Type comparison: the one-family conjuncts against the v3 headline conjuncts instantiated

Each check below typechecks a v3 conjunct, instantiated at the flows `q06Flows`, the gauge `q06`, and the
R-8362E5EB input `rd8362_Q06`, at the declared Prop of the corresponding one-family conjunct. The static conjuncts
are not checked this way (the index `n+1` of v3 differs from `1+n`); they are the transport proofs above. -/

theorem cmp_dynamic_v3 (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Q06Dynamic L κ hκ :=
  (FullWickH14.thm_full_wick_printed_v3 L κ hκ).2.2.2.2.2.2.2.1 (q06Flows L κ hκ) (q06 L κ hκ) (rd8362_Q06 L κ hκ)

theorem cmp_dynamic_dirac_v3 (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Q06DynamicDirac L κ hκ :=
  (FullWickH14.thm_full_wick_printed_v3 L κ hκ).2.2.2.2.2.2.2.2.1 (q06Flows L κ hκ) (q06 L κ hκ) (rd8362_Q06 L κ hκ)

theorem cmp_dynamic_word_v3 (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Q06DynamicWord L κ hκ :=
  (FullWickH14.thm_full_wick_printed_v3 L κ hκ).2.2.2.2.2.2.2.2.2.1 (q06Flows L κ hκ) (q06 L κ hκ)
    (rd8362_Q06 L κ hκ)

theorem cmp_dynamic_polyproduct_v3 (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) : Q06DynamicPolyProduct L κ hκ :=
  (FullWickH14.thm_full_wick_printed_v3 L κ hκ).2.2.2.2.2.2.2.2.2.2.2.2.2.2 (q06Flows L κ hκ) (q06 L κ hκ)
    (rd8362_Q06 L κ hκ)

end QuantumNLS.FullWickFinalH15

#print axioms QuantumNLS.FullWickFinalH15.thm_full_wick_Q06_final
#print axioms QuantumNLS.FullWickFinalH15.cmp_dynamic_v3
#print axioms QuantumNLS.FullWickFinalH15.cmp_dynamic_dirac_v3
#print axioms QuantumNLS.FullWickFinalH15.cmp_dynamic_word_v3
#print axioms QuantumNLS.FullWickFinalH15.cmp_dynamic_polyproduct_v3
#print axioms QuantumNLS.FullWickFinalH15.rd8362_Q06

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickFinalH15." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickFinalH15." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          name.components.any (fun c => c.toString == "RegularCut") ||
          name == ``QuantumNLS.UniformStaticR31m.GaugeRetargetingRD51987CAInput ||
          name == ``QuantumNLS.UniformStaticR31m.uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.retarget_and_uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.uniform_static_intermediate ||
          name == ``QuantumNLS.DynamicGaugeR34m.dynamic_gauge_ofInput ||
          name == ``QuantumNLS.DynamicGaugeR34m.dynamic_gauge_successor_ofInput then
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
  Lean.logInfo m!"FullWickFinalH15 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
