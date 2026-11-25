import QuantumNLS.FullWickO3
import QuantumNLS.FullWickH10

/-! FullWickO4 (opus_tensor, R-140AE34B `thm:full-wick`, Gap 2 of the FullWickH10 assembly and the Q06
dynamic clause).

Gap 2 (basis index). The static clause uses `Def044D1SpectralR51a.basis hκ n : BetheBasis L (n+1)` and the
dynamic clauses use `ReconstructionR33m.basis hκ n : BetheBasis L (1+n)`. Both are
`UnconditionalBetheBasis.meanField_physicalBasis L _ _ hκ`; the only difference is the index `n+1` versus
`1+n`. Proved here:
* `meanField_heq`, `basis_heq`, `basis_cast`: the two bases agree up to the cast along `n+1 = 1+n`;
* `castHN h : HN L N ≃ₗᵢ[ℂ] HN L M` (the identity transported along `h : N = M`), and
  `quantization_castHN`, `quantization_adjoint_castHN`, `quantization_heq`: Wick quantization (DEF-032)
  commutes with that cast, for every gauge and symbol; `castHN_wvec`: the cast maps `u^{⊗N}` to `u^{⊗M}`;
* `static_pair_one_add`: the static clause of `FullWickH8.static_poly_pair`, re-indexed to the dynamic family
  `fun n => quantization (ReconstructionR33m.basis hκ n) (staticGauge q) f` on `HN L (1+n)`.

Q06 dynamic clause (Gap 1 closed by FullWickO3): `full_wick_Q06_one_family`, for the ONE operator family
`W^q_n(f) = quantization (ReconstructionR33m.basis hκ n) (staticGauge (sectorGauge hκ)) f`:
static uniform strong symbols on `𝒰_R`, dynamic strong symbols along hierarchy trajectories (every norm-close
preparation, every compact joint-time box), dynamic scaled Dirac commutator and dynamic ordered products.
Hypotheses: the remaining R-8362E5EB inputs only (`HierarchyR7B122087Input`, `RE679E41DInput`,
`DynftFullTorusInput`, `R300B8640Input`), i.e. binders 6-9 of the frozen `DynamicGaugeR34m.dynamic_gauge_ofInput`.
No gauge hypothesis and no `RD8362E5EBInput` hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Filter Topology
open scoped ComplexConjugate

namespace QuantumNLS.FullWickO4

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickO1 (staticGauge)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.WickSymbols (Sym Balanced)
open QuantumNLS.WickBounds (gensym wordSym labelsOf)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox flows)
open QuantumNLS.FullWickS1 (orderedWord)
open Def033HierarchyR24m (Smooth physical)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ### Gap 2: the basis index cast -/

/-- The mean-field physical Bethe basis at two equal particle numbers. -/
theorem meanField_heq (hκ : 0 < κ) {N M : ℕ} (h : N = M) (hN : 1 ≤ N) (hM : 1 ≤ M) :
    HEq (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ)
      (UnconditionalBetheBasis.meanField_physicalBasis L M hM hκ) := by
  subst h; rfl

/-- **The static and dynamic bases are the same basis, up to `n+1 = 1+n`.** -/
theorem basis_heq (hκ : 0 < κ) (n : ℕ) :
    HEq (Def044D1SpectralR51a.basis (L := L) hκ n) (ReconstructionR33m.basis (L := L) hκ n) :=
  meanField_heq hκ (Nat.add_comm n 1) _ _

theorem basis_cast (hκ : 0 < κ) (n : ℕ) :
    cast (congrArg (BetheBasis L) (Nat.add_comm n 1)) (Def044D1SpectralR51a.basis (L := L) hκ n) =
      ReconstructionR33m.basis (L := L) hκ n :=
  cast_eq_iff_heq.2 (basis_heq hκ n)

/-- The identity of the physical sector, transported along `N = M`. -/
def castHN {N M : ℕ} (h : N = M) : HN L N ≃ₗᵢ[ℂ] HN L M :=
  h ▸ LinearIsometryEquiv.refl ℂ (HN L N)

theorem castHN_rfl (N : ℕ) (x : HN L N) : castHN (L := L) (rfl : N = N) x = x := rfl

theorem castHN_heq {N M : ℕ} (h : N = M) (x : HN L N) : HEq (castHN (L := L) h x) x := by
  subst h; rfl

/-- The cast maps the product vector `u^{⊗N}` to `u^{⊗M}`. -/
theorem castHN_wvec {N M : ℕ} (h : N = M) (u : L2T L) :
    castHN (L := L) h (HighMomentsOps.wvec N u) = HighMomentsOps.wvec M u := by
  subst h; rfl

/-- **Wick quantization commutes with the index cast**, for every basis pair related by the cast. -/
theorem quantization_castHN {N M : ℕ} (h : N = M) (b : BetheBasis L N) (b' : BetheBasis L M)
    (hb : HEq b b') (g : Gauge) (f : Sym) (x : HN L N) :
    BalancedWickDefinition.quantization b' g f (castHN h x) =
      castHN h (BalancedWickDefinition.quantization b g f x) := by
  subst h; cases hb; rfl

theorem quantization_adjoint_castHN {N M : ℕ} (h : N = M) (b : BetheBasis L N) (b' : BetheBasis L M)
    (hb : HEq b b') (g : Gauge) (f : Sym) (x : HN L N) :
    (BalancedWickDefinition.quantization b' g f).adjoint (castHN h x) =
      castHN h ((BalancedWickDefinition.quantization b g f).adjoint x) := by
  subst h; cases hb; rfl

theorem quantization_heq {N M : ℕ} (h : N = M) (b : BetheBasis L N) (b' : BetheBasis L M)
    (hb : HEq b b') (g : Gauge) (f : Sym) :
    HEq (BalancedWickDefinition.quantization b g f) (BalancedWickDefinition.quantization b' g f) := by
  subst h; cases hb; rfl

/-- **The static and dynamic `W^G_N(f)` are one operator**: at the bases of the two settings they agree
up to the index cast, for every gauge `G` and symbol `f`. -/
theorem static_dynamic_same_operator (hκ : 0 < κ) (G : Gauge) (f : Sym) (n : ℕ) (x : HN L (n+1)) :
    BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f
        (castHN (Nat.add_comm n 1) x) =
      castHN (Nat.add_comm n 1)
        (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) G f x) :=
  quantization_castHN _ _ _ (basis_heq hκ n) G f x

theorem static_dynamic_same_adjoint (hκ : 0 < κ) (G : Gauge) (f : Sym) (n : ℕ) (x : HN L (n+1)) :
    (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f).adjoint
        (castHN (Nat.add_comm n 1) x) =
      castHN (Nat.add_comm n 1)
        ((BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) G f).adjoint x) :=
  quantization_adjoint_castHN _ _ _ (basis_heq hκ n) G f x

theorem static_dynamic_heq (hκ : 0 < κ) (G : Gauge) (f : Sym) (n : ℕ) :
    HEq (BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n) G f)
      (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f) :=
  quantization_heq (Nat.add_comm n 1) _ _ (basis_heq hκ n) G f

/-! ### The static clause on the dynamic index -/

/-- The static pair statement, with the particle number given by an index function. -/
def StaticAt (hκ : 0 < κ) (G : Gauge) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (f : Sym)
    (particles : ℕ → ℕ) (pos : ∀ n, 1 ≤ particles n) : Prop :=
  HasUniformPairT (H := fun n => HN L (particles n))
    (fun n => BalancedWickDefinition.quantization
      (UnconditionalBetheBasis.meanField_physicalBasis L (particles n) (pos n) hκ) G f)
    (fun n => (BalancedWickDefinition.quantization
      (UnconditionalBetheBasis.meanField_physicalBasis L (particles n) (pos n) hκ) G f).adjoint)
    (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (particles n) u : HN L (particles n)))
    (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)

/-- **Static clause on the dynamic family**: for every static parameter pair `(j, q)` and balanced `f`,
`quantization (ReconstructionR33m.basis hκ n) (staticGauge q) f` on `HN L (1+n)` has the uniform strong symbol
`f(w(u))` on `𝒰_R` at `u^{⊗(1+n)}`, and its adjoint the conjugate. -/
theorem static_pair_one_add (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStaticR49b.UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) {f : Sym}
    (hf : Balanced f) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f)
      (fun n => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f).adjoint)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
      (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f) := by
  have h1 : StaticAt (L := L) hκ (staticGauge q) Tb R f (fun n => n+1) (fun n => by omega) :=
    FullWickH8.static_poly_pair hκ hU Tb R hf
  have he : (fun n : ℕ => n+1) = fun n => 1+n := funext (fun n => Nat.add_comm n 1)
  have hh : ∃ pos : ∀ n, 1 ≤ (fun n : ℕ => n+1) n,
      StaticAt (L := L) hκ (staticGauge q) Tb R f (fun n => n+1) pos := ⟨_, h1⟩
  rw [he] at hh
  obtain ⟨_, h⟩ := hh
  exact h

/-! ### The dynamic clauses at the static gauge, with no gauge hypothesis -/

/-- **Dynamic clause for `W^q` at every static parameter pair `(j, q)`**: the gauge is `staticGauge q`, the same
as in the static clause; the R-8362E5EB input is supplied by `FullWickO3.rd8362_at_staticGauge`. -/
theorem dynamic_clause_at_static (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (RE679E41DInput : TerraMultiRound88Input.RE679E41DInput hκ HierarchyR7B122087Input)
    (DynftFullTorusInput : ∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ),
      DynSeedInputR47b.DynftFullTorusInput hκ (flows hκ HierarchyR7B122087Input) u R)
    (R300B8640Input : DynamicGaugeR34m.R300B8640Input hκ (flows hκ HierarchyR7B122087Input))
    {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStaticR49b.UniformStatic (L := L) hκ j q) :
    ∀ (u : Smooth L), ‖physical u‖ = 1 →
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
          evalSym ((ReconstructionR33m.w hκ (flows hκ HierarchyR7B122087Input) u R t : ℤ → ℂ)) f) :=
  FullWickH10.dynamic_clause_at_Q06 L κ hκ q (flows hκ HierarchyR7B122087Input)
    (FullWickO3.rd8362_at_staticGauge hκ HierarchyR7B122087Input RE679E41DInput DynftFullTorusInput
      R300B8640Input hU)

/-- **The printed `thm:full-wick` Q06 statements for ONE operator family** `W^q_n(f) =
quantization (ReconstructionR33m.basis hκ n) (staticGauge q) f` on `HN L (1+n)`, `q = sectorGauge hκ`:
(1) static uniform strong symbols `f(w(u))` on every `𝒰_R` (and the adjoint, conjugate);
(2) dynamic strong symbols `f(w(u,t))` along every fixed smooth hierarchy trajectory, every compact joint-time
box, every norm-close preparation (and the adjoint, conjugate);
(3) the dynamic scaled Dirac commutator with symbol `{f,h}(w(u,t))`;
(4) dynamic fixed ordered products of generators with the product symbol.
Hypotheses: the remaining R-8362E5EB inputs only. -/
theorem full_wick_Q06_one_family (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (RE679E41DInput : TerraMultiRound88Input.RE679E41DInput hκ HierarchyR7B122087Input)
    (DynftFullTorusInput : ∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ),
      DynSeedInputR47b.DynftFullTorusInput hκ (flows hκ HierarchyR7B122087Input) u R)
    (R300B8640Input : DynamicGaugeR34m.R300B8640Input hκ (flows hκ HierarchyR7B122087Input)) :
    let q := RetargetSelectionR49b.sectorGauge (L := L) hκ
    let F := flows hκ HierarchyR7B122087Input
    (∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) {f : Sym}, Balanced f →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f)
        (fun n => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f).adjoint)
        (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => (HighMomentsOps.wvec (1 + n) u : HN L (1 + n)))
        (fun (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) f)) ∧
    (∀ (u : Smooth L), ‖physical u‖ = 1 →
      ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
      ∀ {f : Sym}, Balanced f →
        HasUniformPairT (H := fun n => HN L (1 + n))
          (fun n => BalancedWickDefinition.quantization
            (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f)
          (fun n => (BalancedWickDefinition.quantization
            (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f).adjoint)
          (Set.univ : Set Unit) (TimeBox R lo hi)
          (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
          (fun (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) f)) ∧
    (∀ (u : Smooth L), ‖physical u‖ = 1 →
      ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
      ∀ {f h : Sym}, Balanced f → Balanced h →
        ∀ {S : Finset ℤ}, labelsOf f ⊆ S → labelsOf h ⊆ S →
        HasUniformStrongT (H := fun n => HN L (1 + n))
          (fun n => (-(Complex.I) * ((1 + n : ℕ) : ℂ)) •
            (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f
              * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) h
              - BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) h
              * BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) f))
          (Set.univ : Set Unit) (TimeBox R lo hi)
          (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
          (fun (_ : Unit) (t : ℕ → ℝ) =>
            evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (WickSymbols.pb S f h))) ∧
    (∀ (u : Smooth L), ‖physical u‖ = 1 →
      ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
      ∀ (w : List (ℤ × ℤ)),
        HasUniformPairT (H := fun n => HN L (1 + n))
          (fun n => orderedWord (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) w)
          (fun n => ((w.map fun p => BalancedWickDefinition.quantization
            (ReconstructionR33m.basis (L := L) hκ n) (staticGauge q) (gensym p.2 p.1)).reverse).prod)
          (Set.univ : Set Unit) (TimeBox R lo hi)
          (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
          (fun (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) (wordSym w))) := by
  intro q F
  have hU := UniformStaticR49b.selected_uniform_static (L := L) hκ
  have D : RD8362E5EBInput hκ F (staticGauge q) :=
    FullWickO3.rd8362_at_Q06 hκ HierarchyR7B122087Input RE679E41DInput DynftFullTorusInput R300B8640Input
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Θ Tb R f hf
    exact static_pair_one_add hκ hU Tb R hf
  · intro u hu R lo hi ψ hψ f hf
    exact FullWickH10.dynamic_clause L κ hκ F (staticGauge q) D u hu R lo hi ψ hψ hf
  · intro u hu R lo hi ψ hψ f h hf hh S hSf hSh
    exact FullWickH10.dynamic_dirac_clause L κ hκ F (staticGauge q) D u hu R lo hi ψ hψ hf hh hSf hSh
  · intro u hu R lo hi ψ hψ w
    exact FullWickH10.dynamic_word_clause L κ hκ F (staticGauge q) D u hu R lo hi ψ hψ w

/-- the auxiliary construction's `FullWickH10.dynamic_clause_at_Q06` at `q = sectorGauge hκ`, with its input `D` discharged. -/
theorem dynamic_clause_at_Q06_discharged (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (RE679E41DInput : TerraMultiRound88Input.RE679E41DInput hκ HierarchyR7B122087Input)
    (DynftFullTorusInput : ∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ),
      DynSeedInputR47b.DynftFullTorusInput hκ (flows hκ HierarchyR7B122087Input) u R)
    (R300B8640Input : DynamicGaugeR34m.R300B8640Input hκ (flows hκ HierarchyR7B122087Input)) :
    ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ {f : Sym}, Balanced f →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n)
          (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) f)
        (fun n => (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n)
          (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) f).adjoint)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          evalSym ((ReconstructionR33m.w hκ (flows hκ HierarchyR7B122087Input) u R t : ℤ → ℂ)) f) :=
  FullWickH10.dynamic_clause_at_Q06 L κ hκ (RetargetSelectionR49b.sectorGauge (L := L) hκ)
    (flows hκ HierarchyR7B122087Input)
    (FullWickO3.rd8362_at_Q06 hκ HierarchyR7B122087Input RE679E41DInput DynftFullTorusInput R300B8640Input)

end QuantumNLS.FullWickO4

#print axioms QuantumNLS.FullWickO4.meanField_heq
#print axioms QuantumNLS.FullWickO4.basis_heq
#print axioms QuantumNLS.FullWickO4.basis_cast
#print axioms QuantumNLS.FullWickO4.castHN_wvec
#print axioms QuantumNLS.FullWickO4.quantization_castHN
#print axioms QuantumNLS.FullWickO4.quantization_adjoint_castHN
#print axioms QuantumNLS.FullWickO4.quantization_heq
#print axioms QuantumNLS.FullWickO4.static_dynamic_same_operator
#print axioms QuantumNLS.FullWickO4.static_dynamic_same_adjoint
#print axioms QuantumNLS.FullWickO4.static_dynamic_heq
#print axioms QuantumNLS.FullWickO4.static_pair_one_add
#print axioms QuantumNLS.FullWickO4.dynamic_clause_at_static
#print axioms QuantumNLS.FullWickO4.full_wick_Q06_one_family
#print axioms QuantumNLS.FullWickO4.dynamic_clause_at_Q06_discharged

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickO4." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickO4." then
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
  Lean.logInfo m!"FullWickO4 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
