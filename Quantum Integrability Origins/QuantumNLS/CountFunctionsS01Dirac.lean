import QuantumNLS.CountFunctionsS01Engine
import QuantumNLS.CountFunctionsS01Words

/-!
# CountFunctionsS01Dirac: eq:dirac-main for the first-order class (dynamic and static instantiations)

PRINTED STATEMENT `source-text/chapters/principal_correspondence.tex:44-51` (sha256 `6008c7e6…da56`):
```
Every fixed ordered word in these bounded observables, their adjoints, and continuous functions of finitely many
intensive counts has the product of the corresponding scalar symbols, in the same strong and compact-time-uniform
sense. In particular, its expectation converges. For finite expressions made from the Cartesian transfers and C²
functions of finitely many counts, with classical expressions A,C,
  sup_{t∈K} ‖( N/i [A_N,C_N] - {A,C}(Φ_t(u)) ) U_N(t) ψ_N ‖ → 0,    sup_N ‖N[A_N,C_N]‖ < ∞.        (eq:dirac-main)
The precise C² class and regularized relative phases are given in Section algebra.
```
and `source-text/chapters/core/canonical_algebra.tex:38-57` (the first-order class, eq:finite-difference, eq:words and
the regularized relative phases `E^q_{N,ab} f(B_{N,J})`, which belong to the class: `f(x) = χ_a(x_a)χ_b(x_b)/√(x_a x_b)`
extended by zero near the excluded faces is smooth).

`dynamic_dirac`: for every `A, C : Expr J` (finite sums, products, scalar multiples and adjoints of the Cartesian
transfers `E^q_{N,ab}`, `a,b ∈ J`, and of `f(B_{N,J})`, `f` `C²` on a neighborhood of `[0,1]^J`), every norm-close
preparation, every compact box and the gauge of the R-8362E5EB input: `‖(N/i)[A_N,C_N]‖` is bounded uniformly in `N`
and `(N/i)[A_N,C_N] - {A,C}(Φ_t(u))` tends to zero strongly, uniformly on the box, along `U_N(t) ψ_N`.
`dynamic_expr_pair`: every expression has the strong symbol `A(Φ_t(u))` (and its adjoint the conjugate).
`static_dirac`, `static_expr_pair`: the same, uniformly on `𝒰_R`, at the gauge of the static input.
No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace
open QuantumNLS CountFunctionsS01Ops CountFunctionsS01Calc CountFunctionsS01Poisson CountFunctionsS01Class
open QuantumNLS.CountFunctionsS01Engine
open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.BetheCoefficientTransform (HN BetheBasis)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.UniformStaticR49b (UniformStatic)

namespace QuantumNLS.CountFunctionsS01Dirac

variable {L κ : ℝ} [Fact (0 < L)]

/-- The restriction of a coordinate vector to the label set `J`. -/
def res (J : Finset ℤ) (w : ℤ → ℂ) : CPt J := fun j => w (j : ℤ)

lemma norm_sc_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ) (X : E →L[ℂ] E) :
    ‖(-Complex.I * (N : ℂ)) • X‖ = ‖(N : ℂ) • X‖ := by
  rw [norm_smul, norm_smul]
  simp

/-! ### Dynamic setting -/

/-- The dynamic setting of the R-8362E5EB input: sector `N = 1 + n`, the physical basis `ReconstructionR33m.basis`, the
gauge `G`, the preparations `U_N(t) ψ_N` on the compact box, and the classical points `w(Φ_t(u))|_J`. -/
def dynSetting (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (J : Finset ℤ) :
    Setting L Unit (ℕ → ℝ) J where
  Nn := fun n => 1 + n
  hN := fun n => by omega
  hNtop := Filter.tendsto_atTop_mono (fun n => Nat.le_add_left n 1) Filter.tendsto_id
  b := fun n => ReconstructionR33m.basis (L := L) hκ n
  g := G
  S := Set.univ
  Tb := TimeBox R lo hi
  ψ := fun _ t n => ReconstructionR33m.U (L := L) hκ R t n (ψ n)
  z := fun _ t => res J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ)
  hψ := Eventually.of_forall fun n _ _ t _ => FullWickH9.dyn_prep_norm hκ hψ R n t
  hgen := fun a c => FullWickH5.generator_pair hκ F G D u hu R lo hi ψ hψ a c

theorem dynSetting_Nn (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (J : Finset ℤ) (n : ℕ) :
    (dynSetting hκ F G D u hu R lo hi ψ hψ J).Nn n = 1 + n := rfl

/-- **Strong symbol of every expression of the first-order class** (dynamic). -/
theorem dynamic_expr_pair (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) {J : Finset ℤ} (A : Expr J) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => A.op (ReconstructionR33m.basis (L := L) hκ n) G)
      (fun n => (A.op (ReconstructionR33m.basis (L := L) hκ n) G).adjoint)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) => A.cl (res J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ))) := by
  have h := (pairOK (dynSetting hκ F G D u hu R lo hi ψ hψ J) (A.nf false)).2
  have e1 : (fun n => (A.nf false).op (ReconstructionR33m.basis (L := L) hκ n) G) =
      fun n => A.op (ReconstructionR33m.basis (L := L) hκ n) G :=
    funext fun n => by simpa using Expr.op_nf (ReconstructionR33m.basis (L := L) hκ n) G false A
  have e2 : (fun n => ((A.nf false).op (ReconstructionR33m.basis (L := L) hκ n) G).adjoint) =
      fun n => (A.op (ReconstructionR33m.basis (L := L) hκ n) G).adjoint :=
    funext fun n => by rw [show (A.nf false).op (ReconstructionR33m.basis (L := L) hκ n) G =
      A.op (ReconstructionR33m.basis (L := L) hκ n) G from by
        simpa using Expr.op_nf (ReconstructionR33m.basis (L := L) hκ n) G false A]
  have e3 : (fun (_ : Unit) (t : ℕ → ℝ) => (A.nf false).cl (res J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ))) =
      fun (_ : Unit) (t : ℕ → ℝ) => A.cl (res J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) := by
    funext _ t
    simpa using Expr.cl_nf false A (res J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ))
  exact (e3 ▸ e2 ▸ e1 ▸ h : _)

/-- **eq:dirac-main for the first-order class** (dynamic; printed `principal_correspondence.tex:44-51`). -/
theorem dynamic_dirac (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) {J : Finset ℤ} (A C : Expr J) :
    HasUniformStrongT (H := fun n => HN L (1 + n))
      (fun n => (-Complex.I * ((1 + n : ℕ) : ℂ)) •
        (A.op (ReconstructionR33m.basis (L := L) hκ n) G * C.op (ReconstructionR33m.basis (L := L) hκ n) G -
          C.op (ReconstructionR33m.basis (L := L) hκ n) G * A.op (ReconstructionR33m.basis (L := L) hκ n) G))
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        poisson A.cl C.cl (res J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ))) ∧
    ∃ M : ℝ, ∀ n : ℕ,
      ‖((1 + n : ℕ) : ℂ) •
        (A.op (ReconstructionR33m.basis (L := L) hκ n) G * C.op (ReconstructionR33m.basis (L := L) hκ n) G -
          C.op (ReconstructionR33m.basis (L := L) hκ n) G * A.op (ReconstructionR33m.basis (L := L) hκ n) G)‖ ≤ M := by
  have h := diracOK_all (dynSetting hκ F G D u hu R lo hi ψ hψ J) (A.nf false) (C.nf false)
  obtain ⟨⟨M, hM, hb⟩, hs⟩ := h
  have eA : ∀ n, (A.nf false).op (ReconstructionR33m.basis (L := L) hκ n) G =
      A.op (ReconstructionR33m.basis (L := L) hκ n) G := fun n => by
    simpa using Expr.op_nf (ReconstructionR33m.basis (L := L) hκ n) G false A
  have eC : ∀ n, (C.nf false).op (ReconstructionR33m.basis (L := L) hκ n) G =
      C.op (ReconstructionR33m.basis (L := L) hκ n) G := fun n => by
    simpa using Expr.op_nf (ReconstructionR33m.basis (L := L) hκ n) G false C
  have eop : ∀ n, (dynSetting hκ F G D u hu R lo hi ψ hψ J).dirOp (A.nf false) (C.nf false) n =
      (-Complex.I * ((1 + n : ℕ) : ℂ)) •
        (A.op (ReconstructionR33m.basis (L := L) hκ n) G * C.op (ReconstructionR33m.basis (L := L) hκ n) G -
          C.op (ReconstructionR33m.basis (L := L) hκ n) G * A.op (ReconstructionR33m.basis (L := L) hκ n) G) :=
    fun n => by
      unfold Setting.dirOp Setting.sc
      change (-Complex.I * ((1 + n : ℕ) : ℂ)) •
        ((A.nf false).op (ReconstructionR33m.basis (L := L) hκ n) G *
            (C.nf false).op (ReconstructionR33m.basis (L := L) hκ n) G -
          (C.nf false).op (ReconstructionR33m.basis (L := L) hκ n) G *
            (A.nf false).op (ReconstructionR33m.basis (L := L) hκ n) G) = _
      rw [eA n, eC n]
  have ecl : ∀ (F' : CPt J → ℂ), True → True := fun _ _ => trivial
  have eA' : (A.nf false).cl = A.cl := funext fun z => by simpa using Expr.cl_nf false A z
  have eC' : (C.nf false).cl = C.cl := funext fun z => by simpa using Expr.cl_nf false C z
  refine ⟨?_, ⟨M, fun n => ?_⟩⟩
  · have e : (fun n => (dynSetting hκ F G D u hu R lo hi ψ hψ J).dirOp (A.nf false) (C.nf false) n) =
        fun n => (-Complex.I * ((1 + n : ℕ) : ℂ)) •
        (A.op (ReconstructionR33m.basis (L := L) hκ n) G * C.op (ReconstructionR33m.basis (L := L) hκ n) G -
          C.op (ReconstructionR33m.basis (L := L) hκ n) G * A.op (ReconstructionR33m.basis (L := L) hκ n) G) :=
      funext eop
    have hs' : HasUniformStrongT (H := fun n => HN L (1 + n))
        (fun n => (dynSetting hκ F G D u hu R lo hi ψ hψ J).dirOp (A.nf false) (C.nf false) n)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          poisson (A.nf false).cl (C.nf false).cl (res J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ))) := hs
    rw [e, eA', eC'] at hs'
    exact hs'
  · have h1 := hb n
    rw [eop n] at h1
    rw [← norm_sc_smul]
    exact h1


/-! ### Static setting -/

/-- The static setting of the R-D2F4CE8F input: sector `N = n + 1`, the basis `Def044D1SpectralR51a.basis`, the gauge
`staticGauge q`, the product preparations `u^{⊗N}` for `u ∈ 𝒰_R`, and the classical points `w(u)|_J`. -/
def statSetting (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (J : Finset ℤ) :
    Setting L (L2T L) Θ J where
  Nn := fun n => n + 1
  hN := fun n => Nat.succ_pos n
  hNtop := Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  b := fun n => Def044D1SpectralR51a.basis (L := L) hκ n
  g := FullWickO1.staticGauge q
  S := UR (L := L) R
  Tb := Tb
  ψ := fun u _ n => UniformStaticR49b.product n u
  z := fun u _ => res J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ)
  hψ := Eventually.of_forall fun n u hu _ _ => FullWickO2.norm_product n u hu.1
  hgen := fun a c => by
    have h := CountFunctionsS01Words.stat_letter_pair hκ hU Tb R (.cart (a : ℤ) (c : ℤ)) trivial
    have e : ∀ n, UniformStaticR49b.E (L := L) hκ q n ((a : ℤ), (c : ℤ)) =
        CartesianOccupationTransfer.physical (Def044D1SpectralR51a.basis (L := L) hκ n)
          (FullWickO1.staticGauge q) (a : ℤ) (c : ℤ) :=
      fun n => UniformStaticBridgeR50b.cartesian_eq_projective_physical hκ q n ((a : ℤ), (c : ℤ))
    simp only [CountFunctionsS01Words.statOp, CountFunctionsS01Words.baseSym, e] at h
    exact h

/-- Strong symbol of every expression of the first-order class (static, uniform on `𝒰_R`). -/
theorem static_expr_pair (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) {J : Finset ℤ} (A : Expr J) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q))
      (fun n => (A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q)).adjoint)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) =>
        A.cl (res J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ))) := by
  have h : HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => (A.nf false).op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q))
      (fun n => ((A.nf false).op (Def044D1SpectralR51a.basis (L := L) hκ n)
        (FullWickO1.staticGauge q)).adjoint)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) =>
        (A.nf false).cl (res J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ))) :=
    (pairOK (statSetting hκ hU Tb R J) (A.nf false)).2
  have e1 : ∀ n, (A.nf false).op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) =
      A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) := fun n => by
    simpa using Expr.op_nf (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) false A
  have e3 : (A.nf false).cl = A.cl := funext fun z => by simpa using Expr.cl_nf false A z
  simp only [e1, e3] at h
  exact h

/-- **eq:dirac-main for the first-order class, static form** (uniform on `𝒰_R`, gauge `staticGauge q`). -/
theorem static_dirac (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) {J : Finset ℤ} (A C : Expr J) :
    HasUniformStrongT (H := fun n => HN L (n + 1))
      (fun n => (-Complex.I * ((n + 1 : ℕ) : ℂ)) •
        (A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) -
          C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q)))
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) =>
        poisson A.cl C.cl (res J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ))) ∧
    ∃ M : ℝ, ∀ n : ℕ,
      ‖((n + 1 : ℕ) : ℂ) •
        (A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) -
          C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q))‖ ≤ M := by
  have h := diracOK_all (statSetting hκ hU Tb R J) (A.nf false) (C.nf false)
  obtain ⟨⟨M, hM, hb⟩, hs⟩ := h
  have eA : ∀ n, (A.nf false).op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) =
      A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) := fun n => by
    simpa using Expr.op_nf (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) false A
  have eC : ∀ n, (C.nf false).op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) =
      C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) := fun n => by
    simpa using Expr.op_nf (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) false C
  have eop : ∀ n, (statSetting hκ hU Tb R J).dirOp (A.nf false) (C.nf false) n =
      (-Complex.I * ((n + 1 : ℕ) : ℂ)) •
        (A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) -
          C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q)) :=
    fun n => by
      unfold Setting.dirOp Setting.sc
      change (-Complex.I * ((n + 1 : ℕ) : ℂ)) •
        ((A.nf false).op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            (C.nf false).op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) -
          (C.nf false).op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            (A.nf false).op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q)) = _
      rw [eA n, eC n]
  have eA' : (A.nf false).cl = A.cl := funext fun z => by simpa using Expr.cl_nf false A z
  have eC' : (C.nf false).cl = C.cl := funext fun z => by simpa using Expr.cl_nf false C z
  refine ⟨?_, ⟨M, fun n => ?_⟩⟩
  · have e : (fun n => (statSetting hκ hU Tb R J).dirOp (A.nf false) (C.nf false) n) =
        fun n => (-Complex.I * ((n + 1 : ℕ) : ℂ)) •
        (A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) -
          C.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) *
            A.op (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q)) :=
      funext eop
    have hs' : HasUniformStrongT (H := fun n => HN L (n + 1))
        (fun n => (statSetting hκ hU Tb R J).dirOp (A.nf false) (C.nf false) n)
        (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
        (fun (u : L2T L) (_ : Θ) =>
          poisson (A.nf false).cl (C.nf false).cl (res J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ))) := hs
    rw [e, eA', eC'] at hs'
    exact hs'
  · have h1 := hb n
    rw [eop n] at h1
    rw [← norm_sc_smul]
    exact h1

end QuantumNLS.CountFunctionsS01Dirac
