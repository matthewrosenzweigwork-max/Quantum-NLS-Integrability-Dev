import QuantumNLS.EnergyContactCommutator

/-!
# Finite-rank operators with smooth kernel: the literal predicate and its normal form

Source: `source-text/chapters/energy_prepared/cubic_charge.tex:74` (ENERGY-002, `lem:A1-trace`):
"Let `J` be a finite-rank operator with smooth kernel on `k` variables."  The proof then says
"It suffices next to take `J = |f⟩⟨g|`, with `f, g` smooth on `𝕋_L^k`" and closes with "Finite sums
... give the remaining assertions".

Owner: opus_tensor.  Imports (read-only, frozen): review record's `EnergyContactCommutator`
(`bd41e27f`, consuming `EnergyContactTrace` `69f1e9d9`), and transitively `ProductWeakDerivatives`
(`IsTorusTest`, `liftK`, `rep`) and `BetheH1` (`continuous_liftK`).

Parts:
1. The literal predicate `IsFiniteRankSmoothKernel J` on the actual carrier `L²(𝕋_L^k)`:
   `J` is a bounded operator of finite rank (its range is finite-dimensional) and an integral
   operator `(Jψ)(x) = ∫_{𝕋_L^k} K(x,y) ψ(y) dy` (a.e. in `x`) with `K` a `C^∞` function of
   `(x,y) ∈ ℝ^k × ℝ^k` that is lattice-periodic in `x` and in `y` (a smooth function on
   `𝕋_L^k × 𝕋_L^k`).
2. Smooth periodic profiles form a subspace `testSub`; their `L²` classes give an injective linear
   map `clsL`.
3. Kernel analysis: Fubini, continuity of `y ↦ ⟨φ, K(·,y)⟩`, and the key fact that every kernel slice
   `K(·, y)` lies in the (closed, finite-dimensional) range of `J`.
4. The span of the slices is finite-dimensional; coordinate functionals are finite combinations of
   point evaluations; hence `K(x,y) = Σ_r f_r(x) \overline{g_r(y)}` everywhere with smooth periodic
   `f_r, g_r`.
5. Finite sums `Σ_r |f_r⟩⟨g_r|` are integral operators with the smooth kernel
   `Σ_r f_r(x) \overline{g_r(y)}` and have finite rank (the converse direction).
6. `isFiniteRankSmoothKernel_iff`: the literal predicate is equivalent to the normal form consumed by
   `energy002`.
7. `energy002_literal`: `energy002` quantified over every literal finite-rank smooth-kernel `J`.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate InnerProductSpace ContDiff
open MeasureTheory

namespace QuantumNLS.SmoothKernelNormalForm

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace QuantumNLS.Fourier
  QuantumNLS.CollisionIdentification QuantumNLS.PhysicalTensor QuantumNLS.EnergyContactTrace
  QuantumNLS.ProductWeakDerivatives QuantumNLS.EnergyContactCommutator

/-! ## Part 1: the literal predicate -/

section Predicate

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

variable (L) in
/-- `K` is a smooth (`C^∞`) lattice-periodic function of `(x, y) ∈ ℝ^k × ℝ^k`, i.e. a smooth
function on `𝕋_L^k × 𝕋_L^k`: jointly `C^∞` and invariant under `Lℤ^k` in each variable. -/
structure IsSmoothPeriodicKernel (K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × (Fin k → ℝ) => K p.1 p.2)
  periodic_left : ∀ y, LatticePeriodic L (fun x => K x y)
  periodic_right : ∀ x, LatticePeriodic L (K x)

/-- `J` is the integral operator with kernel `K` on `L²(𝕋_L^k)`:
`(Jψ)(x) = ∫_{𝕋_L^k} K(x,y) ψ(y) dy` for almost every `x`, for every `ψ ∈ L²(𝕋_L^k)`. -/
def IsIntegralOperator (J : L2TN L k →L[ℂ] L2TN L k) (K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ) : Prop :=
  ∀ ψ : L2TN L k, (J ψ : (Fin k → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L k]
    fun x => ∫ y, K (fun i => rep (x i)) (fun i => rep (y i)) * (ψ : (Fin k → AddCircle L) → ℂ) y
      ∂(torusPiMeasure L k)

/-- `J` has a smooth kernel on `k` variables. -/
def HasSmoothKernel (J : L2TN L k →L[ℂ] L2TN L k) : Prop :=
  ∃ K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ, IsSmoothPeriodicKernel L K ∧ IsIntegralOperator J K

/-- `J` has finite rank: its range is finite-dimensional. -/
def IsFiniteRank (J : L2TN L k →L[ℂ] L2TN L k) : Prop :=
  FiniteDimensional ℂ (LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k))

/-- **"A finite-rank operator with smooth kernel on `k` variables"** (`cubic_charge.tex:74`), on the
actual carrier `L²(𝕋_L^k)`. -/
def IsFiniteRankSmoothKernel (J : L2TN L k →L[ℂ] L2TN L k) : Prop :=
  IsFiniteRank J ∧ HasSmoothKernel J

end Predicate

/-! ## Part 2: smooth periodic profiles and their `L²` classes -/

section Profiles

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

variable (L k) in
/-- The subspace of smooth lattice-periodic profiles `ℝ^k → ℂ`. -/
def testSub : Submodule ℂ ((Fin k → ℝ) → ℂ) where
  carrier := {φ | IsTorusTest L φ}
  add_mem' := fun {a b} ha hb =>
    ⟨ha.smooth.add hb.smooth, fun x m => by
      simp only [Pi.add_apply, ha.periodic x m, hb.periodic x m]⟩
  zero_mem' := ⟨contDiff_const, fun _ _ => rfl⟩
  smul_mem' := fun c φ hφ =>
    ⟨hφ.smooth.const_smul c, fun x m => by simp only [Pi.smul_apply, hφ.periodic x m]⟩

omit [Fact (0 < L)] in
theorem isTest_of_mem {φ : (Fin k → ℝ) → ℂ} (h : φ ∈ testSub L k) : IsTorusTest L φ := h

omit [Fact (0 < L)] in
theorem conj_isTest {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    IsTorusTest L (fun x => conj (φ x)) :=
  ⟨Complex.conjCLE.contDiff.comp hφ.smooth, fun x m => by simp only [hφ.periodic x m]⟩

variable (L k) in
/-- `φ ↦ [φ] ∈ L²(𝕋_L^k)` on smooth periodic profiles (the frozen `cls`). -/
def clsL : testSub L k →ₗ[ℂ] L2TN L k where
  toFun φ := cls (isTest_of_mem φ.2)
  map_add' φ ψ := by
    apply Lp.ext
    filter_upwards [coe_cls (isTest_of_mem (φ + ψ).2), coe_cls (isTest_of_mem φ.2),
      coe_cls (isTest_of_mem ψ.2),
      Lp.coeFn_add (cls (isTest_of_mem φ.2)) (cls (isTest_of_mem ψ.2))] with y h h1 h2 h3
    rw [h, h3, Pi.add_apply, h1, h2]
    rfl
  map_smul' c φ := by
    apply Lp.ext
    filter_upwards [coe_cls (isTest_of_mem (c • φ).2), coe_cls (isTest_of_mem φ.2),
      Lp.coeFn_smul c (cls (isTest_of_mem φ.2))] with y h h1 h2
    rw [h, RingHom.id_apply, h2, Pi.smul_apply, h1]
    rfl

theorem clsL_apply (φ : testSub L k) : clsL L k φ = cls (isTest_of_mem φ.2) := rfl

theorem continuous_liftK_of_isTest {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    Continuous (liftK (L := L) φ) :=
  BetheH1.continuous_liftK hφ.smooth.continuous hφ.periodic

/-- Distinct smooth periodic profiles have distinct `L²` classes. -/
theorem clsL_injective : Function.Injective (clsL L k) := by
  refine (injective_iff_map_eq_zero _).2 fun φ hφ => ?_
  have hT := isTest_of_mem φ.2
  have h0 : liftK (L := L) (φ : (Fin k → ℝ) → ℂ) =ᵐ[torusPiMeasure L k] fun _ => (0 : ℂ) := by
    have h2 : ((clsL L k φ : L2TN L k) : (Fin k → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L k] 0 := by
      rw [hφ]; exact Lp.coeFn_zero _ _ _
    exact (coe_cls hT).symm.trans h2
  have h1 := (Continuous.ae_eq_iff_eq (torusPiMeasure L k) (continuous_liftK_of_isTest hT)
    continuous_const).1 h0
  apply Subtype.ext
  funext x
  have := congrFun h1 (fun i => (x i : AddCircle L))
  rw [liftK_coe hT.periodic] at this
  simpa using this

end Profiles

/-! ## Part 3: kernel analysis -/

section Kernel

variable {L : ℝ} [Fact (0 < L)] {k : ℕ} {K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ}

/-- A kernel slice `x ↦ K(x, y)`. -/
def slice (K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ) (y : Fin k → ℝ) : (Fin k → ℝ) → ℂ := fun x => K x y

variable (L) in
/-- The kernel read on `𝕋_L^k × 𝕋_L^k`. -/
def kt (K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ) (s t : Fin k → AddCircle L) : ℂ :=
  K (fun i => rep (s i)) (fun i => rep (t i))

omit [Fact (0 < L)] in
theorem slice_isTest (hK : IsSmoothPeriodicKernel L K) (y : Fin k → ℝ) :
    IsTorusTest L (slice K y) :=
  ⟨hK.smooth.comp (contDiff_id.prodMk contDiff_const), hK.periodic_left y⟩

omit [Fact (0 < L)] in
theorem column_isTest (hK : IsSmoothPeriodicKernel L K) (x : Fin k → ℝ) : IsTorusTest L (K x) :=
  ⟨hK.smooth.comp (contDiff_const.prodMk contDiff_id), hK.periodic_right x⟩

theorem measurable_repK : Measurable (fun s : Fin k → AddCircle L => fun i => rep (s i)) :=
  measurable_pi_iff.mpr fun i => measurable_rep.comp (measurable_pi_apply i)

theorem kernel_bound (hK : IsSmoothPeriodicKernel L K) :
    ∃ C, ∀ s t : Fin k → AddCircle L, ‖kt L K s t‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : Fin k → ℝ)) (b := fun _ => L)).prod
    (isCompact_Icc (a := (0 : Fin k → ℝ)) (b := fun _ => L))).exists_bound_of_continuousOn
    hK.smooth.continuous.continuousOn
  exact ⟨C, fun s t => hC ((fun i => rep (s i)), (fun i => rep (t i)))
    ⟨⟨fun i => (rep_mem (s i)).1, fun i => (rep_mem (s i)).2⟩,
     ⟨fun i => (rep_mem (t i)).1, fun i => (rep_mem (t i)).2⟩⟩⟩

theorem measurable_kt (hK : IsSmoothPeriodicKernel L K) :
    Measurable (fun z : (Fin k → AddCircle L) × (Fin k → AddCircle L) => kt L K z.1 z.2) :=
  hK.smooth.continuous.measurable.comp
    ((measurable_repK.comp measurable_fst).prodMk (measurable_repK.comp measurable_snd))

theorem integrable_L2 (φ : L2TN L k) :
    Integrable (φ : (Fin k → AddCircle L) → ℂ) (torusPiMeasure L k) :=
  (Lp.memLp φ).integrable (by norm_num)

/-- A bounded continuous function on the compact torus. -/
theorem exists_bound_of_continuous {h : (Fin k → AddCircle L) → ℂ} (hh : Continuous h) :
    ∃ C, ∀ t, ‖h t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Fin k → AddCircle L)).exists_bound_of_continuousOn
    hh.continuousOn
  exact ⟨C, fun t => hC t (Set.mem_univ _)⟩

theorem integrable_bdd_mul {c : (Fin k → AddCircle L) → ℂ} (hc : Measurable c) {C : ℝ}
    (hC : ∀ t, ‖c t‖ ≤ C) (ψ : L2TN L k) :
    Integrable (fun t => c t * (ψ : (Fin k → AddCircle L) → ℂ) t) (torusPiMeasure L k) := by
  refine Integrable.mono' ((integrable_L2 ψ).norm.const_mul C)
    (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable ψ)) (ae_of_all _ fun t => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _)

/-- **Fubini for the kernel pairing.** -/
theorem kernel_swap (hK : IsSmoothPeriodicKernel L K) (φ ψ : L2TN L k) :
    ∫ s, conj ((φ : (Fin k → AddCircle L) → ℂ) s) *
        ∫ t, kt L K s t * (ψ : (Fin k → AddCircle L) → ℂ) t ∂(torusPiMeasure L k)
        ∂(torusPiMeasure L k) =
      ∫ t, (∫ s, conj ((φ : (Fin k → AddCircle L) → ℂ) s) * kt L K s t ∂(torusPiMeasure L k)) *
        (ψ : (Fin k → AddCircle L) → ℂ) t ∂(torusPiMeasure L k) := by
  obtain ⟨C, hC⟩ := kernel_bound hK
  set μ := torusPiMeasure L k
  have hint : Integrable (Function.uncurry fun s t => conj ((φ : (Fin k → AddCircle L) → ℂ) s) *
      (kt L K s t * (ψ : (Fin k → AddCircle L) → ℂ) t)) (μ.prod μ) := by
    have hb : Integrable (fun z : (Fin k → AddCircle L) × (Fin k → AddCircle L) =>
        C * (‖(φ : (Fin k → AddCircle L) → ℂ) z.1‖ * ‖(ψ : (Fin k → AddCircle L) → ℂ) z.2‖))
        (μ.prod μ) :=
      ((integrable_L2 φ).norm.mul_prod (integrable_L2 ψ).norm).const_mul C
    refine Integrable.mono' hb ?_ (ae_of_all _ fun z => ?_)
    · exact ((Complex.continuous_conj.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable φ)).comp_fst).mul
        ((measurable_kt hK).aestronglyMeasurable.mul (Lp.aestronglyMeasurable ψ).comp_snd)
    · show ‖conj ((φ : (Fin k → AddCircle L) → ℂ) z.1) *
          (kt L K z.1 z.2 * (ψ : (Fin k → AddCircle L) → ℂ) z.2)‖ ≤ _
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have := hC z.1 z.2
      have h1 := norm_nonneg ((φ : (Fin k → AddCircle L) → ℂ) z.1)
      have h2 := norm_nonneg ((ψ : (Fin k → AddCircle L) → ℂ) z.2)
      nlinarith [mul_nonneg h1 h2]
  have hsw := integral_integral_swap hint
  calc ∫ s, conj ((φ : (Fin k → AddCircle L) → ℂ) s) *
        ∫ t, kt L K s t * (ψ : (Fin k → AddCircle L) → ℂ) t ∂μ ∂μ
      = ∫ s, ∫ t, conj ((φ : (Fin k → AddCircle L) → ℂ) s) *
          (kt L K s t * (ψ : (Fin k → AddCircle L) → ℂ) t) ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ t, ∫ s, conj ((φ : (Fin k → AddCircle L) → ℂ) s) *
          (kt L K s t * (ψ : (Fin k → AddCircle L) → ℂ) t) ∂μ ∂μ := hsw
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        dsimp only
        rw [← integral_mul_const]
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        ring

variable (L) in
/-- `h_φ(t) = ∫ \overline{φ(s)} K(s,t) ds = ⟨φ, K(·,t)⟩`. -/
def hfun (K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ) (φ : L2TN L k) (t : Fin k → AddCircle L) : ℂ :=
  ∫ s, conj ((φ : (Fin k → AddCircle L) → ℂ) s) * kt L K s t ∂(torusPiMeasure L k)

theorem continuous_hfun (hK : IsSmoothPeriodicKernel L K) (φ : L2TN L k) :
    Continuous (hfun L K φ) := by
  obtain ⟨C, hC⟩ := kernel_bound hK
  refine continuous_of_dominated (bound := fun s => ‖(φ : (Fin k → AddCircle L) → ℂ) s‖ * C)
    (fun t => ?_) (fun t => ae_of_all _ fun s => ?_) ((integrable_L2 φ).norm.mul_const C)
    (ae_of_all _ fun s => ?_)
  · refine (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable φ)).mul ?_
    exact (measurable_liftK (L := L) (slice_isTest hK (fun i => rep (t i))).smooth.continuous.measurable).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hC s t) (norm_nonneg _)
  · exact continuous_const.mul (continuous_liftK_of_isTest (column_isTest hK (fun i => rep (s i))))

theorem inner_L2_eq (φ ψ : L2TN L k) :
    ⟪φ, ψ⟫_ℂ = ∫ s, conj ((φ : (Fin k → AddCircle L) → ℂ) s) * (ψ : (Fin k → AddCircle L) → ℂ) s
      ∂(torusPiMeasure L k) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [RCLike.inner_apply]
  ring

/-- **Key lemma.** If `φ ⊥ range J`, then `φ ⊥ K(·, y)` for every `y`. -/
theorem inner_slice_eq_zero (hK : IsSmoothPeriodicKernel L K) {J : L2TN L k →L[ℂ] L2TN L k}
    (hJ : IsIntegralOperator J K) (φ : L2TN L k) (hφ : ∀ ψ, ⟪φ, J ψ⟫_ℂ = 0) (y : Fin k → ℝ) :
    ⟪φ, cls (slice_isTest hK y)⟫_ℂ = 0 := by
  set μ := torusPiMeasure L k
  have hc := continuous_hfun hK φ
  -- `∫ h_φ ψ = 0` for every `ψ`
  have hpair : ∀ ψ : L2TN L k,
      ∫ t, hfun L K φ t * (ψ : (Fin k → AddCircle L) → ℂ) t ∂μ = 0 := by
    intro ψ
    rw [← hφ ψ, inner_L2_eq]
    have e : ∫ s, conj ((φ : (Fin k → AddCircle L) → ℂ) s) * ((J ψ : L2TN L k) :
        (Fin k → AddCircle L) → ℂ) s ∂μ = ∫ s, conj ((φ : (Fin k → AddCircle L) → ℂ) s) *
          ∫ t, kt L K s t * (ψ : (Fin k → AddCircle L) → ℂ) t ∂μ ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hJ ψ] with s hs
      rw [hs]
      rfl
    rw [e, kernel_swap hK φ ψ]
    rfl
  -- take `ψ = \overline{h_φ}`
  obtain ⟨C, hC⟩ := exists_bound_of_continuous hc
  have hmem : MemLp (fun t => conj (hfun L K φ t)) 2 μ :=
    MemLp.of_bound (Complex.continuous_conj.comp hc).aestronglyMeasurable C
      (ae_of_all _ fun t => by simpa [Complex.norm_conj] using hC t)
  have h0 := hpair (hmem.toLp _)
  have e2 : ∫ t, hfun L K φ t * ((hmem.toLp _ : L2TN L k) : (Fin k → AddCircle L) → ℂ) t ∂μ =
      ((∫ t, Complex.normSq (hfun L K φ t) ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with t ht
    rw [ht, Complex.mul_conj]
  rw [e2, Complex.ofReal_eq_zero] at h0
  have hns : Continuous fun t => Complex.normSq (hfun L K φ t) :=
    Complex.continuous_normSq.comp hc
  obtain ⟨C', hC'⟩ := exists_bound_of_continuous (L := L) (k := k)
    (h := fun t => (Complex.normSq (hfun L K φ t) : ℂ)) (Complex.continuous_ofReal.comp hns)
  have hint : Integrable (fun t => Complex.normSq (hfun L K φ t)) μ :=
    Integrable.of_bound hns.aestronglyMeasurable C' (ae_of_all _ fun t => by
      simpa [Complex.norm_real] using hC' t)
  have hae := (integral_eq_zero_iff_of_nonneg (fun t => Complex.normSq_nonneg _) hint).1 h0
  have hz := (Continuous.ae_eq_iff_eq μ hns continuous_const).1 hae
  have hy : hfun L K φ (fun i => (y i : AddCircle L)) = 0 :=
    Complex.normSq_eq_zero.1 (congrFun hz _)
  rw [inner_L2_eq, ← hy]
  refine integral_congr_ae ?_
  filter_upwards [coe_cls (slice_isTest hK y)] with s hs
  rw [hs]
  show _ = conj ((φ : (Fin k → AddCircle L) → ℂ) s) *
    liftK (L := L) (K (fun i => rep (s i))) (fun i => (y i : AddCircle L))
  rw [liftK_coe (hK.periodic_right _)]
  rfl

/-- **Every kernel slice `K(·, y)` lies in the range of `J`** (finite-dimensional, hence closed). -/
theorem cls_slice_mem_range (hK : IsSmoothPeriodicKernel L K) {J : L2TN L k →L[ℂ] L2TN L k}
    (hR : IsFiniteRank J) (hJ : IsIntegralOperator J K) (y : Fin k → ℝ) :
    cls (slice_isTest hK y) ∈ LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k) := by
  have : FiniteDimensional ℂ (LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k)) := hR
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k)), Submodule.mem_orthogonal]
  intro u hu
  refine inner_slice_eq_zero hK hJ u (fun ψ => ?_) y
  rw [Submodule.mem_orthogonal] at hu
  exact inner_eq_zero_symm.1 (hu _ (LinearMap.mem_range_self (J : L2TN L k →ₗ[ℂ] L2TN L k) ψ))

end Kernel

/-! ## Part 4: the span of the slices and the normal form of the kernel -/

section Span

variable {L : ℝ} [Fact (0 < L)] {k : ℕ} {K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ}

/-- A slice as a smooth periodic profile. -/
def sliceT (hK : IsSmoothPeriodicKernel L K) (y : Fin k → ℝ) : testSub L k :=
  ⟨slice K y, slice_isTest hK y⟩

/-- The span of the kernel slices, inside the smooth periodic profiles. -/
def spanW (hK : IsSmoothPeriodicKernel L K) : Submodule ℂ (testSub L k) :=
  Submodule.span ℂ (Set.range (sliceT hK))

theorem clsL_mem_range (hK : IsSmoothPeriodicKernel L K) {J : L2TN L k →L[ℂ] L2TN L k}
    (hR : IsFiniteRank J) (hJ : IsIntegralOperator J K) (w : spanW hK) :
    clsL L k (w : testSub L k) ∈ LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k) := by
  have hle : (spanW hK).map (clsL L k) ≤ LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k) := by
    rw [spanW, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact cls_slice_mem_range hK hR hJ y
  exact hle (Submodule.mem_map_of_mem w.2)

/-- The span of the slices is finite-dimensional. -/
theorem finiteDimensional_spanW (hK : IsSmoothPeriodicKernel L K) {J : L2TN L k →L[ℂ] L2TN L k}
    (hR : IsFiniteRank J) (hJ : IsIntegralOperator J K) : FiniteDimensional ℂ (spanW hK) := by
  have : FiniteDimensional ℂ (LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k)) := hR
  let F : spanW hK →ₗ[ℂ] LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k) :=
    ((clsL L k).comp (spanW hK).subtype).codRestrict (LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k))
      (fun w => clsL_mem_range hK hR hJ w)
  refine Module.Finite.of_injective F fun a b hab => ?_
  have h : clsL L k (a : testSub L k) = clsL L k (b : testSub L k) := congrArg Subtype.val hab
  exact Subtype.ext (clsL_injective h)

/-- On a finite-dimensional space of functions, every linear functional is a finite combination of
point evaluations. -/
theorem dual_eq_eval {X V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : V →ₗ[ℂ] (X → ℂ)) (he : Function.Injective e) (ℓ : Module.Dual ℂ V) :
    ∃ a : X →₀ ℂ, ∀ w, ℓ w = a.sum fun x c => c * e w x := by
  let ev : X → Module.Dual ℂ V := fun x => (LinearMap.proj x).comp e
  let E : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ (Set.range ev)
  have h1 : E.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have : e w = 0 := funext fun x => hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
    rw [Submodule.mem_bot]
    exact (map_eq_zero_iff e he).1 this
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := E)
  rw [h1, Submodule.dualAnnihilator_bot] at h2
  have hℓ : ℓ ∈ E := h2 ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hℓ
  refine ⟨a, fun w => ?_⟩
  rw [← ha]
  simp [Finsupp.sum, ev]

/-- The embedding of the slice span into functions `ℝ^k → ℂ`. -/
def embW (hK : IsSmoothPeriodicKernel L K) : spanW hK →ₗ[ℂ] ((Fin k → ℝ) → ℂ) :=
  (testSub L k).subtype.comp (spanW hK).subtype

omit [Fact (0 < L)] in
theorem embW_injective (hK : IsSmoothPeriodicKernel L K) : Function.Injective (embW hK) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

omit [Fact (0 < L)] in
/-- **Normal form of the kernel.** A smooth periodic kernel whose slices span a finite-dimensional
space is `Σ_r f_r(x) \overline{g_r(y)}` everywhere, with smooth lattice-periodic `f_r, g_r`. -/
theorem kernel_normalForm (hK : IsSmoothPeriodicKernel L K) [FiniteDimensional ℂ (spanW hK)] :
    ∃ (n : ℕ) (f g : Fin n → (Fin k → ℝ) → ℂ), (∀ r, IsTorusTest L (f r)) ∧
      (∀ r, IsTorusTest L (g r)) ∧ ∀ x y, K x y = ∑ r, f r x * conj (g r y) := by
  have : Module.Free ℂ (spanW hK) := @Module.Free.of_divisionRing ℂ (spanW hK) _ _ _
  let b := Module.finBasis ℂ (spanW hK)
  choose a ha using fun r => @dual_eq_eval (Fin k → ℝ) (spanW hK) _ _ _ (embW hK) (embW_injective hK) (b.coord r)
  let c : Fin (Module.finrank ℂ (spanW hK)) → (Fin k → ℝ) → ℂ :=
    fun r y => (a r).sum fun x c => c * K x y
  have hc : ∀ r, IsTorusTest L (c r) := fun r =>
    ⟨ContDiff.sum fun x _ => contDiff_const.mul (column_isTest hK x).smooth, fun y m => by
      simp only [c, Finsupp.sum, (column_isTest hK _).periodic y m]⟩
  refine ⟨Module.finrank ℂ (spanW hK), fun r => ((b r : testSub L k) : (Fin k → ℝ) → ℂ),
    fun r y => conj (c r y), fun r => (b r : testSub L k).2, fun r => conj_isTest (hc r),
    fun x y => ?_⟩
  let w : spanW hK := ⟨sliceT hK y, Submodule.subset_span ⟨y, rfl⟩⟩
  have h := congrFun (congrArg (embW hK) (b.sum_repr w)) x
  rw [map_sum, Finset.sum_apply] at h
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h
  have hw : embW hK w x = K x y := rfl
  rw [hw] at h
  rw [← h]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.conj_conj, mul_comm]
  congr 1
  rw [← Module.Basis.coord_apply, ha r w]
  rfl

end Span

/-! ## Part 5: finite sums of smooth rank-one operators -/

section Sums

variable {L : ℝ} [Fact (0 < L)] {k n : ℕ}

theorem Jsum_apply (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
    (hg : ∀ r, IsTorusTest L (g r)) (ψ : L2TN L k) :
    Jsum f g hf hg ψ = ∑ r, ⟪cls (hg r), ψ⟫_ℂ • cls (hf r) := by
  unfold Jsum
  rw [sum_apply]
  simp only [InnerProductSpace.rankOne_apply]

theorem coe_Jsum (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
    (hg : ∀ r, IsTorusTest L (g r)) (ψ : L2TN L k) :
    (Jsum f g hf hg ψ : (Fin k → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L k]
      fun t => ∑ r, ⟪cls (hg r), ψ⟫_ℂ * f r (fun i => rep (t i)) := by
  have hmem : (fun x => ∑ r, ⟪cls (hg r), ψ⟫_ℂ * f r x) ∈ testSub L k := by
    have : (fun x => ∑ r, ⟪cls (hg r), ψ⟫_ℂ * f r x) =
        ∑ r, ⟪cls (hg r), ψ⟫_ℂ • f r := by
      funext x; simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hf r)
  have e : Jsum f g hf hg ψ = clsL L k ⟨_, hmem⟩ := by
    have : (⟨_, hmem⟩ : testSub L k) = ∑ r, ⟪cls (hg r), ψ⟫_ℂ • (⟨f r, hf r⟩ : testSub L k) := by
      apply Subtype.ext
      funext x
      simp [Finset.sum_apply]
    rw [this, map_sum, Jsum_apply]
    simp only [map_smul]
    rfl
  rw [e]
  exact coe_cls (isTest_of_mem hmem)

/-- `⟨[g], ψ⟩ = ∫ \overline{g(y)} ψ(y) dy`. -/
theorem inner_cls (g : (Fin k → ℝ) → ℂ) (hg : IsTorusTest L g) (ψ : L2TN L k) :
    ⟪cls hg, ψ⟫_ℂ = ∫ s, conj (g (fun i => rep (s i))) * (ψ : (Fin k → AddCircle L) → ℂ) s
      ∂(torusPiMeasure L k) := by
  rw [inner_L2_eq]
  refine integral_congr_ae ?_
  filter_upwards [coe_cls hg] with s hs
  rw [hs]
  rfl

/-- **Finite sums of smooth rank-one operators are integral operators** with the smooth kernel
`Σ_r f_r(x) \overline{g_r(y)}`. -/
theorem Jsum_isIntegralOperator (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
    (hg : ∀ r, IsTorusTest L (g r)) :
    IsIntegralOperator (Jsum f g hf hg) (fun x y => ∑ r, f r x * conj (g r y)) := by
  intro ψ
  filter_upwards [coe_Jsum f g hf hg ψ] with t ht
  rw [ht]
  have hint : ∀ r, Integrable (fun s => conj (g r (fun i => rep (s i))) *
      (ψ : (Fin k → AddCircle L) → ℂ) s) (torusPiMeasure L k) := fun r => by
    obtain ⟨C, hC⟩ := exists_bound_of_continuous (L := L) (k := k)
      (h := fun s => conj (liftK (L := L) (g r) s))
      (Complex.continuous_conj.comp (continuous_liftK_of_isTest (hg r)))
    exact integrable_bdd_mul (Complex.continuous_conj.comp
      (continuous_liftK_of_isTest (hg r))).measurable hC ψ
  calc ∑ r, ⟪cls (hg r), ψ⟫_ℂ * f r (fun i => rep (t i))
      = ∑ r, ∫ s, f r (fun i => rep (t i)) * (conj (g r (fun i => rep (s i))) *
          (ψ : (Fin k → AddCircle L) → ℂ) s) ∂(torusPiMeasure L k) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [inner_cls, integral_const_mul, mul_comm]
    _ = ∫ s, ∑ r, f r (fun i => rep (t i)) * (conj (g r (fun i => rep (s i))) *
          (ψ : (Fin k → AddCircle L) → ℂ) s) ∂(torusPiMeasure L k) :=
        (integral_finsetSum _ fun r _ => (hint r).const_mul _).symm
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring

omit [Fact (0 < L)] in
theorem Jsum_kernel_isSmooth (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
    (hg : ∀ r, IsTorusTest L (g r)) :
    IsSmoothPeriodicKernel L (fun x y => ∑ r, f r x * conj (g r y)) where
  smooth := ContDiff.sum fun r _ =>
    ((hf r).smooth.comp contDiff_fst).mul ((conj_isTest (hg r)).smooth.comp contDiff_snd)
  periodic_left := fun y x m => by simp only [(hf _).periodic x m]
  periodic_right := fun x y m => by simp only [(hg _).periodic y m]

theorem Jsum_isFiniteRank (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
    (hg : ∀ r, IsTorusTest L (g r)) : IsFiniteRank (Jsum f g hf hg) := by
  have hle : LinearMap.range (Jsum f g hf hg : L2TN L k →ₗ[ℂ] L2TN L k) ≤
      Submodule.span ℂ (Set.range fun r => cls (hf r)) := by
    rintro _ ⟨ψ, rfl⟩
    show Jsum f g hf hg ψ ∈ _
    rw [Jsum_apply]
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun r => cls (hf r))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le hle

end Sums

/-! ## Part 6: the equivalence with the normal form -/

section Equivalence

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- Two integral operators with the same kernel are equal. -/
theorem eq_of_isIntegralOperator {J J' : L2TN L k →L[ℂ] L2TN L k}
    {K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ} (hJ : IsIntegralOperator J K)
    (hJ' : IsIntegralOperator J' K) : J = J' := by
  ext1 ψ
  exact Lp.ext ((hJ ψ).trans (hJ' ψ).symm)

/-- **Normal form.** Every finite-rank operator with smooth kernel on `k` variables is
`Σ_r |f_r⟩⟨g_r|` with finitely many smooth lattice-periodic `f_r, g_r`, exactly the `Jsum` consumed
by `energy002`. -/
theorem exists_Jsum_of_isFiniteRankSmoothKernel {J : L2TN L k →L[ℂ] L2TN L k}
    (hJ : IsFiniteRankSmoothKernel J) :
    ∃ (n : ℕ) (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
      (hg : ∀ r, IsTorusTest L (g r)), J = Jsum f g hf hg := by
  obtain ⟨hR, K, hK, hJK⟩ := hJ
  have := finiteDimensional_spanW hK hR hJK
  obtain ⟨n, f, g, hf, hg, hKfg⟩ := kernel_normalForm hK
  refine ⟨n, f, g, hf, hg, eq_of_isIntegralOperator hJK ?_⟩
  have hfun : K = fun x y => ∑ r, f r x * conj (g r y) := funext fun x => funext fun y => hKfg x y
  rw [hfun]
  exact Jsum_isIntegralOperator f g hf hg

/-- **The literal predicate is equivalent to the normal form.** -/
theorem isFiniteRankSmoothKernel_iff (J : L2TN L k →L[ℂ] L2TN L k) :
    IsFiniteRankSmoothKernel J ↔
      ∃ (n : ℕ) (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
        (hg : ∀ r, IsTorusTest L (g r)), J = Jsum f g hf hg := by
  refine ⟨exists_Jsum_of_isFiniteRankSmoothKernel, ?_⟩
  rintro ⟨n, f, g, hf, hg, rfl⟩
  exact ⟨Jsum_isFiniteRank f g hf hg, _, Jsum_kernel_isSmooth f g hf hg,
    Jsum_isIntegralOperator f g hf hg⟩

end Equivalence

/-! ## Part 7: ENERGY-002 for every literal finite-rank smooth-kernel operator -/

section Literal

variable {L : ℝ} [Fact (0 < L)]

/-- The external commutator clause of `energy002`, phrased for the operator `J` itself:
`J ⊗ Id` (`JI J`) is characterized by its matrix elements and has adjoint `J^* ⊗ Id`; it maps `H¹`
to `H¹` (`KJ`, `KJ'` for `J ⊗ Id` and `J^* ⊗ Id`); and
`A^{-1/2}[B_{i,k+1}, J ⊗ Id]A^{-1/2}` is a compact operator `C` with commutator form
`b(φ, (J⊗Id)ψ) − b((J⊗Id)^*φ, ψ)` on `H¹`, also after bosonic restriction. -/
def ExtCommLit (L : ℝ) [Fact (0 < L)] {k : ℕ} (J : L2TN L k →L[ℂ] L2TN L k) (i : Fin k) : Prop :=
  ((∀ (a a' : Fin k → L2T L) (u u' : L2T L),
      ⟪elem a u, JI J (elem a' u')⟫_ℂ = ⟪prodLp a, J (prodLp a')⟫_ℂ * ⟪u, u'⟫_ℂ) ∧
    (∀ T : L2TN L (k + 1) →L[ℂ] L2TN L (k + 1),
      (∀ (a a' : Fin k → L2T L) (u u' : L2T L),
        ⟪elem a u, T (elem a' u')⟫_ℂ = ⟪prodLp a, J (prodLp a')⟫_ℂ * ⟪u, u'⟫_ℂ) → T = JI J) ∧
    (∀ x y : L2TN L (k + 1), ⟪x, JI J y⟫_ℂ = ⟪JI (ContinuousLinearMap.adjoint J) x, y⟫_ℂ)) ∧
  ∃ KJ KJ' : PhysH1 L (k + 1) → PhysH1 L (k + 1),
    (∀ φ : PhysH1 L (k + 1), (KJ φ).val = JI J φ.val) ∧
    (∀ φ : PhysH1 L (k + 1), (KJ' φ).val = JI (ContinuousLinearMap.adjoint J) φ.val) ∧
    ∃ C : L2TN L (k + 1) →L[ℂ] L2TN L (k + 1), IsCompactOperator C ∧
      (∀ φ ψ : PhysH1 L (k + 1),
        ⟪PhysH1.unitary φ, C (PhysH1.unitary ψ)⟫_ℂ =
          bform (ext_ne i) φ (KJ ψ) - bform (ext_ne i) (KJ' φ) ψ) ∧
      CompressClause C (fun φ ψ => bform (ext_ne i) φ (KJ ψ) - bform (ext_ne i) (KJ' φ) ψ)

/-- The internal commutator clause of `energy002`, phrased for the operator `J` itself. -/
def IntCommLit (L : ℝ) [Fact (0 < L)] {k : ℕ} (J : L2TN L k →L[ℂ] L2TN L k) {i j : Fin k}
    (hij : i ≠ j) : Prop :=
  ∃ KJ KJ' : PhysH1 L k → PhysH1 L k,
    (∀ φ : PhysH1 L k, (KJ φ).val = J φ.val) ∧
    (∀ φ : PhysH1 L k, (KJ' φ).val = ContinuousLinearMap.adjoint J φ.val) ∧
    ∃ C : L2TN L k →L[ℂ] L2TN L k, IsCompactOperator C ∧
      (∀ φ ψ : PhysH1 L k,
        ⟪PhysH1.unitary φ, C (PhysH1.unitary ψ)⟫_ℂ = bform hij φ (KJ ψ) - bform hij (KJ' φ) ψ) ∧
      CompressClause C (fun φ ψ => bform hij φ (KJ ψ) - bform hij (KJ' φ) ψ)

theorem extCommLit {k : ℕ} {J : L2TN L k →L[ℂ] L2TN L k} (hJ : IsFiniteRankSmoothKernel J)
    (i : Fin k) : ExtCommLit L J i := by
  obtain ⟨n, f, g, hf, hg, rfl⟩ := exists_Jsum_of_isFiniteRankSmoothKernel hJ
  obtain ⟨h1, h2, h3, C, hC, hform, hcomp⟩ := extCommClause f g hf hg i
  exact ⟨h1, KH f g hf hg, KH g f hg hf, h2, h3, C, hC, hform, hcomp⟩

theorem intCommLit {k : ℕ} {J : L2TN L k →L[ℂ] L2TN L k} (hJ : IsFiniteRankSmoothKernel J)
    {i j : Fin k} (hij : i ≠ j) : IntCommLit L J hij := by
  obtain ⟨n, f, g, hf, hg, rfl⟩ := exists_Jsum_of_isFiniteRankSmoothKernel hJ
  obtain ⟨h2, h3, C, hC, hform, hcomp⟩ := intCommClause f g hf hg hij
  exact ⟨KHi f g hf hg, KHi g f hg hf, h2, h3, C, hC, hform, hcomp⟩

/-- **ENERGY-002 (`lem:A1-trace`, `cubic_charge.tex:74`), with the literal hypothesis on `J`.**
For every `L > 0`:
* the first paragraph (all `m ≥ 2`, all pairs `i ≠ j`, also after bosonic restriction), as in
  `energy002`;
* for every `k` and every finite-rank operator `J` on `L²(𝕋_L^k)` with smooth kernel (the literal
  `IsFiniteRankSmoothKernel`): `J = Σ_r |f_r⟩⟨g_r|` with smooth lattice-periodic `f_r, g_r`, and for
  that representation the external and internal clauses `ExtCommClause`, `IntCommClause` of
  `energy002` hold;
* the same clauses phrased for `J` itself (`ExtCommLit`, `IntCommLit`), independent of the chosen
  representation. -/
theorem energy002_literal (L : ℝ) [Fact (0 < L)] :
    (∀ m : ℕ, 2 ≤ m → ∀ (i j : Fin m) (hij : i ≠ j),
        TraceClause L m i j hij ∧ TraceClauseSym L m i j hij) ∧
    (∀ (k : ℕ) (J : L2TN L k →L[ℂ] L2TN L k), IsFiniteRankSmoothKernel J →
      ∃ (n : ℕ) (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
        (hg : ∀ r, IsTorusTest L (g r)),
        J = Jsum f g hf hg ∧ (∀ i : Fin k, ExtCommClause L f g hf hg i) ∧
          ∀ (i j : Fin k) (hij : i ≠ j), IntCommClause L f g hf hg hij) ∧
    (∀ (k : ℕ) (J : L2TN L k →L[ℂ] L2TN L k), IsFiniteRankSmoothKernel J →
      (∀ i : Fin k, ExtCommLit L J i) ∧ ∀ (i j : Fin k) (hij : i ≠ j), IntCommLit L J hij) := by
  obtain ⟨h0, hext, hint⟩ := energy002 L
  refine ⟨h0, fun k J hJ => ?_, fun k J hJ => ⟨fun i => extCommLit hJ i,
    fun i j hij => intCommLit hJ hij⟩⟩
  obtain ⟨n, f, g, hf, hg, hJs⟩ := exists_Jsum_of_isFiniteRankSmoothKernel hJ
  exact ⟨n, f, g, hf, hg, hJs, fun i => hext k n f g hf hg i,
    fun i j hij => hint k n f g hf hg i j hij⟩

end Literal

/-! Kernel axiom audit. -/
#print axioms clsL_injective
#print axioms kernel_swap
#print axioms continuous_hfun
#print axioms inner_slice_eq_zero
#print axioms cls_slice_mem_range
#print axioms finiteDimensional_spanW
#print axioms dual_eq_eval
#print axioms kernel_normalForm
#print axioms coe_Jsum
#print axioms Jsum_isIntegralOperator
#print axioms Jsum_kernel_isSmooth
#print axioms Jsum_isFiniteRank
#print axioms exists_Jsum_of_isFiniteRankSmoothKernel
#print axioms isFiniteRankSmoothKernel_iff
#print axioms extCommLit
#print axioms intCommLit
#print axioms energy002_literal

end QuantumNLS.SmoothKernelNormalForm
