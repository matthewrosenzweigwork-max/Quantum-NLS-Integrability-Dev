import Mathlib
import QuantumNLS.HaarKernelFactorization
import QuantumNLS.BethePhysicalAssembly

/-!
# R-F611926F `QG:prop:haar-kernel-factorization` (stage 2): operator-level factorization on `L²(𝕋_L^r)`
(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:293`; imports stage 1 `HaarKernelFactorization` read-only)

Realized against the ACTUAL DEF-048 operator `BetheCompressedKernel.compressedKernel` (= `P_r(K⁺+K⁻)P_r` with both
`r!`-averages exposed, `physicalKernel_action`):
* `Rk`/`Rtens`: the resolvent kernel `R_z^ρ(x,y) = e^{iz(x−y)}/(1−q)(1_{x>y} + q 1_{x<y})` on the representatives
  `[0,L)` of `𝕋_L` and the integral operator `R_z^{⊗r}` with kernel `∏_i R_z^ρ(x_i,y_i)` on `L²(𝕋_L^r)`;
* `Sop`: multiplication by the ordering sign `sgn(x)` (the unitary `A_r` extended to all of `L²`, `sgnDec` of stage 1);
* **`compressed_operator_eq`**: for every `F ∈ L²(𝕋_L^r)` and `q = ρ_r e^{izL} ≠ 1`,
  `(P_r(K⁺+K⁻)P_r) F = (1−q)/r! · S R_z^{⊗r} S (P_r F)`, i.e. `K_{r,z} = (1−q)/r! · A_r^*(∧^r R_z^ρ)A_r` on `Sym^r`
  (`A_r^*(∧^r R)A_r f = S R^{⊗r} S f` for symmetric `f`, since `R^{⊗r}` commutes with permutations and `S` maps symmetric
  to antisymmetric functions);
* the symmetric-sector version `physicalKernel_factorization` through `physicalKernel_action`.
Proof: stage-1 pointwise identity `averagedRaw = (1−q)/(r!)² sgn sgn det R` on the almost-sure set of tuples with
distinct coordinates in `(0,L)` and no ties, expanded by Leibniz as `Σ_τ B(X, Y∘τ)` (`B = sgn sgn ∏ R`), then
`permutedKernel_operator` and the position average.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators InnerProductSpace ComplexConjugate Classical

namespace QuantumNLS.HaarKernelFactorizationOp

open QuantumNLS.BetheIntegralOperator QuantumNLS.PhysicalTensor QuantumNLS.BetheWeakGradient
  QuantumNLS.BetheCompressedKernel QuantumNLS.HaarKernelFactorization

/-! ### Generic facts on integral operators and multiplication operators -/

section Generic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- Integral operators only depend on the kernel function almost everywhere. -/
theorem operator_congr_ae (k j : Kernel μ) (h : ∀ᵐ p ∂μ.prod μ, k.fn p = j.fn p) :
    k.operator = j.operator := by
  refine ContinuousLinearMap.ext (fun g => ?_)
  apply ext_inner_left ℂ
  intro f
  rw [Kernel.inner_operator, Kernel.inner_operator]
  simp only [Kernel.form]
  refine integral_congr_ae ?_
  filter_upwards [h] with p hp
  simp only [Kernel.integrand, hp]

variable (φ : X → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ x, ‖φ x‖ ≤ C)
include hφ hC

theorem memLp_mulFun (f : Lp ℂ 2 μ) : MemLp (fun x => φ x * f x) 2 μ :=
  MemLp.of_le_mul (c := C) (Lp.memLp f) (hφ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

/-- The multiplication of an `L²` class by a bounded measurable function. -/
def mulLp (f : Lp ℂ 2 μ) : Lp ℂ 2 μ := (memLp_mulFun φ hφ C hC f).toLp _

theorem coeFn_mulLp (f : Lp ℂ 2 μ) : mulLp φ hφ C hC f =ᵐ[μ] fun x => φ x * f x :=
  MemLp.coeFn_toLp _

/-- Multiplication by a bounded measurable function as a continuous linear map on `L²`. -/
def mulOp : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := mulLp φ hφ C hC
      map_add' := fun f g => by
        refine Lp.ext ?_
        filter_upwards [coeFn_mulLp φ hφ C hC (f + g), coeFn_mulLp φ hφ C hC f, coeFn_mulLp φ hφ C hC g,
          Lp.coeFn_add f g, Lp.coeFn_add (mulLp φ hφ C hC f) (mulLp φ hφ C hC g)] with x h1 h2 h3 h4 h5
        simp only [Pi.add_apply] at h4 h5
        rw [h1, h4, h5, h2, h3]; ring
      map_smul' := fun c f => by
        refine Lp.ext ?_
        filter_upwards [coeFn_mulLp φ hφ C hC (c • f), coeFn_mulLp φ hφ C hC f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (mulLp φ hφ C hC f)] with x h1 h2 h3 h4
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at h3 h4 ⊢
        rw [h1, h3, h4, h2]; ring } C
    (fun f => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [coeFn_mulLp φ hφ C hC f] with x hx
      show ‖(mulLp φ hφ C hC f) x‖ ≤ C * ‖f x‖
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

theorem coeFn_mulOp (f : Lp ℂ 2 μ) : mulOp φ hφ C hC f =ᵐ[μ] fun x => φ x * f x :=
  coeFn_mulLp φ hφ C hC f

end Generic

/-! ### The ordering sign -/

section Sgn

variable {m : ℕ}

theorem norm_sgnDec (X : Fin m → ℝ) : ‖sgnDec X‖ = 1 := by
  unfold sgnDec
  rcases Int.units_eq_one_or (Equiv.Perm.sign (sortPerm X)) with h | h <;> simp [h]

theorem conj_sgnDec (X : Fin m → ℝ) : conj (sgnDec X) = sgnDec X := by
  unfold sgnDec
  rcases Int.units_eq_one_or (Equiv.Perm.sign (sortPerm X)) with h | h <;> simp [h]

theorem measurableSet_sortPerm_eq (σ : Equiv.Perm (Fin m)) :
    MeasurableSet {X : Fin m → ℝ | sortPerm X = σ} := by
  have hset : {X : Fin m → ℝ | sortPerm X = σ} =
      {X | Monotone ((fun i => -X i) ∘ σ)} ∩
        {X | ∀ i j, i < j → -X (σ i) = -X (σ j) → σ i < σ j} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, sortPerm]
    rw [eq_comm, Tuple.eq_sort_iff]
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · have : {X : Fin m → ℝ | Monotone ((fun i => -X i) ∘ σ)} =
        ⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {X : Fin m → ℝ | -X (σ i) ≤ -X (σ j)} := by
      ext X; simp [Monotone]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (by fun_prop) (by fun_prop)
  · have : {X : Fin m → ℝ | ∀ i j, i < j → -X (σ i) = -X (σ j) → σ i < σ j} =
        ⋂ i, ⋂ j, ⋂ (_ : i < j), ({X : Fin m → ℝ | -X (σ i) = -X (σ j)}ᶜ ∪ {_X | σ i < σ j}) := by
      ext X; simp [imp_iff_not_or]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
    refine MeasurableSet.union (MeasurableSet.compl ?_) (MeasurableSet.const _)
    exact measurableSet_eq_fun (by fun_prop) (by fun_prop)

theorem measurable_sgnDec : Measurable (sgnDec (m := m)) := by
  have : (sgnDec (m := m)) = fun X => ∑ σ : Equiv.Perm (Fin m),
      if sortPerm X = σ then ((Equiv.Perm.sign σ : ℤˣ) : ℂ) else 0 := by
    funext X
    rw [Finset.sum_ite_eq]
    simp [sgnDec]
  rw [this]
  exact Finset.measurable_sum _ (fun σ _ =>
    Measurable.ite (measurableSet_sortPerm_eq σ) measurable_const measurable_const)

/-- The ordering sign transforms by the sign of a permutation of the coordinates (distinct coordinates). -/
theorem sgnDec_comp {X : Fin m → ℝ} (hX : Function.Injective X) (τ : Equiv.Perm (Fin m)) :
    sgnDec (X ∘ τ) = ((Equiv.Perm.sign τ : ℤˣ) : ℂ) * sgnDec X := by
  have hinj : Function.Injective (X ∘ τ) := hX.comp τ.injective
  have hs : StrictAnti ((X ∘ τ) ∘ sortPerm (X ∘ τ)) := sortPerm_strictAnti hinj
  have h1 : τ * sortPerm (X ∘ τ) = sortPerm X := by
    apply eq_sortPerm
    have : (X ∘ ⇑(τ * sortPerm (X ∘ τ))) = (X ∘ τ) ∘ sortPerm (X ∘ τ) := by
      funext i; rfl
    rw [this]; exact hs
  have h2 : sortPerm (X ∘ τ) = τ⁻¹ * sortPerm X := by
    rw [← h1]; group
  unfold sgnDec
  rw [h2, map_mul, Equiv.Perm.sign_inv]
  push_cast
  rfl

end Sgn

/-! ### The resolvent kernel and its tensor power -/

section Resolvent

variable (L : ℝ) [Fact (0 < L)] (m : ℕ) (q z : ℂ)

theorem measurable_Rk : Measurable (fun p : ℝ × ℝ => Rk q z p.1 p.2) := by
  unfold Rk
  have hl : Measurable (fun p : ℝ × ℝ => ((p.1 - p.2 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_fst.sub measurable_snd)
  have hexp : Measurable (fun p : ℝ × ℝ => Complex.exp (Complex.I * z * ((p.1 - p.2 : ℝ) : ℂ))) :=
    Complex.continuous_exp.measurable.comp (measurable_const.mul hl)
  refine (hexp.div_const _).mul ?_
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst) measurable_const
    (Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const measurable_const)

/-- Bound of the resolvent kernel on `[0,L)²`. -/
def RB : ℝ := Real.exp (L * |z.im|) / ‖1 - q‖ * max 1 ‖q‖

theorem RB_nonneg : 0 ≤ RB L q z := by unfold RB; positivity

theorem norm_Rk_le {a b : ℝ} (ha : 0 ≤ a ∧ a < L) (hb : 0 ≤ b ∧ b < L) :
    ‖Rk q z a b‖ ≤ RB L q z := by
  unfold Rk RB
  rw [norm_mul, norm_div]
  have hexp : ‖Complex.exp (Complex.I * z * ((a - b : ℝ) : ℂ))‖ ≤ Real.exp (L * |z.im|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (Complex.I * z * ((a - b : ℝ) : ℂ)).re = -(z.im * (a - b)) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have h1 : |a - b| ≤ L := by rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    calc -(z.im * (a - b)) ≤ |z.im * (a - b)| := neg_le_abs _
      _ = |z.im| * |a - b| := abs_mul _ _
      _ ≤ |z.im| * L := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = L * |z.im| := mul_comm _ _
  have hind : ‖(if b < a then (1 : ℂ) else if a < b then q else 0)‖ ≤ max 1 ‖q‖ := by
    split_ifs
    · simp
    · exact le_max_right _ _
    · simp
  calc ‖Complex.exp (Complex.I * z * ((a - b : ℝ) : ℂ))‖ / ‖1 - q‖ *
        ‖(if b < a then (1 : ℂ) else if a < b then q else 0)‖
      ≤ Real.exp (L * |z.im|) / ‖1 - q‖ * max 1 ‖q‖ := by
        gcongr
    _ = _ := rfl

theorem rep_bounds {N : ℕ} (x : Fin N → AddCircle L) (i : Fin N) :
    0 ≤ representatives L x i ∧ representatives L x i < L := by
  have := (AddCircle.equivIco L 0 (x i)).2
  simp only [Set.mem_Ico, zero_add] at this
  exact this

theorem measurable_repFst (i : Fin m) : Measurable (fun p : (Fin m → AddCircle L) × (Fin m → AddCircle L) =>
    representatives L p.1 i) :=
  (measurable_pi_apply i).comp ((measurable_representatives m L).comp measurable_fst)

theorem measurable_repSnd (i : Fin m) : Measurable (fun p : (Fin m → AddCircle L) × (Fin m → AddCircle L) =>
    representatives L p.2 i) :=
  (measurable_pi_apply i).comp ((measurable_representatives m L).comp measurable_snd)

theorem measurable_RkRep (i : Fin m) : Measurable (fun p : (Fin m → AddCircle L) × (Fin m → AddCircle L) =>
    Rk q z (representatives L p.1 i) (representatives L p.2 i)) :=
  by
    have h := (measurable_Rk q z).comp ((measurable_repFst L m i).prodMk (measurable_repSnd L m i))
    exact h

theorem measurable_RtensFn : Measurable (fun p : (Fin m → AddCircle L) × (Fin m → AddCircle L) =>
    ∏ i, Rk q z (representatives L p.1 i) (representatives L p.2 i)) :=
  Finset.measurable_prod (f := fun i (p : (Fin m → AddCircle L) × (Fin m → AddCircle L)) =>
    Rk q z (representatives L p.1 i) (representatives L p.2 i)) Finset.univ
    (fun i _ => measurable_RkRep L m q z i)

/-- `R_z^{⊗r}`: the integral kernel `∏_i R_z^ρ(x_i, y_i)` on `𝕋_L^r` (representatives in `[0,L)`). -/
def Rtens : Kernel (torusPiMeasure L m) where
  fn p := ∏ i, Rk q z (representatives L p.1 i) (representatives L p.2 i)
  measurable := measurable_RtensFn L m q z
  bound := (RB L q z) ^ m
  bound_nonneg := pow_nonneg (RB_nonneg L q z) _
  norm_le p := by
    rw [norm_prod]
    calc ∏ i, ‖Rk q z (representatives L p.1 i) (representatives L p.2 i)‖
        ≤ ∏ _i : Fin m, RB L q z :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
            (fun i _ => norm_Rk_le L q z (rep_bounds L p.1 i) (rep_bounds L p.2 i))
      _ = (RB L q z) ^ m := by simp

/-- The ordering sign `sgn(x)` as a multiplication operator on `L²(𝕋_L^r)`: the unitary involution extending `A_r`. -/
def Sop : L2TN L m →L[ℂ] L2TN L m :=
  mulOp (fun X => sgnDec (representatives L X))
    (measurable_sgnDec.comp (measurable_representatives m L)) 1 (fun X => (norm_sgnDec _).le)

theorem coeFn_Sop (f : L2TN L m) :
    Sop L m f =ᵐ[torusPiMeasure L m] fun X => sgnDec (representatives L X) * f X :=
  coeFn_mulOp _ _ _ _ f

/-- `B(x,y) = sgn(x) sgn(y) ∏_i R(x_i,y_i)`, the kernel of `S R^{⊗r} S`. -/
def Bker : Kernel (torusPiMeasure L m) where
  fn p := sgnDec (representatives L p.1) * sgnDec (representatives L p.2) *
    (Rtens L m q z).fn p
  measurable := ((measurable_sgnDec.comp ((measurable_representatives m L).comp measurable_fst)).mul
    (measurable_sgnDec.comp ((measurable_representatives m L).comp measurable_snd))).mul
    (Rtens L m q z).measurable
  bound := (RB L q z) ^ m
  bound_nonneg := pow_nonneg (RB_nonneg L q z) _
  norm_le p := by
    rw [norm_mul, norm_mul, norm_sgnDec, norm_sgnDec, one_mul, one_mul]
    exact (Rtens L m q z).norm_le p

theorem inner_Sop_left (f h : L2TN L m) : ⟪f, Sop L m h⟫_ℂ = ⟪Sop L m f, h⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_Sop L m h, coeFn_Sop L m f] with x hh hf
  simp only [RCLike.inner_apply', hh, hf, map_mul, conj_sgnDec]
  ring

/-- `B_op = S ∘ R^{⊗r} ∘ S`. -/
theorem Bker_operator : (Bker L m q z).operator =
    (Sop L m).comp ((Rtens L m q z).operator.comp (Sop L m)) := by
  refine ContinuousLinearMap.ext (fun g => ?_)
  apply ext_inner_left ℂ
  intro f
  rw [Kernel.inner_operator, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    inner_Sop_left, Kernel.inner_operator]
  simp only [Kernel.form]
  refine integral_congr_ae ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := torusPiMeasure L m)
      (ν := torusPiMeasure L m)).ae_eq_comp (coeFn_Sop L m f),
    (Measure.quasiMeasurePreserving_snd (μ := torusPiMeasure L m)
      (ν := torusPiMeasure L m)).ae_eq_comp (coeFn_Sop L m g)] with p hf hg
  simp only [Kernel.integrand, Bker, Function.comp_apply] at hf hg ⊢
  rw [hf, hg]
  simp only [map_mul, conj_sgnDec]
  ring

end Resolvent

/-! ### Almost-sure good points -/

section Good

variable (L : ℝ) [Fact (0 < L)] (m : ℕ)

theorem rep_injective {N : ℕ} {x : Fin N → AddCircle L} (hx : Function.Injective x) :
    Function.Injective (representatives L x) := by
  intro i j h
  apply hx
  apply (AddCircle.equivIco L 0).injective
  exact Subtype.ext h

theorem rep_pos {N : ℕ} {x : Fin N → AddCircle L} (hx : ∀ i, x i ≠ 0) (i : Fin N) :
    0 < representatives L x i := by
  have h0 := (rep_bounds L x i).1
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx i
    have := (AddCircle.coe_equivIco (p := L) (a := 0) (y := x i)).symm
    rw [this]
    have h' : ((AddCircle.equivIco L 0 (x i) : ℝ)) = 0 := h.symm
    rw [h']
    simp

theorem nullSingleton : NullSingletonClass (volume : Measure (AddCircle L)) :=
  ⟨fun x => by
    have h := AddCircle.volume_closedBall (T := L) (x := x) 0
    simpa only [Metric.closedBall_zero, mul_zero,
      min_eq_right (Fact.out : 0 < L).le, ENNReal.ofReal_zero] using h⟩

theorem ae_coord_ne_zero : ∀ᵐ x ∂torusPiMeasure L m, ∀ i, x i ≠ 0 := by
  have := nullSingleton L
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  have hset : {x : Fin m → AddCircle L | ¬ x i ≠ 0} = Function.eval i ⁻¹' {0} := by
    ext x; simp
  rw [hset]
  exact Measure.pi_eval_preimage_null (fun _ : Fin m => (volume : Measure (AddCircle L)))
    (measure_singleton _)

theorem ae_noTie : ∀ᵐ p ∂(torusPiMeasure L m).prod (torusPiMeasure L m),
    ∀ i j, p.1 i ≠ p.2 j := by
  have := nullSingleton L
  rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
  have hs : MeasurableSet {p : (Fin m → AddCircle L) × (Fin m → AddCircle L) | p.1 i ≠ p.2 j} :=
    (measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst)
      ((measurable_pi_apply j).comp measurable_snd)).compl
  refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 (Eventually.of_forall (fun x => ?_))
  rw [ae_iff]
  have hset : {y : Fin m → AddCircle L | ¬ ((x, y) ∈ {p : (Fin m → AddCircle L) ×
      (Fin m → AddCircle L) | p.1 i ≠ p.2 j})} =
      Function.eval j ⁻¹' ({x i} : Set (AddCircle L)) := by
    ext y; simp [eq_comm]
  rw [hset]
  exact Measure.pi_eval_preimage_null (fun _ : Fin m => (volume : Measure (AddCircle L)))
    (measure_singleton _)

theorem ae_good : ∀ᵐ p ∂(torusPiMeasure L m).prod (torusPiMeasure L m),
    Function.Injective (representatives L p.1) ∧ Function.Injective (representatives L p.2) ∧
    NoTie (representatives L p.1) (representatives L p.2) ∧
    (∀ i, 0 < representatives L p.1 i ∧ representatives L p.1 i < L) ∧
    (∀ i, 0 < representatives L p.2 i ∧ representatives L p.2 i < L) := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := torusPiMeasure L m)
    (ν := torusPiMeasure L m)).ae (QuantumNLS.BethePhysicalAssembly.torus_ae_injective L m)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := torusPiMeasure L m)
    (ν := torusPiMeasure L m)).ae (QuantumNLS.BethePhysicalAssembly.torus_ae_injective L m)
  have h3 := (Measure.quasiMeasurePreserving_fst (μ := torusPiMeasure L m)
    (ν := torusPiMeasure L m)).ae (ae_coord_ne_zero L m)
  have h4 := (Measure.quasiMeasurePreserving_snd (μ := torusPiMeasure L m)
    (ν := torusPiMeasure L m)).ae (ae_coord_ne_zero L m)
  have h5 := ae_noTie L m
  filter_upwards [h1, h2, h3, h4, h5] with p a b c d e
  refine ⟨rep_injective L a, rep_injective L b, fun i j hij => e i j ?_,
    fun i => ⟨rep_pos L c i, (rep_bounds L p.1 i).2⟩,
    fun i => ⟨rep_pos L d i, (rep_bounds L p.2 i).2⟩⟩
  apply (AddCircle.equivIco L 0).injective
  exact Subtype.ext hij

end Good

/-! ### The kernel identity and the operator factorization -/

section Main

variable (L : ℝ) [Fact (0 < L)]

/-- `Σ_τ c · B(x, y∘τ)`: the weighted sum over input permutations of the sign-twisted resolvent kernel. -/
def Kfact (m : ℕ) (q z c : ℂ) : Kernel (torusPiMeasure L m) :=
  weightedKernel (fun _ : Equiv.Perm (Fin m) => c)
    (fun τ => permutedKernel L m (Bker L m q z) 1 τ)

/-- **The exact factorization of the actual DEF-048 averaged kernel, almost everywhere.** -/
theorem ae_kernel_identity (n : ℕ) (z : ℂ)
    (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1) :
    ∀ᵐ p ∂(torusPiMeasure L (n + 1)).prod (torusPiMeasure L (n + 1)),
      (compressedKernel L (n + 1) z).fn p =
        (Kfact L (n + 1) ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z
          ((((n + 1).factorial : ℂ)⁻¹) ^ 2 *
            (1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)))).fn p := by
  filter_upwards [ae_good L (n + 1)] with p hp
  obtain ⟨hX, hY, hnt, hXb, hYb⟩ := hp
  obtain ⟨x, y⟩ := p
  simp only at hX hY hnt hXb hYb
  set q : ℂ := (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) with hqdef
  rw [compressedKernel_fn, averagedRaw_eq L n z hq (representatives L x) (representatives L y)
    hX hY hnt hXb hYb]
  have hdet : (RkMat q z (representatives L x) (representatives L y)).det =
      ∑ τ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign τ : ℤˣ) : ℂ) *
        ∏ i, Rk q z (representatives L x i) (representatives L y (τ i)) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    simp [RkMat, Matrix.transpose_apply]
  rw [hdet, Finset.mul_sum]
  simp only [Kfact, weightedKernel, permutedKernel, Bker, Rtens]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  have hs : sgnDec (representatives L (coordPerm τ y)) =
      ((Equiv.Perm.sign τ : ℤˣ) : ℂ) * sgnDec (representatives L y) :=
    sgnDec_comp hY τ
  have hr : ∀ i, representatives L (coordPerm τ y) i = representatives L y (τ i) := fun i => rfl
  have h1 : (coordPerm (1 : Equiv.Perm (Fin (n + 1))) x : Fin (n + 1) → AddCircle L) = x := rfl
  simp only [hr, h1, hs]
  ring

theorem physPerm_one {N : ℕ} (f : L2TN L N) : physPerm (1 : Equiv.Perm (Fin N)) f = f := by
  apply Lp.ext
  filter_upwards [coeFn_physPerm (1 : Equiv.Perm (Fin N)) f] with x hx
  exact hx

/-- **Operator-level exact factorization** (`QG:eq:haar-kernel-factorization`), for the actual `P_r(K⁺+K⁻)P_r`:
for every `F ∈ L²(𝕋_L^r)` and `q = ρ_r e^{izL} ≠ 1`,
`(P_r(K⁺+K⁻)P_r) F = (1−q)/r! · S R_z^{⊗r} S (P_r F)`. -/
theorem compressed_operator_eq (n : ℕ) (z : ℂ)
    (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1) (f : L2TN L (n + 1)) :
    (compressedKernel L (n + 1) z).operator f =
      ((1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) / ((n + 1).factorial : ℂ)) •
        Sop L (n + 1) ((Rtens L (n + 1) ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z).operator
          (Sop L (n + 1) (positionAverage L (n + 1) f))) := by
  set q : ℂ := (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) with hqdef
  set c : ℂ := (((n + 1).factorial : ℂ)⁻¹) ^ 2 * (1 - q) with hc
  have h1 := operator_congr_ae (compressedKernel L (n + 1) z)
    (Kfact L (n + 1) q z c) (ae_kernel_identity L n z hq)
  rw [h1]
  unfold Kfact
  rw [weightedKernel_operator]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, permutedKernel_operator,
    physPerm_one]
  have hB : (Bker L (n + 1) q z).operator =
      (Sop L (n + 1)).comp ((Rtens L (n + 1) q z).operator.comp (Sop L (n + 1))) :=
    Bker_operator L (n + 1) q z
  have hsum : ∑ τ : Equiv.Perm (Fin (n + 1)), physPerm τ.symm f =
      ∑ σ : Equiv.Perm (Fin (n + 1)), physPerm σ f := by
    exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun τ => rfl)
  have hpos : ∑ σ : Equiv.Perm (Fin (n + 1)), physPerm σ f =
      ((n + 1).factorial : ℂ) • positionAverage L (n + 1) f := by
    unfold positionAverage
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_smul]
    have hne : ((n + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    rw [mul_inv_cancel₀ hne, one_smul]; rfl
  calc ∑ τ : Equiv.Perm (Fin (n + 1)), c • (Bker L (n + 1) q z).operator (physPerm τ.symm f)
      = c • (Bker L (n + 1) q z).operator (∑ τ : Equiv.Perm (Fin (n + 1)), physPerm τ.symm f) := by
        rw [map_sum, Finset.smul_sum]
    _ = c • (Bker L (n + 1) q z).operator (((n + 1).factorial : ℂ) • positionAverage L (n + 1) f) := by
        rw [hsum, hpos]
    _ = _ := by
        rw [map_smul, hB, smul_smul]
        have hne : ((n + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
        congr 1
        rw [hc]; field_simp

#print axioms ae_kernel_identity
#print axioms compressed_operator_eq

end Main

end QuantumNLS.HaarKernelFactorizationOp
