import NlsGge.Analysis.RegularizedDeterminant.RealHilbertSchmidt
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Explicit synthesis of a bounded real-linear operator from square-summable
columns.  This proves completeness and finite-rank density for arbitrary real
Hilbert spaces; finite subsets, not an enumeration of the basis, index the
approximants.  No countability assumption is introduced.
-/
set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators Topology

namespace NlsGge.Analysis.RegularizedDeterminant

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Norms of l2 columns, as an actual real l2 sequence. -/
def columnNorms {I G : Type*} [NormedAddCommGroup G]
    (y : lp (fun _ : I => G) 2) : lp (fun _ : I => ℝ) 2 :=
  Subtype.mk (fun i => norm (y i)) (lp.memℓp y).norm

@[simp] theorem columnNorms_apply {I G : Type*} [NormedAddCommGroup G]
    (y : lp (fun _ : I => G) 2) (i : I) : columnNorms y i = norm (y i) := rfl

theorem norm_columnNorms {I G : Type*} [NormedAddCommGroup G]
    (y : lp (fun _ : I => G) 2) : norm (columnNorms y) = norm y := by
  have hy := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) y
  have hz := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (columnNorms y)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hy hz
  have hz' : HasSum (fun i => norm (y i) ^ 2) (norm (columnNorms y) ^ 2) := by
    simpa only [columnNorms_apply, norm_norm] using hz
  have hsq := hy.unique hz'
  nlinarith [norm_nonneg y, norm_nonneg (columnNorms y)]

/-- The scalar-vector l2 estimate is reduced to the pinned same-fiber Holder API. -/
theorem column_holder {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) (x : E) :
    Summable (fun i => norm (b.repr x i) * norm (y i)) ∧
      tsum (fun i => norm (b.repr x i) * norm (y i)) ≤ norm x * norm y := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := lp.tsum_mul_le_mul_norm hp (b.repr x) (columnNorms y)
  simpa only [columnNorms_apply, norm_norm, norm_columnNorms,
    LinearIsometryEquiv.norm_map] using h

theorem synthesis_norm_summable {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) (x : E) :
    Summable (fun i => norm (b.repr x i • y i)) := by
  simpa only [norm_smul] using (column_holder b y x).1

theorem synthesis_summable {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) (x : E) :
    Summable (fun i => b.repr x i • y i) :=
  (synthesis_norm_summable b y x).of_norm

theorem synthesis_norm_bound {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) (x : E) :
    norm (tsum (fun i => b.repr x i • y i)) ≤ norm y * norm x := by
  calc
    norm (tsum (fun i => b.repr x i • y i))
        ≤ tsum (fun i => norm (b.repr x i • y i)) :=
      norm_tsum_le_tsum_norm (synthesis_norm_summable b y x)
    _ = tsum (fun i => norm (b.repr x i) * norm (y i)) := by
      apply tsum_congr
      intro i
      exact norm_smul _ _
    _ ≤ norm x * norm y := (column_holder b y x).2
    _ = norm y * norm x := mul_comm _ _

/-- Synthesis is linear in the input vector, with its convergence already proved. -/
def synthesisLinear {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) : E →ₗ[ℝ] F where
  toFun x := tsum (fun i => b.repr x i • y i)
  map_add' x z := by
    simp only [map_add, lp.coeFn_add, Pi.add_apply, add_smul]
    exact (synthesis_summable b y x).tsum_add (synthesis_summable b y z)
  map_smul' c x := by
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
    exact (synthesis_summable b y x).tsum_const_smul c

/-- The bound proves that the synthesized map is genuinely bounded. -/
def synthesis {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) : E →L[ℝ] F :=
  (synthesisLinear b y).mkContinuous (norm y) (synthesis_norm_bound b y)

@[simp] theorem synthesis_apply {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) (x : E) :
    synthesis b y x = tsum (fun i => b.repr x i • y i) := rfl

@[simp] theorem synthesis_basis {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) (j : I) : synthesis b y (b j) = y j := by
  classical
  rw [synthesis_apply, b.repr_self]
  simp [lp.single_apply, Pi.single_apply, ite_smul]

theorem synthesis_isHilbertSchmidt {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) : IsHilbertSchmidt (synthesis b y) := by
  apply isHilbertSchmidt_of_summable b
  simpa only [synthesis_basis] using (memLp_two_iff _).mp (lp.memℓp y)

namespace HilbertSchmidt

/-- A constructive inverse to the column realization. -/
def ofColumns {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) : HilbertSchmidt E F :=
  ofCLM (synthesis b y) (synthesis_isHilbertSchmidt b y)

@[simp] theorem toCLM_ofColumns {I : Type*} (b : HilbertBasis I ℝ E)
    (y : lp (fun _ : I => F) 2) : toCLM (ofColumns b y) = synthesis b y := rfl

@[simp] theorem columns_ofColumns (y : lp (fun _ : basisIndex E => F) 2) :
    columns (ofColumns (basis E) y) = y := by
  apply lp.ext
  funext i
  exact synthesis_basis (basis E) y i

@[simp] theorem ofColumns_columns (T : HilbertSchmidt E F) :
    ofColumns (basis E) (columns T) = T :=
  columns_injective (columns_ofColumns (columns T))

/-- Every l2 family is the column family of a unique HS bounded operator. -/
def columnsEquiv : HilbertSchmidt E F ≃ₗ[ℝ] lp (fun _ : basisIndex E => F) 2 where
  __ := columns
  invFun := ofColumns (basis E)
  left_inv := ofColumns_columns
  right_inv := columns_ofColumns

/-- The HS norm realizes the complete l2 norm without any totalization. -/
def columnsIsometry : HilbertSchmidt E F ≃ₗᵢ[ℝ] lp (fun _ : basisIndex E => F) 2 where
  __ := columnsEquiv
  norm_map' _ := rfl

instance instCompleteSpace : CompleteSpace (HilbertSchmidt E F) :=
  (columnsIsometry (E := E) (F := F)).toIsometryEquiv.completeSpace

/-- The operator norm is dominated by the genuine Hilbert--Schmidt norm. -/
theorem opNorm_le (T : HilbertSchmidt E F) : norm (toCLM T) ≤ norm T := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  have h : synthesis (basis E) (columns T) = toCLM T :=
    congrArg toCLM (ofColumns_columns T)
  rw [← h]
  exact synthesis_norm_bound (basis E) (columns T) x

/-- Forgetting the HS summability proof is a linear map. -/
def toCLMLinear : HilbertSchmidt E F →ₗ[ℝ] (E →L[ℝ] F) where
  toFun := toCLM
  map_add' := toCLM_add
  map_smul' := toCLM_smul

/-- HS convergence implies operator-norm convergence. -/
def toCLMContinuous : HilbertSchmidt E F →L[ℝ] (E →L[ℝ] F) :=
  toCLMLinear.mkContinuous 1 (fun T => by
    change norm (toCLM T) ≤ 1 * norm T
    simpa only [one_mul] using opNorm_le T)

/-- One nonzero column; its range is contained in the span of that column. -/
def columnOperator (i : basisIndex E) (y : F) : HilbertSchmidt E F := by
  classical
  exact ofColumns (basis E) (lp.single 2 i y)

@[simp] theorem columnOperator_apply (i : basisIndex E) (y : F) (x : E) :
    toCLM (columnOperator i y) x = (basis E).repr x i • y := by
  classical
  change tsum (fun j => (basis E).repr x j • (lp.single (E := fun _ : basisIndex E => F) 2 i y) j) = _
  simp [lp.single_apply, Pi.single_apply, smul_ite]

/-- Unconditional convergence of column operators in the HS norm. -/
theorem hasSum_columnOperators (T : HilbertSchmidt E F) :
    HasSum (fun i => columnOperator i (columns T i)) T := by
  classical
  have h := (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (columns T)).mapL
    (columnsIsometry (E := E) (F := F)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun i => ofColumns (basis E) (lp.single 2 i (columns T i)))
    (ofColumns (basis E) (columns T)) at h
  simpa only [ofColumns_columns, columnOperator] using h

/-- The standard finite-column approximant. -/
def finiteColumnApprox (T : HilbertSchmidt E F) (s : Finset (basisIndex E)) :
    HilbertSchmidt E F := s.sum (fun i => columnOperator i (columns T i))

theorem finiteColumnApprox_apply (T : HilbertSchmidt E F)
    (s : Finset (basisIndex E)) (x : E) :
    toCLM (finiteColumnApprox T s) x =
      s.sum (fun i => (basis E).repr x i • columns T i) := by
  classical
  unfold finiteColumnApprox
  have h := map_sum (toCLMLinear (E := E) (F := F))
    (fun i => columnOperator i (columns T i)) s
  change toCLM (s.sum (fun i => columnOperator i (columns T i))) =
    s.sum (fun i => toCLM (columnOperator i (columns T i))) at h
  rw [h]
  simp only [ContinuousLinearMap.sum_apply, columnOperator_apply]

/-- Finite rank means that the range of the actual linear map is finite dimensional. -/
def HasFiniteRank (T : E →L[ℝ] F) : Prop :=
  FiniteDimensional ℝ (LinearMap.range T.toLinearMap)

theorem finiteColumnApprox_finiteRank (T : HilbertSchmidt E F)
    (s : Finset (basisIndex E)) : HasFiniteRank (toCLM (finiteColumnApprox T s)) := by
  classical
  let W : Submodule ℝ F := Submodule.span ℝ (Set.range (fun i : s => columns T i))
  haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hW : LinearMap.range (toCLM (finiteColumnApprox T s)).toLinearMap ≤ W := by
    rintro z ⟨x, rfl⟩
    change toCLM (finiteColumnApprox T s) x ∈ W
    rw [finiteColumnApprox_apply]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span (Exists.intro (Subtype.mk i hi) rfl)
  let j : LinearMap.range (toCLM (finiteColumnApprox T s)).toLinearMap →ₗ[ℝ] W :=
    { toFun := fun z => Subtype.mk z.val (hW z.property)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : W => (z : F)) h
  exact FiniteDimensional.of_injective j hj

/-- This net theorem does not presuppose a countable Hilbert basis. -/
theorem tendsto_finiteColumnApprox (T : HilbertSchmidt E F) :
    Filter.Tendsto (finiteColumnApprox T) Filter.atTop (nhds T) :=
  hasSum_columnOperators T

theorem dense_finiteRank : Dense {T : HilbertSchmidt E F | HasFiniteRank (toCLM T)} := by
  intro T
  refine mem_closure_of_tendsto (tendsto_finiteColumnApprox T) (Filter.Eventually.of_forall ?_)
  intro s
  exact finiteColumnApprox_finiteRank T s

end HilbertSchmidt
end NlsGge.Analysis.RegularizedDeterminant
