import NlsGge.Sobolev.RectangularBasisChange
import Mathlib.Tactic

/-!
Real, rectangular Hilbert--Schmidt operators.  The carrier consists of actual
bounded real-linear maps whose columns are square summable.  Its norm is induced
from genuine l2, not a totalized real sum on all bounded operators.

Checkpoint20 source reuse: RectangularBasisEnergy and RectangularBasisChange.
All declarations in this submission are uncompiled proof candidates.
-/
set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators InnerProductSpace

namespace NlsGge.Analysis.RegularizedDeterminant

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- An internal index set; no separability assumption is imposed. -/
def basisIndex (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] : Set E :=
  Classical.choose (exists_hilbertBasis ℝ E)

/-- The internal real Hilbert basis used only to construct the carrier. -/
def basis (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] : HilbertBasis (basisIndex E) ℝ E :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℝ E))

/-- This energy, unlike a real-valued sum, detects divergence. -/
def energy (T : E →L[ℝ] F) : ℝ≥0∞ :=
  tsum (fun i => ENNReal.ofReal (norm (T (basis E i)) ^ 2))

/-- Hilbert--Schmidt membership is finite extended nonnegative energy. -/
def IsHilbertSchmidt (T : E →L[ℝ] F) : Prop := energy T ≠ ∞

theorem energy_eq_basis {I : Type*} (T : E →L[ℝ] F)
    (b : HilbertBasis I ℝ E) :
    energy T = tsum (fun i => ENNReal.ofReal (norm (T (b i)) ^ 2)) := by
  exact NlsGge.Pilot.ennreal_source_basis_energy_eq T (basis E) b (basis F)

theorem isHilbertSchmidt_of_summable {I : Type*} {T : E →L[ℝ] F}
    (b : HilbertBasis I ℝ E) (h : Summable (fun i => norm (T (b i)) ^ 2)) :
    IsHilbertSchmidt T := by
  unfold IsHilbertSchmidt
  rw [energy_eq_basis T b]
  exact h.tsum_ofReal_ne_top

theorem isHilbertSchmidt_iff_summable {I : Type*} (T : E →L[ℝ] F)
    (b : HilbertBasis I ℝ E) :
    IsHilbertSchmidt T ↔ Summable (fun i => norm (T (b i)) ^ 2) := by
  constructor
  · intro h
    have hf : (tsum (fun i => ENNReal.ofReal (norm (T (b i)) ^ 2))) ≠ ∞ := by
      rw [← energy_eq_basis T b]
      exact h
    have hnn : Summable (fun i => Real.toNNReal (norm (T (b i)) ^ 2)) := by
      apply ENNReal.tsum_coe_ne_top_iff_summable.mp
      simpa only [← ENNReal.ofNNReal_toNNReal] using hf
    have hr := NNReal.summable_coe.mpr hnn
    exact hr.congr (fun i => by
      simp [Real.coe_toNNReal', max_eq_left (sq_nonneg (norm (T (b i))))])
  · exact isHilbertSchmidt_of_summable b

theorem memLp_two_iff {I G : Type*} [NormedAddCommGroup G] (x : I → G) :
    Memℓp x 2 ↔ Summable (fun i => norm (x i) ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

/-- A submodule of bounded maps, with genuine column summability. -/
def hsSubmodule : Submodule ℝ (E →L[ℝ] F) where
  carrier := {T | Memℓp (fun i => T (basis E i)) 2}
  zero_mem' := by
    change Memℓp (fun _ : basisIndex E => (0 : F)) 2
    exact zero_memℓp
  add_mem' := by
    intro S T hS hT
    change Memℓp ((fun i => S (basis E i)) + (fun i => T (basis E i))) 2
    exact hS.add hT
  smul_mem' := by
    intro c T hT
    change Memℓp (c • (fun i => T (basis E i))) 2
    exact hT.const_smul c

/-- A type synonym prevents use of the inherited operator norm as the HS norm. -/
def HilbertSchmidt (E F : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] : Type _ :=
  hsSubmodule (E := E) (F := F)

namespace HilbertSchmidt

instance instAddCommGroup : AddCommGroup (HilbertSchmidt E F) :=
  inferInstanceAs (AddCommGroup (hsSubmodule (E := E) (F := F)))

instance instModule : Module ℝ (HilbertSchmidt E F) :=
  inferInstanceAs (Module ℝ (hsSubmodule (E := E) (F := F)))

/-- The actual bounded real-linear operator, not an abstract placeholder. -/
def toCLM (T : HilbertSchmidt E F) : E →L[ℝ] F := T.val

@[simp] theorem toCLM_zero : toCLM (0 : HilbertSchmidt E F) = 0 := rfl
@[simp] theorem toCLM_add (S T : HilbertSchmidt E F) :
    toCLM (S + T) = toCLM S + toCLM T := rfl
@[simp] theorem toCLM_smul (c : ℝ) (T : HilbertSchmidt E F) :
    toCLM (c • T) = c • toCLM T := rfl
@[simp] theorem toCLM_neg (T : HilbertSchmidt E F) : toCLM (-T) = -toCLM T := rfl
@[simp] theorem toCLM_sub (S T : HilbertSchmidt E F) :
    toCLM (S - T) = toCLM S - toCLM T := rfl

@[ext] theorem ext {S T : HilbertSchmidt E F}
    (h : forall x, toCLM S x = toCLM T x) : S = T := by
  apply Subtype.ext
  exact ContinuousLinearMap.ext h

theorem membership (T : HilbertSchmidt E F) : IsHilbertSchmidt (toCLM T) :=
  isHilbertSchmidt_of_summable (basis E) ((memLp_two_iff _).mp T.property)

/-- Package a bounded operator only after finite energy has been proved. -/
def ofCLM (T : E →L[ℝ] F) (h : IsHilbertSchmidt T) : HilbertSchmidt E F :=
  (show hsSubmodule (E := E) (F := F) from
    Subtype.mk T ((memLp_two_iff _).mpr
      ((isHilbertSchmidt_iff_summable T (basis E)).mp h)))

@[simp] theorem toCLM_ofCLM (T : E →L[ℝ] F) (h : IsHilbertSchmidt T) :
    toCLM (ofCLM T h) = T := rfl

/-- Column realization into actual l2. -/
def columns : HilbertSchmidt E F →ₗ[ℝ] lp (fun _ : basisIndex E => F) 2 where
  toFun T := Subtype.mk (fun i => toCLM T (basis E i)) T.property
  map_add' S T := by apply lp.ext; rfl
  map_smul' c T := by apply lp.ext; rfl

@[simp] theorem columns_apply (T : HilbertSchmidt E F) (i : basisIndex E) :
    columns T i = toCLM T (basis E i) := rfl

/-- Bounded maps with the same columns agree on every vector by Hilbert expansion. -/
theorem columns_injective : Function.Injective (columns (E := E) (F := F)) := by
  intro S T h
  have hi (i : basisIndex E) : toCLM S (basis E i) = toCLM T (basis E i) :=
    congrArg (fun y : lp (fun _ : basisIndex E => F) 2 => y i) h
  apply ext
  intro x
  have hS := ((basis E).hasSum_repr x).mapL (toCLM S)
  have hT := ((basis E).hasSum_repr x).mapL (toCLM T)
  have hS' : HasSum (fun i => (basis E).repr x i • toCLM T (basis E i))
      (toCLM S x) := by
    simpa only [map_smul, hi] using hS
  have hT' : HasSum (fun i => (basis E).repr x i • toCLM T (basis E i))
      (toCLM T x) := by
    simpa only [map_smul] using hT
  exact hS'.unique hT'

instance instNormedAddCommGroup : NormedAddCommGroup (HilbertSchmidt E F) :=
  NormedAddCommGroup.induced _ _ columns columns_injective

instance instNormedSpace : NormedSpace ℝ (HilbertSchmidt E F) where
  norm_smul_le c T := by
    change norm (columns (c • T)) ≤ norm c * norm (columns T)
    rw [map_smul]
    exact norm_smul_le c (columns T)

instance instInnerProductSpace : InnerProductSpace ℝ (HilbertSchmidt E F) :=
  InnerProductSpace.induced columns

@[simp] theorem norm_columns (T : HilbertSchmidt E F) : norm (columns T) = norm T := rfl

/-- The HS norm has a summable, not merely totalized, square-series formula. -/
theorem hasSum_columns_sq (T : HilbertSchmidt E F) :
    HasSum (fun i => norm (toCLM T (basis E i)) ^ 2) (norm T ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (columns T)
  change HasSum (fun i => norm (toCLM T (basis E i)) ^ (2 : ℝ≥0∞).toReal)
    (norm T ^ (2 : ℝ≥0∞).toReal) at h
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- Basis independence is proved over arbitrary real Hilbert bases. -/
theorem hasSum_basis_sq {I : Type*} (T : HilbertSchmidt E F)
    (b : HilbertBasis I ℝ E) :
    HasSum (fun i => norm (toCLM T (b i)) ^ 2) (norm T ^ 2) := by
  have h := NlsGge.Pilot.hasSum_norm_sq_apply_of_real_hilbertBasis
    (T := toCLM T) (basis E) b (hasSum_columns_sq T).summable
  rw [(hasSum_columns_sq T).tsum_eq] at h
  exact h

theorem energy_eq_norm_sq (T : HilbertSchmidt E F) :
    energy (toCLM T) = ENNReal.ofReal (norm T ^ 2) := by
  unfold energy
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (hasSum_columns_sq T).summable, (hasSum_columns_sq T).tsum_eq]

theorem norm_eq_sqrt_energy (T : HilbertSchmidt E F) :
    norm T = Real.sqrt (energy (toCLM T)).toReal := by
  rw [energy_eq_norm_sq, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg T)]

end HilbertSchmidt
end NlsGge.Analysis.RegularizedDeterminant
