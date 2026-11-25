import QuantumNLS.Prop022FactorialCoefficientsR115
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Real calculus for the actual completed tensor powers and finite-rank
contractions. Infinite Hessian identification is a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
open scoped InnerProductSpace ComplexConjugate Topology ContDiff
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022TensorCalculusR116
open TensorCarrier PhysicalTensor IntrinsicContact BetheCoefficientTransform
open Prop022TensorCompressionR115 Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup
local instance (n : ℕ) : AddCommGroup (HilbertTensorPower ℂ (L2T L) n) :=
  (inferInstance : NormedAddCommGroup (HilbertTensorPower ℂ (L2T L) n)).toAddCommGroup

/-- The elementary tensor map into the actual Hilbert completion. -/
def tensorMultilinear (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => L2T L) (HilbertTensorPower ℂ (L2T L) n) :=
  ((UniformSpace.Completion.toComplL : AlgTensorPower ℂ (L2T L) n →L[ℂ]
    HilbertTensorPower ℂ (L2T L) n).toLinearMap.compMultilinearMap
      (PiTensorProduct.tprod ℂ)).mkContinuous 1 (by
        intro v
        change ‖((ptprod v : AlgTensorPower ℂ (L2T L) n) :
          HilbertTensorPower ℂ (L2T L) n)‖ ≤ _
        simp [UniformSpace.Completion.norm_coe, norm_ptprod])

lemma tensorMultilinear_apply (n : ℕ) (v : Fin n → L2T L) :
    tensorMultilinear n v = ((ptprod v : AlgTensorPower ℂ (L2T L) n) :
      HilbertTensorPower ℂ (L2T L) n) := rfl

lemma htpow_smooth (n : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (fun u : L2T L => (htpow n u : HilbertTensorPower ℂ (L2T L) n)) := by
  change ContDiff ℝ k (fun u => ((tensorMultilinear (L := L) n).restrictScalars ℝ) (fun _ => u))
  exact ((tensorMultilinear (L := L) n).restrictScalars ℝ).contDiff.comp
    (contDiff_pi.mpr (fun _ => contDiff_id))

/-- The real differential, before identifying the symmetric slot sum. -/
def powerDifferential (n : ℕ) (u : L2T L) :
    L2T L →L[ℝ] HilbertTensorPower ℂ (L2T L) n :=
  ∑ i : Fin n, ((tensorMultilinear (L := L) n).restrictScalars ℝ).toContinuousLinearMap
    (fun _ => u) i

lemma htpow_hasFDerivAt (n : ℕ) (u : L2T L) :
    HasFDerivAt (fun v : L2T L => (htpow n v : HilbertTensorPower ℂ (L2T L) n))
      (powerDifferential n u) u := by
  change HasFDerivAt (fun v => ((tensorMultilinear (L := L) n).restrictScalars ℝ) (fun _ => v))
    (powerDifferential n u) u
  simpa +instances only [powerDifferential, comp_id, id_eq] using
    (HasFDerivAt.multilinear_comp (f := (tensorMultilinear (L := L) n).restrictScalars ℝ)
      (fun _ : Fin n => hasFDerivAt_id u))

lemma power_smooth (n : ℕ) (k : ℕ∞ω) : ContDiff ℝ k (power (L := L) n) := by
  have heq : power (L := L) n = fun u =>
      (physSector L n).orthogonalProjectionOnto (htpow n u) := by
    funext u
    exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (power n u)).symm
  rw [heq]
  exact ((physSector L n).orthogonalProjectionOnto.restrictScalars ℝ).contDiff.comp
    (htpow_smooth n k)

/-- Tensoring on the left is continuous in operator norm. -/
def tensorLeft {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    E →L[ℂ] F →L[ℂ] HilbertTensor ℂ E F :=
  LinearMap.mkContinuous
    { toFun := htmulR
      map_add' := by intro x y; ext z; exact htmul_add_left x y z
      map_smul' := by intro c x; ext z; exact htmul_smul_left c x z }
    1 (by
      intro x
      change ‖htmulR x‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact opNorm_le_bound _ (norm_nonneg x) (fun y => by
        change ‖htmul x y‖ ≤ ‖x‖ * ‖y‖
        exact (norm_htmul x y).le))

lemma tensorLeft_smooth {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (q : ℕ∞ω) :
    ContDiff ℝ q (tensorLeft (E := E) (F := F)) := by
  have hc : ContDiff ℂ q (tensorLeft (E := E) (F := F)) := by
    exact ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := E)
      (F := F →L[ℂ] HilbertTensor ℂ E F) (n := q) (tensorLeft (E := E) (F := F))
  exact hc.restrict_scalars ℝ

section ComplexOperators
variable {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma smooth_comp {q : ℕ∞ω} {g : X → F →L[ℂ] G} {f : X → E →L[ℂ] F}
    (hg : ContDiff ℝ q g) (hf : ContDiff ℝ q f) :
    ContDiff ℝ q (fun x => (g x).comp (f x)) := by
  have hc : ContDiff ℂ q (fun p : (F →L[ℂ] G) × (E →L[ℂ] F) => p.1.comp p.2) :=
    isBoundedBilinearMap_comp.contDiff
  exact (hc.restrict_scalars ℝ).comp₂ hg hf

lemma smooth_apply {q : ℕ∞ω} {f : X → E →L[ℂ] F} {g : X → E}
    (hf : ContDiff ℝ q f) (hg : ContDiff ℝ q g) :
    ContDiff ℝ q (fun x => f x (g x)) := by
  have hc : ContDiff ℂ q (fun p : (E →L[ℂ] F) × E => p.1 p.2) :=
    isBoundedBilinearMap_apply.contDiff
  exact (hc.restrict_scalars ℝ).comp₂ hf hg
end ComplexOperators

/-- The adjoint operation is real linear and continuous. -/
def realAdjoint {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    (E →L[ℂ] F) →L[ℝ] (F →L[ℂ] E) :=
  let a : (E →L[ℂ] F) →+ (F →L[ℂ] E) :=
    { toFun := fun T => T.adjoint
      map_zero' := adjoint.map_zero
      map_add' := fun T S => adjoint.map_add T S }
  a.toRealLinearMap (by exact (adjoint (𝕜 := ℂ) (E := E) (F := F)).continuous)

lemma insertion_smooth (r k : ℕ) (q : ℕ∞ω) :
    ContDiff ℝ q (insertion (L := L) r k) := by
  have ht := (tensorLeft_smooth (E := HilbertTensorPower ℂ (L2T L) r)
    (F := HilbertTensorPower ℂ (L2T L) k) q).comp (htpow_smooth (L := L) r q)
  unfold insertion
  exact smooth_comp contDiff_const (smooth_comp contDiff_const
    (smooth_comp ht contDiff_const))

lemma mixedTerm_smooth (B : ∀ m, HN L m →L[ℂ] HN L m) (r : ℕ) (q : ℕ∞ω) :
    ContDiff ℝ q (mixedTerm B · r) := by
  have hi := insertion_smooth (L := L) r 1 q
  have hadj := realAdjoint.contDiff.comp hi
  unfold mixedTerm
  exact (smooth_comp hadj (smooth_comp contDiff_const hi)).const_smul _

lemma pairTerm_smooth (B : ∀ m, HN L m →L[ℂ] HN L m) (r : ℕ) (q : ℕ∞ω) :
    ContDiff ℝ q (Prop022TensorCompressionR115.pairTerm B · r) := by
  have hi := insertion_smooth (L := L) r 2 q
  have hadj := realAdjoint.contDiff.comp hi
  unfold Prop022TensorCompressionR115.pairTerm
  exact (smooth_apply hadj (((B (r+2)).restrictScalars ℝ).contDiff.comp
    (power_smooth (r+2) q))).const_smul _

/-- The actual rank-m classical polynomial, viewed over the reals. -/
def classicalTerm (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ) (u : L2T L) : ℝ :=
  (⟪power m u, B m (power m u)⟫_ℂ).re

lemma classicalTerm_smooth (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ) (q : ℕ∞ω) :
    ContDiff ℝ q (classicalTerm B m) := by
  exact Complex.reCLM.contDiff.comp ((power_smooth m q).inner ℂ
    (((B m).restrictScalars ℝ).contDiff.comp (power_smooth m q)))

/-- Actual coefficient continuity follows from the factorial majorants;
no coefficient continuity is an input. -/
lemma numberCoefficient_time_continuous (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (u : ℝ → L2T L) (hu : Continuous u) (hn : ∀ t, ‖u t‖ = 1) :
    Continuous (fun t => numberCoefficient B (u t)) := by
  unfold numberCoefficient
  apply continuous_tsum (fun r => (mixedTerm_smooth B r 0).continuous.comp hu)
    ((number_summable A hA).mul_left M)
  intro r t
  exact mixed_dominated B M A hB (u t) (hn t) r

lemma pairCoefficient_time_continuous (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (u : ℝ → L2T L) (hu : Continuous u) (hn : ∀ t, ‖u t‖ = 1) :
    Continuous (fun t => pairCoefficient B (u t)) := by
  unfold pairCoefficient
  apply continuous_tsum (fun r => (pairTerm_smooth B r 0).continuous.comp hu)
    ((Prop022FactorialMajorantR115.pair_summable A hA).mul_left M)
  intro r t
  exact pair_dominated B M A hB (u t) (hn t) r

end QuantumNLS.Prop022TensorCalculusR116
#print axioms QuantumNLS.Prop022TensorCalculusR116.htpow_hasFDerivAt
#print axioms QuantumNLS.Prop022TensorCalculusR116.classicalTerm_smooth
#print axioms QuantumNLS.Prop022TensorCalculusR116.numberCoefficient_time_continuous
#print axioms QuantumNLS.Prop022TensorCalculusR116.pairCoefficient_time_continuous

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022TensorCalculusR116." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022TensorCalculusR116." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R116 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
