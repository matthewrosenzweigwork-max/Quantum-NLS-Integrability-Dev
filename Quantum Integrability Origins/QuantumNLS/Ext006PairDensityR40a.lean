import QuantumNLS.Ext006CanonicalExponentialR39a
import QuantumNLS.Ext006InverseSourceR36a
import QuantumNLS.TraceNormTopology

/-! The actual operator square as a reduced density of the ADJOINT matrix
pair tensor. All conjugations are explicit; no trace or norm equality is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped InnerProductSpace ENNReal
open Filter Topology
namespace QuantumNLS.Ext006PairDensityR40a
open TensorCarrier TraceClass Ext006PairTensor Ext006KernelHilbertSchmidt
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def tensorLeft (x : H) : H →L[ℂ] HilbertTensor ℂ H H :=
  LinearMap.mkContinuous
    { toFun := fun y => htmul x y
      map_add' := htmul_add_right x
      map_smul' := fun c y => htmul_smul_right c x y }
    ‖x‖ (fun y => (norm_htmul x y).le)

def contract (x : H) : HilbertTensor ℂ H H →L[ℂ] H := (tensorLeft x).adjoint

lemma inner_contract (x y : H) (v : HilbertTensor ℂ H H) :
    inner ℂ y (contract x v) = inner ℂ (htmul x y) v :=
  ContinuousLinearMap.adjoint_inner_right (tensorLeft x) y v

lemma contract_htmul (x u v : H) : contract x (htmul u v) = inner ℂ x u • v := by
  apply ext_inner_left ℂ
  intro z
  rw [inner_contract, inner_htmul, inner_smul_right, mul_comm]

lemma map_rankOne (x y : H) :
    htmap (InnerProductSpace.rankOne ℂ y x) (ContinuousLinearMap.id ℂ H) =
      (tensorLeft y) ∘L contract x := by
  apply ContinuousLinearMap.ext
  intro v
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (htmap _ _).continuous ((tensorLeft y) ∘L contract x).continuous
  | ih a =>
    induction a using TensorProduct.inductionOn with
    | tmul u v =>
      change htmap _ _ (htmul u v) = tensorLeft y (contract x (htmul u v))
      rw [htmap_htmul, InnerProductSpace.rankOne_apply, ContinuousLinearMap.id_apply,
        contract_htmul]
      change htmul (inner ℂ x u • y) v = htmul y (inner ℂ x u • v)
      rw [htmul_smul_left, htmul_smul_right]
    | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

lemma density_inner (v : HilbertTensor ℂ H H) (x y : H) :
    inner ℂ (reducedDensity v x) y = inner ℂ (contract y v) (contract x v) := by
  rw [inner_reducedDensity_left, map_rankOne, ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_left (tensorLeft y) (contract x v) v).symm

lemma contract_adjoint_pair (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H)
    (hHS : hsSq b K ≠ ⊤) (i : ι) :
    contract (b i) (pairTensor b K.adjoint
      (by rwa [← hsSq_eq_hsSq_adjoint b b])) = conjugation b (K (b i)) := by
  apply b.repr.injective
  apply lp.ext
  funext j
  rw [HilbertBasis.repr_apply_apply, inner_contract, pairTensor_coefficient]
  rw [conjugation_apply, LinearIsometryEquiv.apply_symm_apply, lp.star_apply,
    HilbertBasis.repr_apply_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]
  simpa only [Complex.star_def] using (inner_conj_symm (K (b i)) (b j)).symm

omit [CompleteSpace H] in
lemma operator_ext_basis (b : HilbertBasis ι ℂ H) (T U : H →L[ℂ] H)
    (h : ∀ i, T (b i) = U (b i)) : T = U := by
  ext x
  have ht := T.hasSum (b.hasSum_repr x)
  have hu := U.hasSum (b.hasSum_repr x)
  simp only [map_smul, h] at ht
  simp only [map_smul] at hu
  exact ht.unique hu

/-- Exact actual operator identity; the adjoint pair gives K* K. -/
theorem reducedDensity_adjoint_pair (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H)
    (hHS : hsSq b K ≠ ⊤) :
    reducedDensity (pairTensor b K.adjoint (by rwa [← hsSq_eq_hsSq_adjoint b b])) =
      K.adjoint ∘L K := by
  apply operator_ext_basis b
  intro i
  apply b.repr.injective
  apply lp.ext
  funext j
  simp only [HilbertBasis.repr_apply_apply]
  rw [← inner_conj_symm (b j), density_inner, contract_adjoint_pair b K hHS j,
    contract_adjoint_pair b K hHS i, Ext006InverseSourceR36a.conjugation_inner]
  simp only [Complex.star_def]
  rw [inner_conj_symm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_conj_symm]

/-- Square finite-mode approximants to the adjoint matrix tensor. -/
def finiteAdjointPair (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H) (S : Finset ι) :
    HilbertTensor ℂ H H :=
  ∑ i ∈ S, ∑ j ∈ S, inner ℂ (b i) (K.adjoint (b j)) • htmul (b i) (b j)

lemma finiteAdjointPair_tendsto (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H)
    (hHS : hsSq b K ≠ ⊤) :
    Tendsto (finiteAdjointPair b K) atTop
      (𝓝 (pairTensor b K.adjoint (by rwa [← hsSq_eq_hsSq_adjoint b b]))) := by
  have ht := ((htmulBasis b b).hasSum_repr
    (pairTensor b K.adjoint (by rwa [← hsSq_eq_hsSq_adjoint b b]))).comp
      (Ext006PhysicalApproximationR38a.square_tendsto_atTop (ι := ι))
  simp only [HilbertBasis.repr_apply_apply, htmulBasis_apply, pairTensor_coefficient] at ht
  apply ht.congr'
  filter_upwards [] with S
  exact Finset.sum_product S S
    (fun p => inner ℂ (b p.1) (K.adjoint (b p.2)) • htmul (b p.1) (b p.2))

/-- Trace-norm convergence of the finite reduced densities to the actual K* K. -/
theorem density_traceNorm_tendsto (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H)
    (hHS : hsSq b K ≠ ⊤) :
    Tendsto (fun S : Finset ι => traceNorm
      (reducedDensity (finiteAdjointPair b K S) - K.adjoint ∘L K)) atTop (𝓝 0) := by
  let v := pairTensor b K.adjoint (by rwa [← hsSq_eq_hsSq_adjoint b b] : hsSq b K.adjoint ≠ ⊤)
  have ht : Tendsto (finiteAdjointPair b K) atTop (𝓝 v) := finiteAdjointPair_tendsto b K hHS
  have hb : Tendsto (fun S : Finset ι => ENNReal.ofReal
      (‖finiteAdjointPair b K S - v‖ * (‖finiteAdjointPair b K S‖ + ‖v‖))) atTop (𝓝 0) := by
    have hz := ((ht.sub (tendsto_const_nhds (x := v))).norm.mul
      (ht.norm.add (tendsto_const_nhds (x := ‖v‖))))
    simpa only [Function.comp_def, sub_self, norm_zero, zero_mul, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto _).comp hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le) (fun S => ?_)
  rw [← reducedDensity_adjoint_pair b K hHS]
  exact traceNorm_reducedDensity_sub_le _ _

end QuantumNLS.Ext006PairDensityR40a
#print axioms QuantumNLS.Ext006PairDensityR40a.reducedDensity_adjoint_pair
#print axioms QuantumNLS.Ext006PairDensityR40a.density_traceNorm_tendsto

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PairDensityR40a." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Round40a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
