import QuantumNLS.Prop022ActualProfileR117
import QuantumNLS.Ext006PairDensityR40a

/-! The pair tensor's actual Hilbert--Schmidt operator representative, in the
original one-particle complex structure, with its exact HS norm and report bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace ENNReal ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022PairHSR122
open TensorCarrier Ext006PairDensityR40a Ext006KernelHilbertSchmidt
open Ext006PhysicalNormBridge.PairTensor TraceClass
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] InnerProductSpace.complexToReal

lemma contract_add (x y : H) (v : HilbertTensor ℂ H H) :
    contract (x+y) v = contract x v + contract y v := by
  apply ext_inner_left ℂ
  intro z
  simp only [inner_contract, htmul_add_left, inner_add_left, inner_add_right]

lemma contract_smul (c : ℂ) (x : H) (v : HilbertTensor ℂ H H) :
    contract (c • x) v = conj c • contract x v := by
  apply ext_inner_left ℂ
  intro z
  simp only [inner_contract, htmul_smul_left, inner_smul_left, inner_smul_right]

lemma contract_bound (x : H) (v : HilbertTensor ℂ H H) :
    ‖contract x v‖ ≤ ‖x‖*‖v‖ := by
  have ht : ‖tensorLeft x‖ ≤ ‖x‖ :=
    opNorm_le_bound _ (norm_nonneg _) (fun y => (norm_htmul x y).le)
  exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (by simpa only [contract, adjoint.norm_map] using ht) (norm_nonneg _))

/-- The complex-linear representative of the intrinsic antilinear contraction.
The fixed conjugation is explicit; no change of complex structure occurs. -/
def tensorOperator (b : HilbertBasis ι ℂ H) (v : HilbertTensor ℂ H H) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun x := contract (conjugation b x) v
      map_add' x y := by rw [map_add, contract_add]
      map_smul' c x := by
        have hc : conjugation b (c • x) = conj c • conjugation b x := by
          simp only [conjugation_apply, map_smul, star_smul]
          rfl
        rw [hc, contract_smul, Complex.conj_conj]
        rfl }
    ‖v‖ (fun x => by
      change ‖contract (conjugation b x) v‖ ≤ ‖v‖*‖x‖
      simpa only [conjugation_norm, mul_comm] using contract_bound (conjugation b x) v)

lemma tensorOperator_matrix (b : HilbertBasis ι ℂ H) (v : HilbertTensor ℂ H H) (i j : ι) :
    inner ℂ (b i) (tensorOperator b v (b j)) = inner ℂ (htmul (b j) (b i)) v := by
  change inner ℂ (b i) (contract (conjugation b (b j)) v) = _
  rw [conjugation_basis, inner_contract]

/-- Parseval on the completed tensor product proves the HS norm equality. -/
theorem tensorOperator_hsSq (b : HilbertBasis ι ℂ H) (v : HilbertTensor ℂ H H) :
    hsSq b (tensorOperator b v) = ENNReal.ofReal (‖v‖^2) := by
  rw [← Ext006PairTensor.matrix_hsSq]
  simp only [tensorOperator_matrix]
  have ht := tsum_ofReal_norm_inner_sq (htmulBasis b b) v
  simp only [htmulBasis_apply] at ht
  calc
    _ = ∑' p : ι × ι, ENNReal.ofReal (‖inner ℂ (htmul (b p.1) (b p.2)) v‖^2) :=
      (Equiv.prodComm ι ι).tsum_eq _
    _ = _ := ht

open BetheCoefficientTransform PhysicalTensor Prop022FactorialCoefficientsR115
open Prop022FactorialMajorantR115 Prop022ActualProfileR117
variable {L : ℝ} [Fact (0 < L)]

/-- The actual pair kernel, constructed from the literal two-particle coefficient. -/
def pairKernel (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) : L2T L →L[ℂ] L2T L :=
  tensorOperator (physicalBasis L) (twoIso (pairCoefficient B u : HilbertTensorPower ℂ (L2T L) 2))

theorem pairKernel_hsSq (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :
    hsSq (physicalBasis L) (pairKernel B u) = ENNReal.ofReal (‖pairCoefficient B u‖^2) := by
  rw [pairKernel, tensorOperator_hsSq, LinearIsometryEquiv.norm_map]
  rfl

/-- Symmetry of the actual two-particle tensor is matrix symmetry of its
operator representative, in the original basis conjugation. -/
theorem pairKernel_symmetric (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (i j : ℤ) :
    inner ℂ (physicalBasis L i) (pairKernel B u (physicalBasis L j)) =
      inner ℂ (physicalBasis L j) (pairKernel B u (physicalBasis L i)) := by
  let v := twoIso (pairCoefficient B u : HilbertTensorPower ℂ (L2T L) 2)
  have hfix := (pairCoefficient B u).property (Equiv.swap (0 : Fin 2) 1)
  have hfix' : permHilbertIsometry (Equiv.swap (0 : Fin 2) 1)
      (pairCoefficient B u : HilbertTensorPower ℂ (L2T L) 2) = pairCoefficient B u := hfix
  have hf : htcommIsometry ℂ (L2T L) (L2T L) v = v := by
    exact (twoIso_swap _).symm.trans (congrArg twoIso hfix')
  have he := (htcommIsometry ℂ (L2T L) (L2T L)).inner_map_map
    (htmul (physicalBasis L i) (physicalBasis L j)) v
  rw [htcommIsometry_htmul, hf] at he
  simpa only [pairKernel, tensorOperator_matrix] using he

/-- Both printed coefficient bounds, including actual Hilbert--Schmidt finiteness.
The square root of the HS square is precisely the pair vector norm. -/
theorem PROP022_printed_coefficient_bounds_R122
    (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (t : ℝ) :
    let u := profile B M A hA hB hs u₀ t
    hsSq (physicalBasis L) (pairKernel B u) ≠ ⊤ ∧
    Real.sqrt ((hsSq (physicalBasis L) (pairKernel B u)).toReal) ≤ pairMajorant A*M ∧
    ‖numberCoefficient B u‖ ≤ M *
      ∑' r : ℕ, (((r+1 : ℕ) : ℝ)^2 * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ)) := by
  dsimp only
  rw [pairKernel_hsSq, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hu := (profile_spec B M A hA hB hs u₀).2.2.1 t
  refine ⟨ENNReal.ofReal_ne_top, ?_, ?_⟩
  · simpa only [mul_comm] using pairCoefficient_bound B M A hA hB _ hu
  · exact numberCoefficient_bound B M A hA hB _ hu

end QuantumNLS.Prop022PairHSR122
#print axioms QuantumNLS.Prop022PairHSR122.tensorOperator_hsSq
#print axioms QuantumNLS.Prop022PairHSR122.PROP022_printed_coefficient_bounds_R122

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022PairHSR122." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022PairHSR122." then
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
  Lean.logInfo m!"R122 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
