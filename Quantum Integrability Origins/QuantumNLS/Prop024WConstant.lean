import QuantumNLS.Prop024WSeries
import QuantumNLS.Prop022ClassicalTimeR116

/-! PROP-024 operator-level Wick expansion, module 8 (Prop024WConstant): the constant term.

`zeroKernelScalar_ck`: the scalar of the degree-(0,0) contraction is the classical symbol, `zeroKernelScalar (contractedKernel m 0 0 B u) = ⟨u^{⊗m}, B_m u^{⊗m}⟩`.  `constScalar_eq_classicalSeries`: for self-adjoint kernels the constant term of `Prop024WStepOne` is `N · classicalSeries B u` (the PROP-021/022 classical energy series), as a complex number. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
namespace QuantumNLS.Prop024WConstant
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022TensorCompressionR115 Prop024WBlock Prop024WSector Prop024WWords Prop024WOrder
open Prop024ContractionsR54 Prop024WSeries Prop022FactorialCoefficientsR115 Prop022ClassicalTimeR116 Prop022TensorCalculusR116
variable {L : ℝ} [Fact (0 < L)]

lemma physZero_power (u : L2T L) : PhysicalPlacements.physZeroSectorIso L (power 0 u) = 1 := by
  change zeroSectorIso (htpow 0 u : TP L 0) = 1
  exact zeroSectorIso_htpow u

lemma physZero_eq_inner (u : L2T L) (z : HN L 0) :
    PhysicalPlacements.physZeroSectorIso L z = ⟪power 0 u, z⟫_ℂ := by
  rw [← (PhysicalPlacements.physZeroSectorIso L).inner_map_map, physZero_power]
  simp

lemma zeroKernelScalar_eq_inner (u : L2T L) (A : HN L 0 →L[ℂ] HN L 0) :
    PhysicalPlacements.zeroKernelScalar L A = ⟪power 0 u, A (power 0 u)⟫_ℂ := by
  unfold PhysicalPlacements.zeroKernelScalar
  have : (PhysicalPlacements.physZeroSectorIso L).symm 1 = power 0 u :=
    (PhysicalPlacements.physZeroSectorIso L).symm_apply_eq.mpr (physZero_power u).symm
  rw [this, physZero_eq_inner u]

lemma insertSector_power_zero (m : ℕ) (u : L2T L) :
    insertSector m 0 (Nat.zero_le m) u (power 0 u) = power m u := by
  apply Subtype.ext
  have h := insertSector_coe m 0 (Nat.zero_le _) u (power 0 u)
  refine h.trans ?_
  unfold insertion
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Submodule.coe_orthogonalProjectionOnto_apply]
  change (physSector L (m+0)).starProjection ((splitIsometry (𝕜 := ℂ) (E := L2T L) m 0).symm
      (htmul (htpow m u) (htpow 0 u : TP L 0))) = (htpow m u : TP L m)
  have h1 : (splitIsometry (𝕜 := ℂ) (E := L2T L) m 0).symm (htmul (htpow m u) (htpow 0 u : TP L 0)) =
      htpow (m+0) u := by
    rw [LinearIsometryEquiv.symm_apply_eq, KernelDefinition.split_htpow]
  rw [h1]
  exact Submodule.starProjection_eq_self_iff.mpr (htpow_mem_symSector (m+0) u)

lemma zeroKernelScalar_ck (m : ℕ) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) :
    PhysicalPlacements.zeroKernelScalar L (ck m 0 0 (Nat.zero_le m) (Nat.zero_le m) Bm u) =
      ⟪power m u, Bm (power m u)⟫_ℂ := by
  rw [zeroKernelScalar_eq_inner u]
  unfold ck
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right, insertSector_power_zero]


lemma inner_self_adjoint_real {m : ℕ} (T : HN L m →L[ℂ] HN L m) (hT : T.adjoint = T) (x : HN L m) :
    ((⟪x, T x⟫_ℂ).re : ℂ) = ⟪x, T x⟫_ℂ := by
  rw [← Complex.conj_eq_iff_re, inner_conj_symm]
  rw [← ContinuousLinearMap.adjoint_inner_right, hT]

/-- **The constant term is `N F(u)`.**  For self-adjoint kernels, the series of the `(0,0)` cells
`constScalar N B u = N ∑_{m≥1} ⟨u^{⊗m}, B_m u^{⊗m}⟩` is `N` times the classical series
`classicalSeries B u = ∑_{m ≥ 1} Re ⟨u^{⊗m}, B_m u^{⊗m}⟩` of PROP-021/022. -/
theorem constScalar_eq_classicalSeries (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r)
    (hs : ∀ m, (B m).adjoint = B m) (u : L2T L) :
    constScalar N B u = (((N : ℝ) * classicalSeries B u : ℝ) : ℂ) := by
  unfold constScalar classicalSeries
  have h1 : ∀ m : ℕ, (N : ℂ) * PhysicalPlacements.zeroKernelScalar L
      (ck (m+1) 0 0 (Nat.zero_le _) (Nat.zero_le _) (B (m+1)) u) =
      (((N : ℝ) * classicalTerm B (m+1) u : ℝ) : ℂ) := by
    intro m
    rw [zeroKernelScalar_ck]
    unfold classicalTerm
    rw [Complex.ofReal_mul, inner_self_adjoint_real (B (m+1)) (hs (m+1))]
    simp
  rw [tsum_congr h1, ← Complex.ofReal_tsum, tsum_mul_left]

end QuantumNLS.Prop024WConstant

#print axioms QuantumNLS.Prop024WConstant.zeroKernelScalar_ck
#print axioms QuantumNLS.Prop024WConstant.constScalar_eq_classicalSeries

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WConstant." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WConstant." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Prop024WConstant aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
