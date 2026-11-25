import QuantumNLS.RootH1RatioAC
import QuantumNLS.RootDiscriminantL1
import QuantumNLS.RiccatiFloquet

/-! Floquet comparison with an absolutely continuous Riccati ratio and L¹ input. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer
  QuantumNLS.RootH1RatioAC QuantumNLS.RootDiscriminant
namespace QuantumNLS.RootH1RatioFloquet
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance rootH1RatioFloquetPseudoMetrizable : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance rootH1RatioFloquetENormed : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

/-- The companion comparison at exactly the rough regularity used in the printed proof. -/
theorem trace_ratio {L κ Y : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ) {f r : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 L) (hr : AbsolutelyContinuousOnInterval r 0 L)
    (hper : r L = r 0)
    (hd : ∀ᵐ t ∂volume.restrict (Icc 0 L),
      HasDerivAt r (f t-(Y:ℂ)*r t-(κ:ℂ)*conj (f t)*(r t)^2) t) :
    Matrix.trace (transfer (balCoef κ f ((Y:ℂ)*Complex.I)) L) =
      Complex.exp ((Y:ℂ)*L/2+(κ:ℂ)*(∫ t in (0:ℝ)..L, conj (f t)*r t)) +
      (Complex.exp ((Y:ℂ)*L/2+(κ:ℂ)*(∫ t in (0:ℝ)..L, conj (f t)*r t)))⁻¹ := by
  let A := balCoef κ f ((Y:ℂ)*Complex.I)
  let M := transfer A
  have hA : IntervalIntegrable A volume 0 L := L2SpatialTransfer.intervalIntegrable_coef hf _ _ _
  have hM := fundamental_spec hL.le hA
  have hc : ContinuousOn r (uIcc 0 L) := hr.continuousOn
  have hfc : IntervalIntegrable (fun t => conj (f t)) volume 0 L :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hf.2⟩
  have hfr := hfc.mul_continuousOn hc
  let a : ℝ → ℂ := fun t => (Y:ℂ)/2+(κ:ℂ)*(conj (f t)*r t)
  have ha : IntervalIntegrable a volume 0 L := by
    simpa only [a] using (intervalIntegrable_const (c := (Y:ℂ)/2)).add (hfr.const_mul (κ:ℂ))
  let e : ℝ → ℂ := fun t => Complex.exp (∫ s in (0:ℝ)..t, a s)
  have heAC : AbsolutelyContinuousOnInterval e 0 L := ac_exp (ac_integral ha)
  have heD : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt e (a t*e t) t := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [ha.ae_hasDerivAt_integral] with t ht htL
    have hd := (ht (by simpa [uIcc_of_le hL.le] using htL) 0 (by simp)).cexp
    simpa only [e, mul_comm] using hd
  let C : ℝ → Mat2 := fun t => !![1,0; (Real.sqrt κ:ℂ)*r t,0]
  let V : ℝ → Mat2 := fun t => e t • C t
  let E0 : Mat2 := !![1,0;0,0]
  let E1 : Mat2 := !![0,0;1,0]
  have hVeq : V = fun t => e t • E0 + ((Real.sqrt κ:ℂ)*r t*e t) • E1 := by
    funext t
    ext i j
    fin_cases i <;> fin_cases j <;> simp [V,C,E0,E1]; ring
  have hVAC : AbsolutelyContinuousOnInterval V 0 L := by
    rw [hVeq]
    have hcreal := hr.const_smul (Real.sqrt κ:ℂ)
    exact (heAC.smul (LipschitzWith.const E0).lipschitzOnWith.absolutelyContinuousOnInterval).add
      ((hcreal.smul heAC).smul (LipschitzWith.const E1).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hVD : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt V (A t*V t) t := by
    filter_upwards [hd,heD] with t hrd hed
    have hr2 := (hrd.const_mul (Real.sqrt κ:ℂ)).mul hed
    have hvd := (hed.smul_const E0).add (hr2.smul_const E1)
    change HasDerivAt (fun s => e s • E0 + ((Real.sqrt κ:ℂ)*r s*e s) • E1) _ t at hvd
    rw [← hVeq] at hvd
    apply hvd.congr_deriv
    have hI : Complex.I*((Y:ℂ)*Complex.I) = -(Y:ℂ) := by
      linear_combination (Y:ℂ)*Complex.I_mul_I
    have hs : (Real.sqrt κ:ℂ)^2 = (κ:ℂ) := by exact_mod_cast Real.sq_sqrt hκ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A,a,V,C,E0,E1,balCoef,coef,Matrix.mul_apply,Fin.sum_univ_two,hI] <;>
      first | (solve | ring) | linear_combination -(conj (f t)*e t*r t)*hs
  let D : ℝ → Mat2 := fun t => M t*C 0 - V t
  have hDAC : AbsolutelyContinuousOnInterval D 0 L := by
    let T : Mat2 →L[ℝ] Mat2 := ContinuousLinearMap.mulLeftRight ℝ Mat2 1 (C 0)
    have ht := T.lipschitzWith.comp_absolutelyContinuousOnInterval hM.2.1
    change AbsolutelyContinuousOnInterval (fun t => T (M t)) 0 L at ht
    have heq : (fun t => T (M t)) = (fun t => M t*C 0) := by
      funext t
      change (1:Mat2)*M t*C 0 = M t*C 0
      rw [one_mul]
    rw [heq] at ht
    exact ht.sub hVAC
  have hDD : ∀ᵐ t ∂volume.restrict (Icc 0 L), HasDerivAt D (A t*D t) t := by
    filter_upwards [hM.2.2.1,hVD] with t hmd hvd
    apply ((hmd.mul_const (C 0)).sub hvd).congr_deriv
    simp only [D,M,mul_sub,mul_assoc]
  have hD0 : D 0 = 0 := by
    have hm0 : M 0 = 1 := hM.1
    simp [D,hm0,V,e]
  have hAD : IntervalIntegrable (fun t => A t*D t) volume 0 L := hA.mul_continuousOn hDAC.continuousOn
  have hDeq : ∀ x ∈ Icc (0:ℝ) L, D x = ∫ t in (0:ℝ)..x, A t*D t := by
    intro x hx
    simpa only [hD0,zero_add] using ac_integral_eq hL.le hDAC hAD hDD hx
  have hDL := eq_zero_of_integral hL.le hA
    (by simpa [uIcc_of_le hL.le] using hDAC.continuousOn) hDeq L ⟨hL.le,le_rfl⟩
  have hCper : C L = C 0 := by simp only [C,hper]
  have hEq : M L*C 0 = e L • C 0 := by
    have heq := sub_eq_zero.mp hDL
    simpa only [D,V,hCper] using heq
  have hmv : Matrix.mulVec (M L-e L • (1:Mat2)) ![1,(Real.sqrt κ:ℂ)*r 0] = 0 := by
    funext i
    have hh := congrFun (congrFun hEq i) 0
    fin_cases i <;>
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,C,Matrix.mul_apply,
        Matrix.one_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at hh ⊢ <;>
      linear_combination hh
  have hv0 : (![1,(Real.sqrt κ:ℂ)*r 0] : Fin 2 → ℂ) ≠ 0 := by
    intro hh
    have h0 := congrFun hh 0
    simp at h0
  have heig : (M L-e L • (1:Mat2)).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_,hv0,hmv⟩
  have hdet : (M L).det = 1 := RootDiscriminantL1.det_transfer hL.le hf κ _ ⟨hL.le,le_rfl⟩
  have htrace := RiccatiFloquet.trace_eq_of_det_one_eigen (M L) hdet (e L)
    (Complex.exp_ne_zero _) heig
  have heL : e L = Complex.exp ((Y:ℂ)*L/2+(κ:ℂ)*(∫ t in (0:ℝ)..L, conj (f t)*r t)) := by
    dsimp [e,a]
    rw [intervalIntegral.integral_add intervalIntegrable_const (hfr.const_mul (κ:ℂ))]
    rw [intervalIntegral.integral_const]
    simp only [sub_zero,Complex.real_smul]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    ring
  simpa only [M,A,heL] using htrace

#print axioms trace_ratio
end QuantumNLS.RootH1RatioFloquet

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioFloquet." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioFloquet." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
