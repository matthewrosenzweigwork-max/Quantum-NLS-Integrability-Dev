import QuantumNLS.Reg010LowPolynomial
import QuantumNLS.Reg010LowL4Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The actual continuous H^(1/3) to native L4 embedding, by finite Fourier approximation. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.Reg010LowEmbedding
open QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Reg010LowL4Space
variable {L : ℝ} [Fact (0<L)]

def embeddingConstant (L : ℝ) : ℝ :=
  (L⁻¹ * ∑' n : ℤ, (f04Weight L (1/3) n)^(-2:ℝ))^(1/4:ℝ)

theorem constant_nonneg : 0 ≤ embeddingConstant L := Real.rpow_nonneg (by
  exact mul_nonneg (inv_nonneg.mpr (Fact.out : 0<L).le)
    (tsum_nonneg (fun n => Real.rpow_nonneg (f04Weight_pos L (1/3) n).le _))) _

theorem constant_fourth : embeddingConstant L ^ 4 =
    L⁻¹ * ∑' n : ℤ, (f04Weight L (1/3) n)^(-2:ℝ) := by
  unfold embeddingConstant
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by
    exact mul_nonneg (inv_nonneg.mpr (Fact.out : 0<L).le)
      (tsum_nonneg (fun n => Real.rpow_nonneg (f04Weight_pos L (1/3) n).le _)))]
  norm_num

def truncCoeffs (u : H04sp L (1/3)) (J : Finset ℤ) (n : ℤ) : ℂ :=
  if n ∈ J then fourierL2 L u.val n else 0

theorem trunc_summable (u : H04sp L (1/3)) (J : Finset ℤ) :
    Summable (fun n => ‖truncCoeffs u J n‖) := by
  classical
  exact summable_of_ne_finset_zero (s := J) (fun n hn => by simp [truncCoeffs,hn])

theorem trunc_energy (u : H04sp L (1/3)) (J : Finset ℤ) :
    Mem04 L (1/3) (truncCoeffs u J) ∧ f04NormSq L (1/3) (truncCoeffs u J) ≤ ‖u‖^2 := by
  classical
  have hs : Summable (fun n => f04Weight L (1/3) n*‖truncCoeffs u J n‖^2) :=
    summable_of_ne_finset_zero (s := J) (fun n hn => by simp [truncCoeffs,hn])
  refine ⟨hs, ?_⟩
  rw [WField.norm_sq_eq_tsum L u]
  apply hs.tsum_le_tsum _ u.summable
  intro n
  change f04Weight L (1/3) n*‖truncCoeffs u J n‖^2 ≤
    f04Weight L (1/3) n*‖fourierL2 L u.val n‖^2
  by_cases hn : n∈J
  · simp [truncCoeffs,hn]
  · simpa [truncCoeffs,hn] using
      mul_nonneg (f04Weight_pos L (1/3) n).le (sq_nonneg ‖fourierL2 L u.val n‖)

def polynomial (u : H04sp L (1/3)) (J : Finset ℤ) : AddCircle L → ℂ :=
  seriesRep L (truncCoeffs u J)

theorem polynomial_memLp (u : H04sp L (1/3)) (J : Finset ℤ) :
    MemLp (polynomial u J) 4 (volume : Measure (AddCircle L)) := by
  have hc := continuous_seriesRep (L := L) (trunc_summable u J)
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C
    (ae_of_all _ (fun x => hC x (mem_univ x)))

theorem polynomial_norm_bound (u : H04sp L (1/3)) (J : Finset ℤ) :
    ‖(polynomial_memLp u J).toLp (polynomial u J)‖ ≤ embeddingConstant L*‖u‖ := by
  let v : L4T L := (polynomial_memLp u J).toLp (polynomial u J)
  have hv : ‖v‖^4 = ∫ x : AddCircle L, ‖polynomial u J x‖^4 := by
    rw [← fourth_integral v]
    exact integral_congr_ae (((polynomial_memLp u J).coeFn_toLp).fun_comp (fun z : ℂ => ‖z‖^4))
  have hb := QuantumNLS.Reg010LowPolynomial.fourth_sobolev_bound (L := L)
    (truncCoeffs u J) (trunc_summable u J) (trunc_energy u J).1
  have he := pow_le_pow_left₀ (tsum_nonneg (fun n =>
    mul_nonneg (f04Weight_pos L (1/3) n).le (sq_nonneg _))) (trunc_energy u J).2 2
  have hC : 0 ≤ L⁻¹*∑' n : ℤ,(f04Weight L (1/3) n)^(-2:ℝ) := by
    rw [← constant_fourth (L := L)]
    positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : 4≠0) (mul_nonneg constant_nonneg (norm_nonneg u))
  rw [mul_pow,constant_fourth, hv]
  exact hb.trans (by simpa only [f04NormSq, ← pow_mul, Nat.reduceMul] using mul_le_mul_of_nonneg_left he hC)

theorem polynomial_L2 (u : H04sp L (1/3)) (J : Finset ℤ) :
    (memLp_seriesRep (L := L) (trunc_summable u J)).toLp (polynomial u J) =
      ∑ n ∈ J, coeff L (u.val : AddCircle L → ℂ) n • modeLp L n := by
  classical
  apply (fourierL2 L).injective
  ext k
  unfold polynomial
  rw [fourierL2_apply, coeff_congr_ae L (MemLp.coeFn_toLp (memLp_seriesRep (L := L) (trunc_summable u J))), coeff_seriesRep (trunc_summable u J)]
  simp only [map_sum,map_smul,fourierL2_modeLp,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,
    Pi.smul_apply,lp.single_apply,Pi.single_apply,smul_eq_mul]
  by_cases hk : k∈J <;> simp [truncCoeffs,hk,fourierL2_apply]

theorem memLp_four (u : H04sp L (1/3)) :
    MemLp (u.val : AddCircle L → ℂ) 4 volume ∧
      eLpNorm u.val 4 volume ≤ ENNReal.ofReal (embeddingConstant L*‖u‖) := by
  have hlim : Tendsto (fun J : Finset ℤ =>
      (memLp_seriesRep (L := L) (trunc_summable u J)).toLp (polynomial u J)) atTop (𝓝 u.val) := by
    simp_rw [polynomial_L2]
    exact hasSum_coeff_smul_modeLp L u.val
  have hm := tendstoInMeasure_of_tendsto_Lp hlim
  have hm' : TendstoInMeasure volume (polynomial u) atTop u.val :=
    TendstoInMeasure.congr_left (fun J => (MemLp.coeFn_toLp _)) hm
  have he : eLpNorm u.val 4 volume ≤ ENNReal.ofReal (embeddingConstant L*‖u‖) := by
    refine eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall (fun J => ?_)) hm'
      (fun J => (polynomial_memLp u J).aestronglyMeasurable)
    have h := ENNReal.ofReal_le_ofReal (polynomial_norm_bound u J)
    rw [ofReal_norm, Lp.enorm_def,
      eLpNorm_congr_ae (MemLp.coeFn_toLp _)] at h
    exact h
  exact ⟨he.trans_lt ENNReal.ofReal_lt_top,he⟩

#print axioms constant_nonneg
#print axioms constant_fourth
#print axioms trunc_summable
#print axioms trunc_energy
#print axioms polynomial_memLp
#print axioms polynomial_norm_bound
#print axioms polynomial_L2
#print axioms memLp_four
end QuantumNLS.Reg010LowEmbedding

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowEmbedding." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowEmbedding." then
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
  Lean.logInfo m!"Round46 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
