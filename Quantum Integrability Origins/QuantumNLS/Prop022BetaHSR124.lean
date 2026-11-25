import QuantumNLS.Prop022SignedEnergyR124

/-! The quantitative Hilbert--Schmidt beta estimate follows from finite-column
energy inequalities. The absolute derivative estimate treats negative time
on the same unoriented interval as positive time. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace ComplexConjugate Topology ENNReal
open ContinuousLinearMap Set
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop022BetaHSR124
open TensorCarrier PhysicalTensor BetheCoefficientTransform TraceClass
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115 Prop022TensorCompressionR115
open Prop022VariationalR123 Prop022PrintedCoefficientsR124 Prop022PairHSR122
open Ext006KernelHilbertSchmidt
open Prop022BlockEquationR124 Prop022SignedEnergyR124 Prop022ActualProfileR117
variable {L : ℝ} [Fact (0 < L)]
local instance : Inner ℝ (L2T L) := Inner.rclikeToReal ℂ (L2T L)
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))

/-- The right ideal estimate is proved using the adjoint and the contraction
ideal inequality, then transported back to finite physical columns. -/
lemma force_sum_bound (s t P : ℝ) (hP : 1 ≤ P)
    (hS : ‖(flow B M A hA hB hs u₀ t s).toContinuousLinearMap‖ ≤ P)
    (F : Finset ℤ) :
    ∑ i ∈ F, ‖blockForce B M A hA hB hs u₀ t s (physicalBasis L i)‖^2 ≤
      (pairMajorant A*M*P)^2 := by
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let K := pairKernel B (profile B M A hA hB hs u₀ t)
  let R := conjugateOperator (alpha B M A hA hB hs u₀ t s)
  let X := ((P⁻¹ : ℝ) : ℂ) • R
  have hR : ‖R‖ ≤ P := (conjugateOperator_norm_le _).trans
    ((alpha_norm B M A hA hB hs u₀ t s).trans hS)
  have hX : ‖X‖ ≤ 1 := by
    change ‖((P⁻¹ : ℝ) : ℂ) • R‖ ≤ 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hPpos)]
    exact (inv_mul_le_one₀ hPpos).mpr hR
  have hK : hsSq (physicalBasis L) K ≠ ⊤ := by
    change hsSq (physicalBasis L) (pairKernel B _) ≠ ⊤
    rw [pairKernel_hsSq]
    exact ENNReal.ofReal_ne_top
  have hswap : hsSq (physicalBasis L) (K ∘L X) ≤ hsSq (physicalBasis L) K := by
    rw [hsSq_eq_hsSq_adjoint (physicalBasis L) (physicalBasis L), adjoint_comp]
    exact (hsSq_comp_le (physicalBasis L) (by simpa only [adjoint.norm_map] using hX) K.adjoint).trans_eq
      (hsSq_eq_hsSq_adjoint (physicalBasis L) (physicalBasis L) K).symm
  have hfin := (sum_norm_sq_le (physicalBasis L) (K ∘L X)
    (ne_top_of_le_ne_top hK hswap) F).trans (ENNReal.toReal_mono hK hswap)
  dsimp only [K] at hfin
  rw [pairKernel_hsSq, ENNReal.toReal_ofReal (sq_nonneg _)] at hfin
  have he (x : L2T L) : blockForce B M A hA hB hs u₀ t s x =
      (P : ℂ) • (K ∘L X) x := by
    change K (R x) = (P : ℂ) • K (((P⁻¹ : ℝ) : ℂ) • R x)
    rw [map_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hPpos.ne', Complex.ofReal_one, one_smul]
  simp_rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPpos, mul_pow]
  rw [← Finset.mul_sum]
  have hp := pairCoefficient_bound B M A hA hB _ ((profile_spec B M A hA hB hs u₀).2.2.1 t)
  calc
    _ ≤ P^2 * ‖pairCoefficient B (profile B M A hA hB hs u₀ t)‖^2 :=
      mul_le_mul_of_nonneg_left hfin (sq_nonneg P)
    _ ≤ P^2 * (M * pairMajorant A)^2 := by
      gcongr
    _ = _ := by ring

/-- Number-block skew cancellation leaves only the pair forcing in the
absolute derivative of each column energy. -/
lemma column_energy_derivative (s t : ℝ) (i : ℤ) :
    HasDerivAt (fun r => ‖betaBlock B M A hA hB hs u₀ r s (physicalBasis L i)‖^2)
      (2 * (⟪betaBlock B M A hA hB hs u₀ t s (physicalBasis L i),
        blockForce B M A hA hB hs u₀ t s (physicalBasis L i)⟫_ℂ).im) t := by
  have hd := (beta_derivative B M A hA hB hs u₀ s t (physicalBasis L i)).norm_sq
  apply hd.congr_deriv
  change 2 * (⟪betaBlock B M A hA hB hs u₀ t s (physicalBasis L i),
    (-Complex.I) • (numberOperator B (profile B M A hA hB hs u₀ t)
      (betaBlock B M A hA hB hs u₀ t s (physicalBasis L i)) +
      blockForce B M A hA hB hs u₀ t s (physicalBasis L i))⟫_ℂ).re = _
  let v := betaBlock B M A hA hB hs u₀ t s (physicalBasis L i)
  let a := numberOperator B (profile B M A hA hB hs u₀ t)
  have him : (⟪v, a v⟫_ℂ).im = 0 := by
    have hh := adjoint_inner_left a v v
    rw [numberOperator_adjoint B hs _] at hh
    have hc := congrArg Complex.im hh
    have hr := inner_im_symm (𝕜 := ℂ) (a v) v
    change (⟪a v, v⟫_ℂ).im = -(⟪v, a v⟫_ℂ).im at hr
    linarith
  simp only [inner_smul_right, inner_add_right, Complex.mul_re, Complex.neg_re,
    Complex.I_re, neg_zero, zero_mul, Complex.neg_im, Complex.I_im,
    Complex.add_im, neg_one_mul, zero_sub, neg_neg]
  change 2*((⟪v, a v⟫_ℂ).im + _) = _
  rw [him, zero_add]

include hM in
/-- Every finite collection of physical beta columns obeys the sharp estimate. -/
lemma finite_beta_bound (s t P : ℝ) (hP : 1 ≤ P)
    (hS : ∀ r ∈ uIcc s t,
      ‖(flow B M A hA hB hs u₀ r s).toContinuousLinearMap‖ ≤ P)
    (F : Finset ℤ) :
    Real.sqrt (∑ i ∈ F, ‖betaBlock B M A hA hB hs u₀ t s (physicalBasis L i)‖^2) ≤
      |t-s| *pairMajorant A*M*P := by
  let E := fun r => ∑ i ∈ F, ‖betaBlock B M A hA hB hs u₀ r s (physicalBasis L i)‖^2
  let D := fun r => ∑ i ∈ F, 2 * (⟪betaBlock B M A hA hB hs u₀ r s (physicalBasis L i),
    blockForce B M A hA hB hs u₀ r s (physicalBasis L i)⟫_ℂ).im
  let C := pairMajorant A*M*P
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (pairMajorant_nonneg A hA) hM) (by linarith)
  have hE (r : ℝ) : 0 ≤ E r := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd (r : ℝ) : HasDerivAt E (D r) r :=
    by
      simpa only [E, D, Finset.sum_fn] using
        HasDerivAt.sum (u := F) (fun i _ => column_energy_derivative B M A hA hB hs u₀ s r i)
  have hi : E s = 0 := by simp only [E, beta_self, zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
  have hb (r : ℝ) (hr : r ∈ uIcc s t) : |D r| ≤ 2*C*Real.sqrt (E r) := by
    let v := fun i => betaBlock B M A hA hB hs u₀ r s (physicalBasis L i)
    let f := fun i => blockForce B M A hA hB hs u₀ r s (physicalBasis L i)
    have hf : Real.sqrt (∑ i ∈ F, ‖f i‖^2) ≤ C := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨hC, force_sum_bound B M A hA hB hs u₀ s r P hP (hS r hr) F⟩
    calc
      |D r| ≤ ∑ i ∈ F, |2*(⟪v i, f i⟫_ℂ).im| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ F, 2*(‖v i‖*‖f i‖) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left
          ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)) (by norm_num)
      _ = 2 * ∑ i ∈ F, ‖v i‖*‖f i‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * (Real.sqrt (E r) * Real.sqrt (∑ i ∈ F, ‖f i‖^2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt F (fun i => ‖v i‖) (fun i => ‖f i‖)) (by norm_num)
      _ ≤ 2*C*Real.sqrt (E r) := by nlinarith [Real.sqrt_nonneg (E r)]
  have he := sqrt_energy_bound E D s t C hC hE hd hi hb
  change Real.sqrt (E t) ≤ _
  calc
    _ ≤ C*|t-s| := he
    _ = _ := by dsimp [C]; ring

include hM in
/-- The full HS sum is finite and satisfies the printed quantitative estimate,
for arbitrary signed initial/final times under the report's flow norm bound. -/
theorem beta_hs_bound (s t P : ℝ) (hP : 1 ≤ P)
    (hS : ∀ r ∈ uIcc s t,
      ‖(flow B M A hA hB hs u₀ r s).toContinuousLinearMap‖ ≤ P) :
    hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t s) ≠ ⊤ ∧
      Real.sqrt ((hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t s)).toReal) ≤
        |t-s| *pairMajorant A*M*P := by
  let C := |t-s| *pairMajorant A*M*P
  have hC : 0 ≤ C := by
    have hpa := pairMajorant_nonneg A hA
    have hP0 : 0 ≤ P := by linarith
    dsimp [C]
    positivity
  have hfinite (F : Finset ℤ) :
      ∑ i ∈ F, ‖betaBlock B M A hA hB hs u₀ t s (physicalBasis L i)‖^2 ≤ C^2 := by
    have hh := finite_beta_bound B M A hM hA hB hs u₀ s t P hP hS F
    have hn : 0 ≤ ∑ i ∈ F, ‖betaBlock B M A hA hB hs u₀ t s (physicalBasis L i)‖^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (∑ i ∈ F, ‖betaBlock B M A hA hB hs u₀ t s (physicalBasis L i)‖^2)]
  have hall : hsSq (physicalBasis L) (betaBlock B M A hA hB hs u₀ t s) ≤ ENNReal.ofReal (C^2) := by
    apply ENNReal.summable.tsum_le_of_sum_le
    intro F
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hfinite F)
  have hn := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hall
  refine ⟨hn, ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hall
  rw [ENNReal.toReal_ofReal (sq_nonneg C)] at hr
  exact (Real.sqrt_le_iff).mpr ⟨hC, hr⟩

end QuantumNLS.Prop022BetaHSR124
#print axioms QuantumNLS.Prop022BetaHSR124.beta_hs_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022BetaHSR124." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022BetaHSR124." then
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
  Lean.logInfo m!"R124 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
