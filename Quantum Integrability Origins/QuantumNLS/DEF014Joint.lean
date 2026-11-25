import QuantumNLS.DiscParamContinuity
import QuantumNLS.PhysicalSourceFinal

/-! Joint continuity of the actual L2 L2SpatialTransfer.discriminant, including its spectral
parameter. This extends the frozen Gronwall proof with the explicit spectral
coefficient difference. No physical regularity conclusion is supplied as input. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix Interval ENNReal
namespace QuantumNLS.DEF014Joint
open SpatialTransfer L1SpatialTransfer L1Stability DiscParamContinuity
open L2SpatialTransfer (profile intervalIntegrable_profile intervalIntegrable_coef discriminant spatialTransfer)
open PhysicalTensor (L2T)
open RootDiscriminantBound (row_sum_le_norm norm_le_of_row_sums)
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L : ℝ} [Fact (0 < L)]

theorem norm_balCoef_spectral_sub_le (κ : ℝ) (v : ℝ → ℂ) (z w : ℂ) (x : ℝ) :
    ‖balCoef κ v z x - balCoef κ v w x‖ ≤ ‖z - w‖ / 2 := by
  refine norm_le_of_row_sums _ (by positivity) fun i => ?_
  fin_cases i <;> simp [balCoef, coef, ← sub_div]
  · rw [show -(Complex.I * z) + Complex.I * w = -(Complex.I * (z - w)) by ring]
    simp
  · rw [← mul_sub]
    simp

theorem continuous_discriminant_joint :
    Continuous (fun p : (ℝ × L2T L) × ℂ => L2SpatialTransfer.discriminant p.1.1 p.1.2 p.2) := by
  have hL : 0 < L := Fact.out
  rw [continuous_iff_continuousAt]
  rintro ⟨⟨κ0, u0⟩, z0⟩
  set A : (ℝ × L2T L) × ℂ → ℝ → Mat2 := fun p => balCoef p.1.1 (profile p.1.2) p.2 with hAdef
  have hA : ∀ p, IntervalIntegrable (A p) volume 0 L := fun p =>
    intervalIntegrable_coef (intervalIntegrable_profile p.1.2) _ _ p.2
  set a : (ℝ × L2T L) × ℂ → ℝ := fun p => ∫ s in (0 : ℝ)..L, ‖A p s - A ((κ0, u0), z0) s‖ with hadef
  set b0 : ℝ := ∫ s in (0 : ℝ)..L, ‖A ((κ0, u0), z0) s‖ with hb0
  set I0 : ℝ := ∫ s in (0 : ℝ)..L, ‖profile u0 s‖ with hI0
  have hnorm_int : ∀ p, IntervalIntegrable (fun s => ‖A p s - A ((κ0, u0), z0) s‖) volume 0 L := fun p =>
    ((hA p).sub (hA ((κ0, u0), z0))).norm
  have ha0 : ∀ p, 0 ≤ a p := fun p => intervalIntegral.integral_nonneg hL.le fun s _ => norm_nonneg _
  -- the bound U(p) for a(p)
  set U : (ℝ × L2T L) × ℂ → ℝ := fun p =>
    Real.sqrt p.1.1 * (Real.sqrt L * ‖p.1.2 - u0‖) + |Real.sqrt p.1.1 - Real.sqrt κ0| * I0 + L * (‖p.2 - z0‖ / 2) with hU
  have hu_int : ∀ p : (ℝ × L2T L) × ℂ, IntervalIntegrable (fun s => ‖profile p.1.2 s - profile u0 s‖) volume 0 L :=
    fun p => ((intervalIntegrable_profile p.1.2).sub (intervalIntegrable_profile u0)).norm
  have hprof : ∀ p : (ℝ × L2T L) × ℂ,
      ∫ s in (0 : ℝ)..L, ‖profile p.1.2 s - profile u0 s‖ ≤ Real.sqrt L * ‖p.1.2 - u0‖ := by
    intro p
    have h1 : ∫ s in (0 : ℝ)..L, ‖profile p.1.2 s - profile u0 s‖ =
        ∫ s in (0 : ℝ)..L, ‖profile (p.1.2 - u0) s‖ := by
      rw [intervalIntegral.integral_of_le hL.le, intervalIntegral.integral_of_le hL.le]
      refine integral_congr_ae ?_
      filter_upwards [profile_sub_ae p.1.2 u0] with s hs
      rw [hs]
    rw [h1]
    exact integral_profile_le _
  have ha_le : ∀ p, a p ≤ U p := by
    intro p
    have hpt : ∀ s, ‖A p s - A ((κ0, u0), z0) s‖ ≤
        Real.sqrt p.1.1 * ‖profile p.1.2 s - profile u0 s‖ + |Real.sqrt p.1.1 - Real.sqrt κ0| * ‖profile u0 s‖ + ‖p.2 - z0‖ / 2 := by
      intro s
      have hsplit := norm_sub_le_norm_sub_add_norm_sub
        (balCoef p.1.1 (profile p.1.2) p.2 s)
        (balCoef κ0 (profile u0) p.2 s) (balCoef κ0 (profile u0) z0 s)
      refine hsplit.trans ?_
      have hs := norm_balCoef_spectral_sub_le κ0 (profile u0) p.2 z0 s
      have hp := norm_balCoef_sub_le p.1.1 κ0 (profile p.1.2) (profile u0) p.2 s
      apply add_le_add (hp.trans ?_) hs
      have e : (Real.sqrt p.1.1 : ℂ) * profile p.1.2 s - (Real.sqrt κ0 : ℂ) * profile u0 s =
          (Real.sqrt p.1.1 : ℂ) * (profile p.1.2 s - profile u0 s) +
            ((Real.sqrt p.1.1 : ℂ) - (Real.sqrt κ0 : ℂ)) * profile u0 s := by ring
      rw [e]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have : ‖(Real.sqrt p.1.1 : ℂ) - (Real.sqrt κ0 : ℂ)‖ = |Real.sqrt p.1.1 - Real.sqrt κ0| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [this]
    have hint2 : IntervalIntegrable (fun s => Real.sqrt p.1.1 * ‖profile p.1.2 s - profile u0 s‖ +
        |Real.sqrt p.1.1 - Real.sqrt κ0| * ‖profile u0 s‖ + ‖p.2 - z0‖ / 2) volume 0 L :=
      ((hu_int p).const_mul _).add (((intervalIntegrable_profile u0).norm).const_mul _) |>.add intervalIntegrable_const
    have h1 := intervalIntegral.integral_mono_on hL.le (hnorm_int p) hint2 (fun s _ => hpt s)
    refine le_trans h1 ?_
    rw [intervalIntegral.integral_add
      (((hu_int p).const_mul _).add (((intervalIntegrable_profile u0).norm).const_mul _))
      intervalIntegrable_const,
      intervalIntegral.integral_add ((hu_int p).const_mul _)
        (((intervalIntegrable_profile u0).norm).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    have := hprof p
    have hs : 0 ≤ Real.sqrt p.1.1 := Real.sqrt_nonneg _
    simp only [hU, hI0, sub_zero, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left this hs]
  have hUcont : ContinuousAt U ((κ0, u0), z0) := by
    have : Continuous U := by
      simp only [hU]
      fun_prop
    exact this.continuousAt
  have hU0 : U ((κ0, u0), z0) = 0 := by simp [hU]
  have haT : Tendsto a (𝓝 ((κ0, u0), z0)) (𝓝 0) := by
    have hUT : Tendsto U (𝓝 ((κ0, u0), z0)) (𝓝 0) := by
      have := hUcont.tendsto
      rwa [hU0] at this
    exact squeeze_zero ha0 ha_le hUT
  -- the bound for the L2SpatialTransfer.discriminant difference
  set K1 : ℝ := ‖(1 : Mat2)‖ with hK1
  set R : ℝ → ℝ := fun x => 2 * (x * (K1 * Real.exp (b0 + x)) * Real.exp b0) with hR
  have hRT : Tendsto (fun p => R (a p)) (𝓝 ((κ0, u0), z0)) (𝓝 0) := by
    have hRc : Continuous R := by simp only [hR]; fun_prop
    have h0 : R 0 = 0 := by simp [hR]
    have := (hRc.tendsto 0).comp haT
    rwa [h0] at this
  have hbound : ∀ p : (ℝ × L2T L) × ℂ, ‖L2SpatialTransfer.discriminant p.1.1 p.1.2 p.2 - L2SpatialTransfer.discriminant κ0 u0 z0‖ ≤ R (a p) := by
    intro p
    have hLmem : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
    have hdiff := norm_transfer_sub_le hL.le (hA p) (hA ((κ0, u0), z0)) hLmem
    have hb : ∫ s in (0 : ℝ)..L, ‖A p s‖ ≤ b0 + a p := by
      have hpt : ∀ s, ‖A p s‖ ≤ ‖A ((κ0, u0), z0) s‖ + ‖A p s - A ((κ0, u0), z0) s‖ := by
        intro s
        have := norm_add_le (A ((κ0, u0), z0) s) (A p s - A ((κ0, u0), z0) s)
        simpa [add_sub_cancel, add_comm] using this
      have h1 := intervalIntegral.integral_mono_on hL.le (hA p).norm
        ((hA ((κ0, u0), z0)).norm.add (hnorm_int p)) (fun s _ => hpt s)
      refine le_trans h1 ?_
      rw [intervalIntegral.integral_add (hA ((κ0, u0), z0)).norm (hnorm_int p)]
    have hexp : Real.exp (∫ s in (0 : ℝ)..L, ‖A p s‖) ≤ Real.exp (b0 + a p) := Real.exp_le_exp.2 hb
    have hK0 : 0 ≤ K1 := norm_nonneg _
    have htr : ‖L2SpatialTransfer.discriminant p.1.1 p.1.2 p.2 - L2SpatialTransfer.discriminant κ0 u0 z0‖ ≤
        2 * ‖spatialTransfer p.1.1 p.1.2 p.2 L - spatialTransfer κ0 u0 z0 L‖ := by
      unfold QuantumNLS.L2SpatialTransfer.discriminant
      rw [← Matrix.trace_sub, Matrix.trace_fin_two]
      refine le_trans (norm_add_le _ _) ?_
      have h0 := row_sum_le_norm (spatialTransfer p.1.1 p.1.2 p.2 L - spatialTransfer κ0 u0 z0 L) 0
      have h1 := row_sum_le_norm (spatialTransfer p.1.1 p.1.2 p.2 L - spatialTransfer κ0 u0 z0 L) 1
      have n0 := norm_nonneg ((spatialTransfer p.1.1 p.1.2 p.2 L - spatialTransfer κ0 u0 z0 L) 0 1)
      have n1 := norm_nonneg ((spatialTransfer p.1.1 p.1.2 p.2 L - spatialTransfer κ0 u0 z0 L) 1 0)
      linarith
    refine le_trans htr ?_
    simp only [hR]
    have hdiff' : ‖spatialTransfer p.1.1 p.1.2 p.2 L - spatialTransfer κ0 u0 z0 L‖ ≤
        a p * (K1 * Real.exp (b0 + a p)) * Real.exp b0 := by
      refine le_trans hdiff ?_
      have e0 : 0 ≤ Real.exp b0 := (Real.exp_pos _).le
      have : a p * (K1 * Real.exp (∫ s in (0 : ℝ)..L, ‖A p s‖)) ≤ a p * (K1 * Real.exp (b0 + a p)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hK0) (ha0 p)
      exact mul_le_mul_of_nonneg_right this e0
    linarith
  have hT : Tendsto (fun p : (ℝ × L2T L) × ℂ => ‖L2SpatialTransfer.discriminant p.1.1 p.1.2 p.2 - L2SpatialTransfer.discriminant κ0 u0 z0‖)
      (𝓝 ((κ0, u0), z0)) (𝓝 0) :=
    squeeze_zero (fun p => norm_nonneg _) hbound hRT
  exact (tendsto_iff_norm_sub_tendsto_zero.2 hT)

end QuantumNLS.DEF014Joint

#print axioms QuantumNLS.DEF014Joint.continuous_discriminant_joint

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DEF014Joint." then
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
  Lean.logInfo m!"DEF014Joint audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
