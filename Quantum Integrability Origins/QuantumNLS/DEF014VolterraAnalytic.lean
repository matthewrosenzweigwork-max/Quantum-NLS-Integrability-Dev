import QuantumNLS.DEF014VolterraOperator

/-! Real analyticity of the L1 transfer from its actual Volterra series.
Polarization converts the diagonal factorial estimate to a convergent
multilinear series on arbitrarily large balls. No Banach holomorphy contract
or assumed analytic transfer is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Topology MeasureTheory
open scoped Interval
namespace QuantumNLS.DEF014VolterraAnalytic
open DEF014VolterraOperator
variable {E 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable {L : ℝ} (hL : 0 ≤ L) (A : Family E 𝔸 L)

/-- Precomposition by the actual bilinear Volterra operator adds one slot. -/
def next {n : ℕ} (B : E [×n]→L[ℝ] Path L 𝔸) :
    E →L[ℝ] E [×n]→L[ℝ] Path L 𝔸 :=
  ((ContinuousLinearMap.apply ℝ (E [×n]→L[ℝ] Path L 𝔸) B).comp
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin n => E) (Path L 𝔸) (Path L 𝔸))).comp (operator hL A)

/-- Ordered iterated integrals with independent coefficient slots. -/
def iterates : ∀ n : ℕ, E [×n]→L[ℝ] Path L 𝔸
  | 0 => ContinuousMultilinearMap.uncurry0 ℝ E (ContinuousMap.const _ 1)
  | n + 1 => (next hL A (iterates n)).uncurryLeft

@[simp] theorem iterates_zero (v : Fin 0 → E) (x : Icc (0 : ℝ) L) :
    iterates hL A 0 v x = 1 := rfl

@[simp] theorem iterates_succ (n : ℕ) (v : Fin (n+1) → E) (x : Icc (0 : ℝ) L) :
    iterates hL A (n+1) v x =
      ∫ t in (0 : ℝ)..x.1, A.coef (v 0) t *
        extend hL (iterates hL A n (Fin.tail v)) t := rfl

/-- On the diagonal these are exactly the frozen Dyson terms, not replacement terms. -/
theorem iterates_diag (n : ℕ) (e : E) (x : Icc (0 : ℝ) L) :
    iterates hL A n (fun _ => e) x = LinearFundamental.dyson (A.coef e) n x.1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iterates_succ, LinearFundamental.dyson]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le x.2.1] at ht
    have htL : t ∈ Icc (0 : ℝ) L := ⟨ht.1, ht.2.trans x.2.2⟩
    have he : extend hL (iterates hL A n (fun _ => e)) t =
        iterates hL A n (fun _ => e) ⟨t, htL⟩ := by
      change (iterates hL A n (fun _ => e)) (projIcc 0 L hL t) = _
      rw [projIcc_of_mem hL htL]
    change A.coef e t * extend hL (iterates hL A n (fun _ => e)) t =
      A.coef e t * LinearFundamental.dyson (A.coef e) n t
    rw [he, ih]

/-- Factorial bound in the sup norm, in terms of the coefficient L1 norm. -/
theorem norm_iterates_diag_le (n : ℕ) (e : E) :
    ‖iterates hL A n (fun _ => e)‖ ≤
      ‖(1 : 𝔸)‖ * (A.bound * ‖e‖)^n / (n.factorial : ℝ) := by
  have hA0 := A.bound_nonneg
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  rw [iterates_diag]
  exact ((L1SpatialTransfer.uniform_dyson_bound hL (A.integrable e)).2 n x.1 x.2).trans
    (by
      have h0 : 0 ≤ ∫ t in (0 : ℝ)..L, ‖A.coef e t‖ :=
        intervalIntegral.integral_nonneg hL (fun t _ => norm_nonneg _)
      gcongr
      exact A.norm_integral_le e)

/-- Actual transfer path, obtained by restricting the frozen L1 transfer. -/
def transferPath (e : E) : Path L 𝔸 where
  toFun x := L1SpatialTransfer.transfer (A.coef e) x.1
  continuous_toFun := by
    have hc := L1SpatialTransfer.continuousOn_transfer hL (A.integrable e)
    exact hc.domRestrict

/-- Norm convergence of the multilinear diagonal series to the actual path. -/
theorem hasSum_iterates (e : E) :
    HasSum (fun n => iterates hL A n (fun _ => e)) (transferPath hL A e) := by
  have hs : Summable (fun n : ℕ => ‖(1 : 𝔸)‖ * (A.bound * ‖e‖)^n / (n.factorial : ℝ)) := by
    simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial (A.bound * ‖e‖)).mul_left ‖(1 : 𝔸)‖
  have hsm : Summable (fun n => iterates hL A n (fun _ => e)) :=
    Summable.of_norm_bounded hs (norm_iterates_diag_le hL A · e)
  convert hsm.hasSum using 1
  ext x
  have heval : (∑' n, iterates hL A n (fun _ => e)) x =
      ∑' n, iterates hL A n (fun _ => e) x := by
    exact (ContinuousMap.tsum_apply hsm x).symm
  rw [heval]
  simp only [iterates_diag, transferPath, ContinuousMap.coe_mk, L1SpatialTransfer.transfer]

/-- A power series for the actual L1 transfer on any prescribed ball (after polarization). -/
theorem powerSeries (R : ℝ) (hR : 0 < R) :
    HasFPowerSeriesOnBall (transferPath hL A)
      (RealAnalyticDef.symSeries (iterates hL A)) 0 (ENNReal.ofReal (R / Real.exp 1)) := by
  apply RealAnalyticDef.hasFPowerSeriesOnBall_symSeries (iterates hL A)
    (C := ‖(1 : 𝔸)‖ * Real.exp (A.bound * R)) (by positivity) hR
  · intro n e
    have hh := Real.pow_div_factorial_le_exp (A.bound * R)
      (mul_nonneg A.bound_nonneg hR.le) n
    calc
      _ ≤ ‖(1 : 𝔸)‖ * (A.bound * ‖e‖)^n / (n.factorial : ℝ) :=
        norm_iterates_diag_le hL A n e
      _ = ‖(1 : 𝔸)‖ * ((A.bound * R)^n / (n.factorial : ℝ)) * (‖e‖ / R)^n := by
        rw [mul_pow, mul_pow, div_pow]
        field_simp
      _ ≤ (‖(1 : 𝔸)‖ * Real.exp (A.bound * R)) * (‖e‖ / R)^n := by gcongr
  · intro e _
    simpa only [zero_add] using (hasSum_iterates hL A e).tendsto_sum_nat

/-- Entire real analyticity on any normed real coefficient carrier mapping
bounded-linearly into L1. No smallness hypothesis on the base coefficient. -/
theorem analyticAt_transferPath (e : E) : AnalyticAt ℝ (transferPath hL A) e := by
  let R := (‖e‖ + 1) * Real.exp 1
  have hR : 0 < R := by dsimp [R]; positivity
  apply (powerSeries hL A R hR).analyticAt_of_mem
  rw [Metric.mem_eball, edist_lt_ofReal, dist_zero_right]
  dsimp [R]
  rw [mul_div_cancel_right₀ _ (Real.exp_ne_zero 1)]
  linarith

end QuantumNLS.DEF014VolterraAnalytic

-- ROUND 4 AUTHOR AUDIT
#print axioms QuantumNLS.DEF014VolterraAnalytic.iterates_diag
#print axioms QuantumNLS.DEF014VolterraAnalytic.hasSum_iterates
#print axioms QuantumNLS.DEF014VolterraAnalytic.powerSeries
#print axioms QuantumNLS.DEF014VolterraAnalytic.analyticAt_transferPath

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DEF014VolterraAnalytic." then
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
  Lean.logInfo m!"DEF014VolterraAnalytic audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
