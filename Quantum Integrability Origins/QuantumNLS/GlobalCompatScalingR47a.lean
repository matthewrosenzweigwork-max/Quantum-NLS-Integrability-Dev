import QuantumNLS.GlobalCompatSettingR47a

/-! Coupling scaling and joint real analyticity, including the analytic inverse.
The analyticity of the positive square root is proved through the analytic
inverse criterion for the square map, with its nonzero derivative verified. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate Topology
open Set Metric Filter
namespace QuantumNLS.GlobalCompatR47a
open PhysicalTensor (L2T)
open D01LocalPrimitive (K)
open RF535Final (Local023Body)
variable {L d CL : ℝ} [Fact (0 < L)]
variable {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
variable {Φ : ℝ → L2T L → K} {Ψ : ℝ → K → L2T L}

abbrev Family (d : ℝ) (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L)
    (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L) : Prop :=
  ∀ κ (hκ : 0 < κ), Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ)

theorem scaling (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl)
    (hf : Family d Φl Ψl Φ Ψ) {κ s : ℝ} (hκ : 0 < κ) (hs : 0 < s) (u : L2T L) :
    Φ κ (s • u) = s • Φ (κ * s^2) u := by
  have hks : 0 < κ * s^2 := mul_pos hκ (sq_pos_of_pos hs)
  let r := min ((d / Real.sqrt κ) / s) (d / Real.sqrt (κ * s^2))
  have hr : 0 < r := lt_min (div_pos (div_pos hd (Real.sqrt_pos.2 hκ)) hs)
    (div_pos hd (Real.sqrt_pos.2 hks))
  have H := identity (f := fun v : L2T L => Φ κ (s • v))
    (g := fun v : L2T L => s • Φ (κ*s^2) v)
    (fun v => ((hf κ hκ).analytic _).comp (Local023.analyticAt_smul_gen s v))
    (fun v => (Local023.analyticAt_smul_gen s _).comp ((hf (κ*s^2) hks).analytic v)) hr (fun v hv => ?_)
  · exact congrFun H u
  · have hvn := mem_ball_zero_iff.mp hv
    have hvB : v ∈ ball (0 : L2T L) (d / Real.sqrt (κ*s^2)) :=
      mem_ball_zero_iff.mpr (hvn.trans_le (min_le_right _ _))
    have hvA : s • v ∈ ball (0 : L2T L) (d / Real.sqrt κ) := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      simpa only [mul_comm] using (lt_div_iff₀ hs).mp (hvn.trans_le (min_le_left _ _))
    rw [(hf κ hκ).local_eq _ hvA, (hf (κ*s^2) hks).local_eq _ hvB]
    exact hl.2.1 κ hκ s hs v (mem_ball_zero_iff.mp hvB)

theorem unit_formula (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl)
    (hf : Family d Φl Ψl Φ Ψ) {κ : ℝ} (hκ : 0 < κ) (u : L2T L) :
    Φ κ u = (Real.sqrt κ)⁻¹ • Φ 1 (Real.sqrt κ • u) := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have H := scaling hd hl hf one_pos (Real.sqrt_pos.2 hκ) u
  simp only [one_mul, Real.sq_sqrt hκ.le] at H
  rw [H, inv_smul_smul₀ hs]

theorem inverse_unit_formula (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl)
    (hf : Family d Φl Ψl Φ Ψ) {κ : ℝ} (hκ : 0 < κ) (z : K) :
    Ψ κ z = (Real.sqrt κ)⁻¹ • Ψ 1 (Real.sqrt κ • z) := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  let w := (Real.sqrt κ)⁻¹ • Ψ 1 (Real.sqrt κ • z)
  have H : Φ κ w = z := by
    rw [unit_formula hd hl hf hκ]
    simp only [w, smul_inv_smul₀ hs, (hf 1 one_pos).right_inv, inv_smul_smul₀ hs]
  calc Ψ κ z = Ψ κ (Φ κ w) := congrArg (Ψ κ) H.symm
       _ = w := (hf κ hκ).left_inv w

theorem sqrt_analytic {κ : ℝ} (hκ : 0 < κ) : AnalyticAt ℝ Real.sqrt κ := by
  have ha : AnalyticAt ℝ (fun t : ℝ => t^2) (Real.sqrt κ) := analyticAt_id.pow 2
  have hd : deriv (fun t : ℝ => t^2) (Real.sqrt κ) ≠ 0 := by
    rw [(hasDerivAt_pow 2 (Real.sqrt κ)).deriv]
    positivity
  have H : AnalyticAt ℝ (Real.sqrt ∘ fun t : ℝ => t^2) (Real.sqrt κ) := by
    apply analyticAt_id.congr
    filter_upwards [eventually_gt_nhds (Real.sqrt_pos.2 hκ)] with t ht
    simp [Function.comp_def, Real.sqrt_sq ht.le]
  simpa only [Real.sq_sqrt hκ.le] using (analyticAt_comp_iff_of_deriv_ne_zero ha hd).mp H

theorem joint_analytic (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl)
    (hf : Family d Φl Ψl Φ Ψ) {κ : ℝ} (hκ : 0 < κ) (u : L2T L) :
    AnalyticAt ℝ (fun p : ℝ × L2T L => Φ p.1 p.2) (κ,u) := by
  have hs : AnalyticAt ℝ (fun p : ℝ × L2T L => Real.sqrt p.1) (κ,u) :=
    (sqrt_analytic hκ).comp analyticAt_fst
  have H := (hs.inv (Real.sqrt_pos.2 hκ).ne').smul
    (((hf 1 one_pos).analytic _).comp (hs.smul analyticAt_snd))
  apply H.congr
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hκ] with p hp
  exact (unit_formula hd hl hf hp p.2).symm

theorem inverse_joint_analytic (hd : 0 < d) (hl : Local023Body L d CL Φl Ψl)
    (hf : Family d Φl Ψl Φ Ψ) {κ : ℝ} (hκ : 0 < κ) (z : K) :
    AnalyticAt ℝ (fun p : ℝ × K => Ψ p.1 p.2) (κ,z) := by
  have hs : AnalyticAt ℝ (fun p : ℝ × K => Real.sqrt p.1) (κ,z) :=
    (sqrt_analytic hκ).comp analyticAt_fst
  have H := (hs.inv (Real.sqrt_pos.2 hκ).ne').smul
    (((hf 1 one_pos).inverse_analytic _).comp (hs.smul analyticAt_snd))
  apply H.congr
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hκ] with p hp
  exact (inverse_unit_formula hd hl hf hp p.2).symm
end QuantumNLS.GlobalCompatR47a

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.GlobalCompatR47a." ||
        n.toString.startsWith "_private.QuantumNLS.GlobalCompatR47a." then
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
  Lean.logInfo m!"Round47 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
