import QuantumNLS.RootH1RatioModes

/-! Full real-parameter strong convergence of the actual periodic resolvent. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioOperator
  QuantumNLS.RootH1RatioModes
namespace QuantumNLS.RootH1RatioStrong
variable {L : ℝ} [hLf : Fact (0 < L)]

def rescaled (Y : ℝ) : L2T L →L[ℂ] L2T L :=
  (Y:ℂ) • RootH1RatioOperator.resolvent Y

lemma rescaled_norm {Y : ℝ} (hY : 0 < Y) (u : L2T L) :
    ‖rescaled Y u‖ ≤ ‖u‖ := by
  change ‖(Y:ℂ) • RootH1RatioOperator.resolvent Y u‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hY.le]
  calc
    _ ≤ Y*(‖u‖/Y) := mul_le_mul_of_nonneg_left (RootH1RatioL2.resolvent_apply_norm hY u) hY.le
    _ = ‖u‖ := by field_simp

omit hLf in
lemma scalar_limit (n : ℤ) :
    Tendsto (fun Y : ℝ => (Y:ℂ)*((Y:ℂ)+omega L n)⁻¹) atTop (nhds 1) := by
  have hi : Tendsto (fun Y : ℝ => ((Y:ℂ))⁻¹) atTop (nhds 0) := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_zero, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  have hs : Tendsto (fun Y : ℝ => ((1:ℂ)+omega L n*(Y:ℂ)⁻¹)⁻¹) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hi)).inv₀ (by norm_num : (1:ℂ)+omega L n*0 ≠ 0)
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Y hY
  have hYc : (Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hd : (Y:ℂ)+omega L n ≠ 0 := by
    intro hh
    have he := congrArg Complex.re hh
    simp only [Complex.add_re, Complex.ofReal_re, omega_re, add_zero, Complex.zero_re] at he
    linarith
  field_simp

lemma mode_limit (n : ℤ) :
    Tendsto (fun Y : ℝ => rescaled Y (QuantumNLS.Fourier.modeLp L n)) atTop
      (nhds (QuantumNLS.Fourier.modeLp L n)) := by
  have h := (scalar_limit (L := L) n).smul_const (QuantumNLS.Fourier.modeLp L n)
  simp only [one_smul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Y hY
  rw [rescaled, smul_apply, resolvent_mode hY, smul_smul]

lemma finite_limit (c : ℤ → ℂ) (s : Finset ℤ) :
    Tendsto (fun Y : ℝ => rescaled Y (∑ n ∈ s, c n • QuantumNLS.Fourier.modeLp L n))
      atTop (nhds (∑ n ∈ s, c n • QuantumNLS.Fourier.modeLp L n)) := by
  have h := tendsto_finsetSum s (fun n _ => (mode_limit (L := L) n).const_smul (c n))
  simpa only [map_sum, map_smul] using h

/-- Convergence along all real Y tending to infinity, not only a selected sequence. -/
theorem resolvent_strong (u : L2T L) :
    Tendsto (fun Y : ℝ => rescaled Y u) atTop (nhds u) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε/4 := by positivity
  have hh := Metric.tendsto_nhds.mp (QuantumNLS.Fourier.hasSum_coeff_smul_modeLp L u) (ε/4) he
  obtain ⟨s,hs⟩ := hh.exists
  let v : L2T L := ∑ n ∈ s, QuantumNLS.Fourier.coeff L u n • QuantumNLS.Fourier.modeLp L n
  have hv : ‖v-u‖ < ε/4 := by simpa only [dist_eq_norm] using hs
  have hlim := Metric.tendsto_nhds.mp (finite_limit (L := L) (QuantumNLS.Fourier.coeff L u) s) (ε/4) he
  filter_upwards [hlim, eventually_gt_atTop (0:ℝ)] with Y hYv hY
  change dist (rescaled Y v) v < ε/4 at hYv
  rw [dist_eq_norm] at hYv ⊢
  have huv : ‖u-v‖ = ‖v-u‖ := norm_sub_rev _ _
  have hb : ‖rescaled Y u-u‖ ≤ 2*‖v-u‖ + ‖rescaled Y v-v‖ := by
    have heq : rescaled Y u-u = rescaled Y (u-v) + (rescaled Y v-v) + (v-u) := by
      rw [map_sub]
      abel
    rw [heq]
    calc
      ‖rescaled Y (u-v)+(rescaled Y v-v)+(v-u)‖ ≤
          ‖rescaled Y (u-v)+(rescaled Y v-v)‖+‖v-u‖ := norm_add_le _ _
      _ ≤ (‖rescaled Y (u-v)‖+‖rescaled Y v-v‖)+‖v-u‖ :=
        by linarith [norm_add_le (rescaled Y (u-v)) (rescaled Y v-v)]
      _ ≤ (‖u-v‖+‖rescaled Y v-v‖)+‖v-u‖ :=
        by gcongr; exact rescaled_norm hY (u-v)
      _ = 2*‖v-u‖+‖rescaled Y v-v‖ := by rw [huv]; ring

  linarith

#print axioms rescaled_norm
#print axioms scalar_limit
#print axioms mode_limit
#print axioms finite_limit
#print axioms resolvent_strong
end QuantumNLS.RootH1RatioStrong

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioStrong." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioStrong." then
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
