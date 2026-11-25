import QuantumNLS.RootH1RatioKernel

/-! Sharp row estimate for the actual periodic L² resolvent. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumNLS.HaarResolvent QuantumNLS.HaarKernelFactorization
  QuantumNLS.HaarKernelFactorizationOp QuantumNLS.RootH1RatioKernel
namespace QuantumNLS.RootH1RatioResolvent

variable {L : ℝ} [hLf : Fact (0 < L)]

lemma kernel_memLp (q z : ℂ) {x : ℝ} (hx : x ∈ Ico 0 L) :
    MemLp (Rk q z x) 2 (volume.restrict (Ioc 0 L)) := by
  have hm : Measurable (Rk q z x) := by
    unfold Rk
    have he : Continuous (fun t : ℝ =>
        Complex.exp (Complex.I*z*((x-t:ℝ):ℂ))) := by fun_prop
    exact (he.measurable.div_const _).mul
      (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
        (Measurable.ite (measurableSet_lt measurable_const measurable_id)
          measurable_const measurable_const))
  apply MemLp.of_bound (μ := volume.restrict (Ioc 0 L))
    hm.aestronglyMeasurable (RB L q z)
  have hn : ∀ᵐ t ∂(volume.restrict (Ioc 0 L)), t ≠ L :=
    ae_restrict_of_ae (by simp [ae_iff])
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hn] with t ht hn
  exact norm_Rk_le L q z hx ⟨ht.1.le, lt_of_le_of_ne ht.2 hn⟩

lemma integral_cauchy_sq {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 L))) :
    ‖∫ t in (0:ℝ)..L, f t*g t‖^2 ≤
      (∫ t in (0:ℝ)..L, ‖f t‖^2)*(∫ t in (0:ℝ)..L, ‖g t‖^2) := by
  have hL : 0 ≤ L := hLf.out.le
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have hb : ‖∫ t in (0:ℝ)..L, f t*g t‖ ≤
      Real.sqrt (∫ t, ‖f t‖^2 ∂volume.restrict (Ioc 0 L))*
        Real.sqrt (∫ t, ‖g t‖^2 ∂volume.restrict (Ioc 0 L)) := by
    rw [intervalIntegral.integral_of_le hL]
    exact (norm_integral_le_integral_norm _).trans (by simpa only [norm_mul] using hh)
  have h1 : 0 ≤ ∫ t, ‖f t‖^2 ∂volume.restrict (Ioc 0 L) :=
    integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ ∫ t, ‖g t‖^2 ∂volume.restrict (Ioc 0 L) :=
    integral_nonneg fun _ => sq_nonneg _
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2,
    intervalIntegral.integral_of_le hL] using hs

lemma row_bound {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    {x : ℝ} (hx : x ∈ Ico 0 L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    ‖∫ t in (0:ℝ)..L, Rk (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I) x t * f t‖^2 ≤
      (1/Y)*(∫ t in (0:ℝ)..L, ‖f t‖^2) := by
  have hh := integral_cauchy_sq
    (kernel_memLp (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I) hx) hf
  rw [integral_norm_Rk_sq hY hLf.out ⟨hx.1,hx.2.le⟩] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (log_three_bound hY hLf.out hlog)
    (intervalIntegral.integral_nonneg hLf.out.le fun _ _ => sq_nonneg _))

#print axioms kernel_memLp
#print axioms integral_cauchy_sq
#print axioms row_bound
end QuantumNLS.RootH1RatioResolvent

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioResolvent." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioResolvent." then
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
