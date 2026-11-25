import QuantumNLS.ActualModelChartR52a

/-! R-E679E41D: the actual local quadratic/logarithmic branch is
holomorphic in its spectral and transfer arguments near every regular
background point. No branch is defined by its desired period value. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Topology Complex
namespace QuantumNLS.ActualModelPeriodGermR52a
open PhysicalTensor RootScalarPeriodR10 ScalarLogBranchR10
variable {L κ : ℝ} [Fact (0 < L)]

def germ (hκ : 0 < κ) (u : L2T L) (p : ℂ × ℂ) : ℂ := lambda hκ u p.1 p.2

/-- Holomorphic background Cauchy exponent on the full regular locus,
including both half planes and every real open-band crossing. -/
theorem analytic_exponent (hκ : 0 < κ) (u : L2T L) (z : ℂ)
    (hz : RootCauchyJointR9.Regular κ (u,z)) :
    AnalyticAt ℂ (exponent hκ u) z := by
  have hG : AnalyticAt ℂ (fun w => RootCauchyFullBracketR8.G hκ w u) z := by
    rw [analyticAt_iff_eventually_differentiableAt]
    have he := ((RootCauchyJointR9.isOpen_regular κ).preimage
      (continuous_const.prodMk continuous_id)).mem_nhds hz
    filter_upwards [he] with w hw
    exact RootCauchyJointR9.differentiableAt_spectral_regular hκ (u,w) hw
  exact (analyticAt_const (v := I*(κ : ℂ))).mul hG

/-- Joint complex analyticity of the literal branch at the actual scalar
transfer, obtained from its square root and logarithm on their slit planes. -/
theorem analytic_germ (hκ : 0 < κ) (u : L2T L) (z : ℂ)
    (hz : RootCauchyJointR9.Regular κ (u,z)) :
    AnalyticAt ℂ (germ hκ u) (z,symbol κ u z) := by
  let p : ℂ × ℂ := (z,symbol κ u z)
  have hg : AnalyticAt ℂ (fun q : ℂ × ℂ => exponent hκ u q.1) p :=
    AnalyticAt.comp (𝕜 := ℂ) (g := RootScalarPeriodR10.exponent hκ u)
      (f := fun q : ℂ × ℂ => q.1) (x := p) (analytic_exponent hκ u z hz) analyticAt_fst
  have he : AnalyticAt ℂ (fun q : ℂ × ℂ => exponential L q.1) p := by
    exact (((analyticAt_const (v := I)).mul analyticAt_fst).mul
      (analyticAt_const (v := (L : ℂ)))).cexp
  have ht := hg.cexp.add (he.div hg.cexp (exp_ne_zero _))
  have hd := hg.cexp.sub (he.div hg.cexp (exp_ne_zero _))
  have hD := difference_ne hκ u z hz
  have hs : p.2 = transfer (exponential L p.1) (exponent hκ u p.1) :=
    transfer_identity hκ u z hz
  have hq : AnalyticAt ℂ (fun q : ℂ × ℂ =>
      1+(q.2^2-transfer (exponential L q.1) (exponent hκ u q.1)^2)/
        difference (exponential L q.1) (exponent hκ u q.1)^2) p :=
    analyticAt_const.add (((analyticAt_snd.pow 2).sub (ht.pow 2)).div (hd.pow 2) (pow_ne_zero 2 hD))
  have hp := hq.cpow (analyticAt_const (v := (2 : ℂ)⁻¹)) (by
    simp [hs,Complex.slitPlane])
  have hr := (analyticAt_snd.add (hd.mul hp)).div_const (c := (2 : ℂ))
  have hratio := hr.div hg.cexp (exp_ne_zero _)
  have hslit : root (exponential L p.1) (exponent hκ u p.1) p.2 /
      exp (exponent hκ u p.1) ∈ slitPlane := by
    rw [hs,root_at,div_self (exp_ne_zero _)]
    simp [Complex.slitPlane]
  exact hg.add (hratio.clog hslit)

/-- The branch exponent solves the actual quadratic wherever its defining
root and logarithm are valid. This constraint is independent of the period. -/
theorem germ_quadratic (hκ : 0 < κ) (u : L2T L) (p : ℂ × ℂ)
    (hD : difference (exponential L p.1) (exponent hκ u p.1) ≠ 0)
    (hr : root (exponential L p.1) (exponent hκ u p.1) p.2 /
      exp (exponent hκ u p.1) ≠ 0) :
    exp (germ hκ u p)^2-p.2*exp (germ hκ u p)+exponential L p.1 = 0 := by
  have hE : exp (germ hκ u p) =
      root (exponential L p.1) (exponent hκ u p.1) p.2 := by
    unfold germ lambda localLog
    rw [exp_add,exp_log hr]
    field_simp [exp_ne_zero]
  rw [hE]
  exact root_quadratic _ _ _ hD

end QuantumNLS.ActualModelPeriodGermR52a
#print axioms QuantumNLS.ActualModelPeriodGermR52a.analytic_exponent
#print axioms QuantumNLS.ActualModelPeriodGermR52a.analytic_germ
#print axioms QuantumNLS.ActualModelPeriodGermR52a.germ_quadratic

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelPeriodGermR52a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelPeriodGermR52a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"Round52 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
