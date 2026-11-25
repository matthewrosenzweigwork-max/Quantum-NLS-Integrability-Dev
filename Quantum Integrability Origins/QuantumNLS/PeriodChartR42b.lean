import QuantumNLS.PeriodMeasureR42b

/-! Apply R-CA92819A to the actual selected R41b chart and its transported
unit-period competitor. No chart or normalization conclusion is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Metric Filter Topology
namespace QuantumNLS.PeriodChartR42b
open PhysicalTensor (L2T)
open D01LocalPrimitive (K)
open PeriodFieldR42b PeriodMeasureR42b
open Def021ChartR41b
open GlobalCompatR47a
variable {L κ : ℝ} [Fact (0 < L)]

/-- Bind all R47a extension premises to the selected R41b witnesses. -/
theorem selected_extension (hκ : 0 < κ) :
    Extension κ hκ (localChart L).d ((localChart L).Φ κ) ((localChart L).Ψ κ)
      (Phi L κ) (chart L κ hκ).Ψ := by
  rw [Phi_eq L κ hκ]
  let c := chart L κ hκ
  refine ⟨c.analytic, c.inverse_analytic, c.left_inverse, c.right_inverse, ?_, c.actions, c.local_agreement⟩
  refine ⟨⟨c.Ψ, c.left_inverse, c.right_inverse, fun z => (c.inverse_analytic z).differentiableAt⟩,
    fun u => (c.analytic u).differentiableAt, ?_, c.symplectic⟩
  intro u
  obtain ⟨e, he, _⟩ := c.differential u
  exact ⟨e, congrArg (fun A : L2T L →L[ℝ] K => (A : L2T L → K)) he.fderiv.symm⟩

/-- Real period equivalence through the established real Fourier equivalences. -/
def periodCLE (L : ℝ) [Fact (0 < L)] : L2T L ≃L[ℝ] L2T 1 :=
  (Local021.Setting.Fcle L).trans (Local021.Setting.Fcle 1).symm

section Isometry
variable {H E F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem isometry_strong (e : H ≃ₗᵢ[ℂ] E) : StrongSymplectic.IsStronglySymplectic (e : H → E) := by
  have h := ResetNormalizationUniqueness.isStronglySymplecticOn_isometry e
    (s := Set.univ) (t := Set.univ) (fun _ _ => trivial) (fun _ _ => trivial)
  obtain ⟨g, _hmem, hl, hr, hg⟩ := h.exists_inverse
  exact ⟨⟨g, fun u => hl u trivial, fun z => hr z trivial, fun z => hg z trivial⟩,
    fun u => h.differentiable u trivial, fun u => h.deriv_iso u trivial,
    fun u => h.symplectic u trivial⟩

omit [CompleteSpace H] [CompleteSpace E] [CompleteSpace F] in
theorem derivative_comp_isometry (e : H ≃ₗᵢ[ℂ] E) (f : E → F) (x v : H)
    (hf : DifferentiableAt ℝ f (e x)) :
    fderiv ℝ (fun u => f (e u)) x v = fderiv ℝ f (e x) (e v) := by
  let eR : H →L[ℝ] E := e.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
  have hd : HasFDerivAt (e : H → E) eR x := eR.hasFDerivAt
  exact congrArg (fun A : H →L[ℝ] F => A v) (hf.hasFDerivAt.comp x hd).fderiv
end Isometry

theorem period_strong : StrongSymplectic.IsStronglySymplectic (period L) := by
  have he : period L = (periodEquiv L : L2T L → L2T 1) := funext (period_eq L)
  rw [he]
  exact isometry_strong (periodEquiv L)

/-- The literal physical real involution commutes with period conversion. -/
theorem period_real (u : L2T L) :
    period L (ResetNormalizationUniqueness.Cphys L u) =
      ResetNormalizationUniqueness.Cphys 1 (period L u) := by
  apply (QuantumNLS.Fourier.fourierL2 1).injective
  rw [fourier_period]
  apply lp.ext
  funext n
  rw [ResetNormalizationUniqueness.fourier_Cphys,
    ResetNormalizationUniqueness.fourier_Cphys, fourier_period]

/-- Instantiate the uniqueness clause of the named R-CA92819A theorem,
then identify its family with the independently selected R41b family. -/
theorem selected_unique (hκ : 0 < κ) (G : L2T L → K)
    (hG : StrongSymplectic.IsStronglySymplectic G)
    (ha : ∀ u, AnalyticAt ℝ G u)
    (hm : ∀ u n, ‖G u n‖^2 = (RootIndexedMasses.masses hκ u).1 n)
    (hD : ∀ v, fderiv ℝ G 0 v = QuantumNLS.Fourier.fourierL2 L v)
    (hc : ∀ u, G (ResetNormalizationUniqueness.Cphys L u) = star (G u)) :
    G = Phi L κ := by
  obtain ⟨d, CL, _hd, _hCL, Φl, Ψl, _hl, ⟨Φ, Ψ, hf⟩, hcompat⟩ := global_compatibility L
  obtain ⟨_cov, _deriv, _plane, _real, _joint, _invjoint, _est, hu, _rest⟩ :=
    (hcompat Φ Ψ hf).1 κ hκ
  let h := selected_extension (L := L) hκ
  let lc := localChart L
  have he : Phi L κ = Φ κ := hu (Phi L κ) h.strong h.analytic h.moduli
    (fun v => by rw [h.fourier_derivative lc.positive lc.spec]; rfl)
    (h.real_normalization lc.positive lc.spec)
  exact (hu G hG ha hm hD hc).trans he.symm

/-- First equality of norm:period-coupling for the selected chart family. -/
theorem period_conversion (hκ : 0 < κ) (u : L2T L) :
    Phi L κ u = Phi 1 (κ*L) (period L u) := by
  have hL : 0 < L := Fact.out
  have hκL : 0 < κ*L := mul_pos hκ hL
  let h1 := selected_extension (L := 1) hκL
  let lc1 := localChart 1
  have ha : ∀ v, AnalyticAt ℝ (fun w : L2T L => Phi 1 (κ*L) (period L w)) v := by
    intro v
    have he : AnalyticAt ℝ (period L) v := by
      have H : period L = (periodEquiv L : L2T L → L2T 1) := funext (period_eq L)
      rw [H]
      exact (periodCLE L).analyticAt v
    exact (h1.analytic _).comp he
  have hs : StrongSymplectic.IsStronglySymplectic (fun w : L2T L => Phi 1 (κ*L) (period L w)) :=
    (period_strong (L := L)).comp h1.strong
  have hm : ∀ v n, ‖Phi 1 (κ*L) (period L v) n‖^2 = (RootIndexedMasses.masses hκ v).1 n := by
    intro v n
    rw [h1.moduli, masses_scale hκ v n]
  have hD : ∀ v, fderiv ℝ (fun w : L2T L => Phi 1 (κ*L) (period L w)) 0 v =
      QuantumNLS.Fourier.fourierL2 L v := by
    intro v
    have he : period L = (periodEquiv L : L2T L → L2T 1) := funext (period_eq L)
    rw [he]
    have hd := derivative_comp_isometry (periodEquiv L) (Phi 1 (κ*L)) 0 v
      (h1.analytic _).differentiableAt
    calc
      fderiv ℝ (fun w : L2T L => Phi 1 (κ*L) (periodEquiv L w)) 0 v =
          fderiv ℝ (Phi 1 (κ*L)) (periodEquiv L 0) (periodEquiv L v) := hd
      _ = QuantumNLS.Fourier.fourierL2 L v := by
        rw [map_zero, h1.fourier_derivative lc1.positive lc1.spec]
        change QuantumNLS.Fourier.fourierL2 1 (periodEquiv L v) = QuantumNLS.Fourier.fourierL2 L v
        simp [periodEquiv]
  have hc : ∀ v, Phi 1 (κ*L) (period L (ResetNormalizationUniqueness.Cphys L v)) =
      star (Phi 1 (κ*L) (period L v)) := by
    intro v
    rw [period_real, h1.real_normalization lc1.positive lc1.spec]
  have H := selected_unique hκ _ hs ha hm hD hc
  exact congrFun H u |>.symm

end QuantumNLS.PeriodChartR42b

#print axioms QuantumNLS.PeriodChartR42b.selected_extension
#print axioms QuantumNLS.PeriodChartR42b.isometry_strong
#print axioms QuantumNLS.PeriodChartR42b.derivative_comp_isometry
#print axioms QuantumNLS.PeriodChartR42b.period_strong
#print axioms QuantumNLS.PeriodChartR42b.period_real
#print axioms QuantumNLS.PeriodChartR42b.selected_unique
#print axioms QuantumNLS.PeriodChartR42b.period_conversion

-- R42b final aggregate audit
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PeriodChartR42b." ||
        n.toString.startsWith "_private.QuantumNLS.PeriodChartR42b." then
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
  Lean.logInfo m!"R42b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
