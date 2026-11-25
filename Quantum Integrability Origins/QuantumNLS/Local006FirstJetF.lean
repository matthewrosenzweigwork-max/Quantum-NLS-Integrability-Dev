import QuantumNLS.Local006CollectiveF

/-! LOCAL-006: identify the derivative of the actual collective chart with the
DEF-001 unitary Fourier transform and construct its real analytic local inverse.
The scalar cubic estimate is used for uniqueness of each first derivative,
never as a collective norm estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology Asymptotics
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local006.FirstJetF
open QuantumNLS.Local006.CollectiveF QuantumNLS.PhysicalTensor

section Scalar
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A cubic scalar remainder determines the first derivative. -/
lemma first_jet {f : E → F} (T : E →L[ℝ] F) {ρ C : ℝ} (hρ : 0 < ρ)
    (hb : ∀ u ∈ ball (0 : E) ρ, ‖f u - T u‖ ≤ C * ‖u‖ ^ 3) :
    f 0 = 0 ∧ HasFDerivAt f T 0 := by
  have hz : f 0 = 0 := by
    have h := hb 0 (mem_ball_self hρ)
    simpa using norm_le_zero_iff.mp (by simpa using h : ‖f 0‖ ≤ 0)
  have ho : (fun u => f u - T u) =O[𝓝 0] fun u : E => ‖u‖ ^ 3 := by
    refine isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [ball_mem_nhds (0 : E) hρ] with u hu
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖u‖ ^ 3)] using hb u hu
  have hlo := ho.trans_isLittleO (isLittleO_norm_pow_id (E' := E) (n := 3) (by norm_num))
  refine ⟨hz, ?_⟩
  rw [hasFDerivAt_iff_isLittleO]
  simpa [hz] using hlo
end Scalar

variable {L κ r : ℝ} [Fact (0 < L)]

def fourierR (L : ℝ) [Fact (0 < L)] : L2T L ≃L[ℝ] Seq :=
  { toLinearEquiv := (QuantumNLS.Fourier.fourierL2 L).toLinearEquiv.restrictScalars ℝ
    continuous_toFun := (QuantumNLS.Fourier.fourierL2 L).continuous
    continuous_invFun := (QuantumNLS.Fourier.fourierL2 L).symm.continuous }

/-- Coordinate first jets determine the derivative of an already established
Banach-valued analytic map. No claim of square summability of coordinate bounds
is used. -/
theorem collective_first_jet {G : L2T L → Seq} {ρ C : ℝ} (hρ : 0 < ρ)
    (hG : AnalyticOnNhd ℝ G (ball 0 ρ))
    (hb : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
      ‖G u n - QuantumNLS.Fourier.fourierL2 L u n‖ ≤ C * ‖u‖ ^ 3) :
    G 0 = 0 ∧ fderiv ℝ G 0 = (fourierR L : L2T L →L[ℝ] Seq) := by
  let F : L2T L →L[ℝ] Seq := fourierR L
  let e : ℤ → Seq →L[ℝ] ℂ := fun n => lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 n
  have hcoord : ∀ n, (fun u => G u n) 0 = 0 ∧
      HasFDerivAt (fun u => G u n) ((e n).comp F) 0 := by
    intro n
    apply first_jet (f := fun u => G u n) ((e n).comp F) (C := C) hρ
    intro u hu
    exact hb u hu n
  have hG0 : G 0 = 0 := lp.ext (funext fun n => (hcoord n).1)
  refine ⟨hG0, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  have hd := (e n).hasFDerivAt.comp 0 ((hG 0 (mem_ball_self hρ)).differentiableAt.hasFDerivAt)
  have h := hd.unique (hcoord n).2
  exact congrArg (fun T : L2T L →L[ℝ] ℂ => T v) h

/-- The source chart admits a real analytic inverse at zero. The local inverse
is exhibited as an open partial homeomorphism with analytic inverse germ. -/
theorem source_chart_inverse (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : L2T L → Seq,
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n) ∧
      G 0 = 0 ∧ fderiv ℝ G 0 = (fourierR L : L2T L →L[ℝ] Seq) ∧
      ∃ e : OpenPartialHomeomorph (L2T L) Seq,
        (e : L2T L → Seq) = G ∧ (0 : L2T L) ∈ e.source ∧ (0 : Seq) ∈ e.target ∧
        e.symm 0 = 0 ∧ AnalyticAt ℝ (e.symm : Seq → L2T L) 0 := by
  obtain ⟨ρ, hρ, C, hC, G, hG, hGe, hb, hsc⟩ := exists_chart hL hκ hr hr2
  obtain ⟨hG0, hF⟩ := collective_first_jet hρ hG hb
  have ha : AnalyticAt ℝ G 0 := hG 0 (mem_ball_self hρ)
  have hd : HasStrictFDerivAt G (fourierR L : L2T L →L[ℝ] Seq) 0 := hF ▸ ha.hasStrictFDerivAt
  let e := hd.toOpenPartialHomeomorph G
  have he : (e : L2T L → Seq) = G := rfl
  have hs : (0 : L2T L) ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  have ht : (0 : Seq) ∈ e.target := by simpa [he, hG0] using e.map_source hs
  have hi : e.symm 0 = 0 := by simpa [he, hG0] using e.left_inv hs
  have hai : AnalyticAt ℝ (e.symm : Seq → L2T L) 0 := by
    simpa [he, hG0] using e.analyticAt_symm' hs (by simpa [he] using ha) (by simpa [he] using hF)
  exact ⟨ρ, hρ, G, hG, hGe, hG0, hF, e, he, hs, ht, hi, hai⟩

end QuantumNLS.Local006.FirstJetF
#print axioms QuantumNLS.Local006.FirstJetF.first_jet
#print axioms QuantumNLS.Local006.FirstJetF.collective_first_jet
#print axioms QuantumNLS.Local006.FirstJetF.source_chart_inverse

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.FirstJetF." ||
        n.toString.startsWith "_private.QuantumNLS.Local006FirstJetF" then
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
  Lean.logInfo m!"Local006FirstJetF audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
