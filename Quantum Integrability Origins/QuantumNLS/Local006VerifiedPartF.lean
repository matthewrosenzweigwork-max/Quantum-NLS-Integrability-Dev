import QuantumNLS.Local006FifthF

/-! LOCAL-006: one named theorem collecting the clauses proved in round 17.
This is explicitly a PARTIAL source theorem: the cubic below is the genuine
Taylor coefficient, not yet identified with the printed g_3. Absolute Fourier
coefficient majorants are not claimed. No gap is turned into a hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local006.VerifiedPartF
open QuantumNLS.PhysicalTensor QuantumNLS.Local006.CollectiveF
  QuantumNLS.Local006.FirstJetF QuantumNLS.Local006.FifthF

variable {L κ r : ℝ} [Fact (0 < L)]

/-- The strongest source-chart statement proved here. The printed g_3
identification and the three absolute Fourier-majorant clauses remain gaps. -/
theorem reset_collective_spectral_verified_part (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ (G : L2T L → Seq)
      (p : FormalMultilinearSeries ℝ (L2T L) Seq)
      (e : OpenPartialHomeomorph (L2T L) Seq),
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧ HasFPowerSeriesAt G p 0 ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n) ∧
      G 0 = 0 ∧ fderiv ℝ G 0 = (fourierR L : L2T L →L[ℝ] Seq) ∧
      (e : L2T L → Seq) = G ∧ (0 : L2T L) ∈ e.source ∧ (0 : Seq) ∈ e.target ∧
      e.symm 0 = 0 ∧ AnalyticAt ℝ (e.symm : Seq → L2T L) 0 ∧
      (∀ k : ℕ, Even k → ∀ u : L2T L, p k (fun _ => u) = 0) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖G u - fourierR L u - p 3 (fun _ => u)‖ ≤ C * ‖u‖ ^ 5) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖fderiv ℝ G u - (fourierR L : L2T L →L[ℝ] Seq)‖ ≤ C * ‖u‖ ^ 2) := by
  obtain ⟨ρ, hρ, C, hC, G, p, hG, hp, hGe, hG0, hF, heven, h5, hder⟩ :=
    source_fifth_order hL hκ hr hr2
  have ha : AnalyticAt ℝ G 0 := hG 0 (mem_ball_self hρ)
  have hd : HasStrictFDerivAt G (fourierR L : L2T L →L[ℝ] Seq) 0 := hF ▸ ha.hasStrictFDerivAt
  let e := hd.toOpenPartialHomeomorph G
  have he : (e : L2T L → Seq) = G := rfl
  have hs : (0 : L2T L) ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  have ht : (0 : Seq) ∈ e.target := by simpa [he, hG0] using e.map_source hs
  have hi : e.symm 0 = 0 := by simpa [he, hG0] using e.left_inv hs
  have hai : AnalyticAt ℝ (e.symm : Seq → L2T L) 0 := by
    simpa [he, hG0] using e.analyticAt_symm' hs (by simpa [he] using ha) (by simpa [he] using hF)
  exact ⟨ρ, hρ, C, hC, G, p, e, hG, hp, hGe, hG0, hF, he, hs, ht, hi, hai, heven, h5, hder⟩

end QuantumNLS.Local006.VerifiedPartF
#print axioms QuantumNLS.Local006.VerifiedPartF.reset_collective_spectral_verified_part

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.VerifiedPartF." ||
        n.toString.startsWith "_private.QuantumNLS.Local006VerifiedPartF" then
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
  Lean.logInfo m!"Local006VerifiedPartF audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
