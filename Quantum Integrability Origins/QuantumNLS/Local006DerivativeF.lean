import QuantumNLS.Local006FirstJetF

/-! LOCAL-006: the collective operator-norm derivative bound on a full ball.
An analytic even Banach-valued map has a quadratic remainder; apply this to Dg,
whose evenness follows by differentiating the actual source parity identity. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology Asymptotics
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local006.DerivativeF
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Bridge
  QuantumNLS.PhysicalTensor QuantumNLS.Local003Analytic QuantumNLS.Local003Isometry
  QuantumNLS.Local006.CollectiveF QuantumNLS.Local006.FirstJetF

section Even
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma even_derivative_zero {H : E → F} (hH : DifferentiableAt ℝ H 0)
    (he : (fun x => H (-x)) =ᶠ[𝓝 0] H) : fderiv ℝ H 0 = 0 := by
  have h1 : HasFDerivAt (fun x => H (-x)) (-fderiv ℝ H 0) 0 := by
    have hd : HasFDerivAt H (fderiv ℝ H 0) (-(0 : E)) := by simpa using hH.hasFDerivAt
    simpa [Function.comp_def] using hd.comp 0 ((hasFDerivAt_id (0 : E)).neg)
  have h2 : -fderiv ℝ H 0 = fderiv ℝ H 0 :=
    (h1.congr_of_eventuallyEq he.symm).unique hH.hasFDerivAt
  have hz : (2 : ℝ) • fderiv ℝ H 0 = 0 := by
    rw [two_smul]
    calc fderiv ℝ H 0 + fderiv ℝ H 0 = -fderiv ℝ H 0 + fderiv ℝ H 0 :=
          congrArg (fun T => T + fderiv ℝ H 0) h2.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

lemma analytic_even_quadratic {H : E → F} (hH : AnalyticAt ℝ H 0)
    (he : (fun x => H (-x)) =ᶠ[𝓝 0] H) :
    (fun x => H x - H 0) =O[𝓝 0] fun x : E => ‖x‖ ^ 2 := by
  have hd0 := even_derivative_zero hH.differentiableAt he
  obtain ⟨p, hp⟩ := hH
  have hp1 : p 1 = 0 := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    simpa [← hp.fderiv_eq] using hd0
  have hs : ∀ x : E, p.partialSum 2 x = H 0 := by
    intro x
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, hp1, hp.coeff_zero]
  simpa only [zero_add, hs] using hp.isBigO_sub_partialSum_pow 2

lemma derivative_even {G : E → F} {ρ : ℝ}
    (hG : AnalyticOnNhd ℝ G (ball 0 ρ))
    (ho : ∀ u ∈ ball (0 : E) ρ, G (-u) = -G u) :
    ∀ u ∈ ball (0 : E) ρ, fderiv ℝ G (-u) = fderiv ℝ G u := by
  intro u hu
  have hnu : -u ∈ ball (0 : E) ρ := by simpa [mem_ball_zero_iff] using hu
  have h1 : HasFDerivAt (fun x => G (-x)) (-fderiv ℝ G (-u)) u := by
    simpa [Function.comp_def] using (hG (-u) hnu).differentiableAt.hasFDerivAt.comp u ((hasFDerivAt_id u).neg)
  have he : (fun x => G (-x)) =ᶠ[𝓝 u] fun x => -G x :=
    eventuallyEq_of_mem (isOpen_ball.mem_nhds hu) (fun x hx => ho x hx)
  have h2 := (hG u hu).differentiableAt.hasFDerivAt.neg
  exact neg_injective ((h1.congr_of_eventuallyEq he.symm).unique h2)
end Even

variable {L κ r : ℝ} [Fact (0 < L)]

/-- Parity of the actual normalized lower-left entry on the common ball. -/
theorem scalarG_odd (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (u : L2T L) (hu : ‖u‖ < QuantumNLS.LocalSpectral.Round27.compressionRadius κ L r) (n : ℤ) :
    scalarG L κ r (-u) n = -scalarG L κ r u n := by
  let v := toInterval L u
  have hv : ‖v‖ < QuantumNLS.LocalSpectral.Round27.compressionRadius κ L r := by
    simpa [v, norm_toInterval] using hu
  have h := (QuantumNLS.Local003Odd.entries_parity hL hr hr2 n v hv).2
  have he := toInterval_coe L u
  have hn : ((-v : Lp ℂ 2 (μI L)) : ℝ → ℂ) =ᵐ[μI L] circleRep (-u) := by
    have hn := toInterval_coe L (-u)
    simpa [map_neg, v] using hn
  rw [QuantumNLS.Local003Odd.Bf_congr he, QuantumNLS.Local003Odd.Bf_congr hn] at h
  simp only [scalarG, h, mul_neg]

/-- The requested collective derivative estimate, for the actual source map,
with the constant and the common radius proved to exist. -/
theorem source_collective_derivative (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ G : L2T L → Seq,
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n) ∧
      G 0 = 0 ∧ fderiv ℝ G 0 = (fourierR L : L2T L →L[ℝ] Seq) ∧
      (∀ u ∈ ball (0 : L2T L) ρ, G (-u) = -G u) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖fderiv ℝ G u - (fourierR L : L2T L →L[ℝ] Seq)‖ ≤ C * ‖u‖ ^ 2) := by
  obtain ⟨ρ0, hρ0, C0, hC0, G, hG, hGe, hb, hsc⟩ := exists_chart hL hκ hr hr2
  obtain ⟨hG0, hF⟩ := collective_first_jet hρ0 hG hb
  let δ := min ρ0 (QuantumNLS.LocalSpectral.Round27.compressionRadius κ L r)
  have hδ : 0 < δ := lt_min hρ0 (QuantumNLS.LocalSpectral.Round27.compressionRadius_pos κ L r)
  have hm : ball (0 : L2T L) δ ⊆ ball 0 ρ0 := ball_subset_ball (min_le_left _ _)
  have hodd : ∀ u ∈ ball (0 : L2T L) δ, G (-u) = -G u := by
    intro u hu
    have hnu : -u ∈ ball (0 : L2T L) δ := by simpa [mem_ball_zero_iff] using hu
    apply lp.ext
    funext n
    rw [lp.coeFn_neg, Pi.neg_apply, hGe (-u) (hm hnu) n, hGe u (hm hu) n]
    exact scalarG_odd hL hr hr2 u ((mem_ball_zero_iff.mp hu).trans_le (min_le_right _ _)) n
  have hD : AnalyticOnNhd ℝ (fderiv ℝ G) (ball 0 δ) := (hG.mono hm).fderiv
  have he : (fun u => fderiv ℝ G (-u)) =ᶠ[𝓝 0] fderiv ℝ G :=
    eventuallyEq_of_mem (ball_mem_nhds (0 : L2T L) hδ) (derivative_even (hG.mono hm) hodd)
  have ho := analytic_even_quadratic (hD 0 (mem_ball_self hδ)) he
  obtain ⟨C, hbound⟩ := isBigO_iff.mp ho
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp hbound
  let ρ := min δ ε
  have hρ : 0 < ρ := lt_min hδ hε
  have hmδ : ball (0 : L2T L) ρ ⊆ ball 0 δ := ball_subset_ball (min_le_left _ _)
  have hmε : ball (0 : L2T L) ρ ⊆ ball 0 ε := ball_subset_ball (min_le_right _ _)
  refine ⟨ρ, hρ, max C 0, le_max_right _ _, G, hG.mono (hmδ.trans hm),
    fun u hu n => hGe u (hm (hmδ hu)) n, hG0, hF, fun u hu => hodd u (hmδ hu), ?_⟩
  intro u hu
  have h := hεb (mem_ball.mp (hmε hu))
  rw [hF] at h
  have hn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  calc ‖fderiv ℝ G u - (fourierR L : L2T L →L[ℝ] Seq)‖ ≤ C * ‖u‖ ^ 2 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hn] using h
    _ ≤ max C 0 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) hn

end QuantumNLS.Local006.DerivativeF
#print axioms QuantumNLS.Local006.DerivativeF.analytic_even_quadratic
#print axioms QuantumNLS.Local006.DerivativeF.scalarG_odd
#print axioms QuantumNLS.Local006.DerivativeF.source_collective_derivative

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.DerivativeF." ||
        n.toString.startsWith "_private.QuantumNLS.Local006DerivativeF" then
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
  Lean.logInfo m!"Local006DerivativeF audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
