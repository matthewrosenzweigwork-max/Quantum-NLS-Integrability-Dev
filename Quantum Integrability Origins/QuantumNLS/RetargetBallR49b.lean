import QuantumNLS.RetargetSelectionR49b

/-! The fixed-sector rough-ball passage for the selected Q06 gauge. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Filter Topology
open scoped ComplexConjugate

namespace QuantumNLS.RetargetBallR49b
open PhysicalTensor Occupation OccupationHilbert FullOccupationAffinity FiniteCellGauge
open RetargetAnglesR48b RetargetStageR48b RetargetWeightsR48b RetargetCellR48b
open RetargetAssemblyR48b RetargetRoughR48b RetargetFinalProofR48b RetargetAffinityR48b
open RetargetSelectionR49b
variable {L κ : ℝ} [Fact (0 < L)]

/-- At fixed particle number, the same stage gauge controls both Cartesian
residuals on every strictly smaller rough unit ball. -/
theorem cartesian_on_ball (hκ : 0 < κ) {j n : ℕ} {q : Arr (n+1) → Phase}
    (hs : Stage (L := L) hκ j n q) {R : ℝ} (hR : R < j) (u : L2T L)
    (hu : u ∈ unitBall (L := L) R) (a b : ↥(labels j)) :
    let g := coefficients hκ n u
    let z := coordinate hκ u a.1 * conj (coordinate hκ u b.1)
    ‖cartesian q a.1 b.1 g - z • g‖ ≤ stageBound j ∧
    ‖(cartesian q a.1 b.1).adjoint g - conj z • g‖ ≤ stageBound j := by
  have hmem := mem_smooth_closure R j hR hu
  refine ⟨(stage_closure hκ hs u hmem a b).1, ?_⟩
  rw [cartesian_adjoint]
  have hconj : conj (coordinate hκ u a.1 * conj (coordinate hκ u b.1)) =
      coordinate hκ u b.1 * conj (coordinate hκ u a.1) := by simp [mul_comm]
  rw [hconj]
  exact (stage_closure hκ hs u hmem b a).1

/-- The phase passage holds at each fixed sector where the two tested
actions strictly exceed the stage floor. The adjoint uses the reversed edge. -/
theorem phase_on_ball (hκ : 0 < κ) {j n : ℕ} {q : Arr (n+1) → Phase}
    (hs : Stage (L := L) hκ j n q) {R : ℝ} (hR : R < j) (u : L2T L)
    (hu : u ∈ unitBall (L := L) R) (a b : ↥(labels j)) (hab : a.1 ≠ b.1)
    (ha : stageBound j < ‖coordinate hκ u a.1‖^2)
    (hb : stageBound j < ‖coordinate hκ u b.1‖^2) :
    let g := coefficients hκ n u
    let ζ := pairPhase (coordinate hκ u a.1) (coordinate hκ u b.1)
    ‖FiniteCellGauge.W q a.1 b.1 g - ζ.1 • g‖ ≤ stageBound j ∧
    ‖(FiniteCellGauge.W q a.1 b.1).adjoint g - conj ζ.1 • g‖ ≤ stageBound j := by
  have hmem := mem_smooth_closure R j hR hu
  refine ⟨(stage_closure hκ hs u hmem a b).2 hab ha hb, ?_⟩
  rw [W_adjoint q a.1 b.1 hab, ← phase_reverse]
  exact (stage_closure hκ hs u hmem b a).2 hab.symm hb ha

/-- All the frozen rough-limit clauses for the explicitly selected gauge. -/
theorem selected_gauge_conclusion (hκ : 0 < κ) :
    GaugeConclusion (L := L) hκ (sectorStage (L := L) hκ) (sectorGauge (L := L) hκ) := by
  let s := sectorStage (L := L) hκ
  let q := sectorGauge (L := L) hκ
  obtain ⟨hs, hs_atTop, hstage⟩ := select_family_explicit (L := L) hκ
  have hR_atTop (R : ℝ) : ∀ᶠ n in atTop, R < (s n : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hs_atTop).eventually (eventually_gt_atTop R)
  have hpos : ∀ᶠ n in atTop, 0 < s n := hs_atTop.eventually (eventually_gt_atTop 0)
  have hb_zero := stageBound_tendsto.comp hs_atTop
  refine ⟨hs, hs_atTop, ?_, ?_⟩
  · intro R ε hε
    filter_upwards [hR_atTop R, hpos,
      hb_zero.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with n hnR hn hne
    intro u hu a b
    have ⟨hf, hr⟩ := cartesian_on_ball hκ (hstage n hn).1 hnR u hu a b
    have hsmall : stageBound (s n) < ε/2 := hne
    exact (add_le_add hf hr).trans (by linarith only [hsmall])
  · intro R ρ ε hρ hε
    let d := min ε (1/2)
    have hd : 0 < d := lt_min hε (by norm_num)
    have hdε : d ≤ ε := min_le_left _ _
    have hhalf : d ≤ 1/2 := min_le_right _ _
    have hdsq2 : 2*d^2 ≤ ε :=
      (show 2*d^2 ≤ d by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hhalf)]).trans hdε
    filter_upwards [hR_atTop R, hpos, hb_zero.eventually (gt_mem_nhds hρ),
      hb_zero.eventually (gt_mem_nhds hd)] with n hnR hn hnρ hnd
    intro u hu a b hab g z w ζ ha hb
    have ⟨hf, hr⟩ := phase_on_ball hκ (hstage n hn).1 hnR u hu a b hab
      (hnρ.trans_le ha) (hnρ.trans_le hb)
    obtain ⟨h1, h2, hA, hD, hc⟩ := phase_errors (q n) a.1 b.1 hab ζ
      ⟨g, coefficients_unit hκ n u hu.1⟩ d hd.le (hf.trans hnd.le) (hr.trans hnd.le)
    have hdsq : d^2 ≤ ε := by linarith [sq_nonneg d]
    exact ⟨hf.trans (hnd.le.trans hdε), hr.trans (hnd.le.trans hdε),
      h1.trans hdsq2, h2.trans hdsq2, hA.trans hdsq, hD.trans hdsq, hc.trans hdε⟩

end QuantumNLS.RetargetBallR49b

#print axioms QuantumNLS.RetargetBallR49b.cartesian_on_ball

#print axioms QuantumNLS.RetargetBallR49b.phase_on_ball

#print axioms QuantumNLS.RetargetBallR49b.selected_gauge_conclusion

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.RetargetBallR49b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetBallR49b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R49b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
