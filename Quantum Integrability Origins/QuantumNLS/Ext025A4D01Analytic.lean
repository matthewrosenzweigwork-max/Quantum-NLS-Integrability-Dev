import QuantumNLS.Ext025A4RealFlow

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Topology Filter
open scoped NNReal
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.Ext025A4D01Analytic
open QuantumNLS.D01LocalPrimitive QuantumNLS.TerraMultiRound18Flow
open QuantumNLS.ProductTorusComplexification QuantumNLS.ProductTorusComplexMultilinear
open QuantumNLS.Ext025A4AnalyticIntegral QuantumNLS.Ext025A4RealFlow
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem lipschitz_const_smul {𝕜 E : Type*} [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → E} {U : Set E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f U) (c : 𝕜) :
    LipschitzOnWith (‖c‖₊ * K) (fun z => c • f z) U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnnorm]
  simpa only [dist_eq_norm, mul_assoc] using
    mul_le_mul_of_nonneg_left (hf.dist_le_mul x hx y hy) (norm_nonneg c)

/-- The real Picard curve agrees with the actual global flow, by uniqueness
on the compact union of their images. No initial-value continuity is used. -/
theorem real_curve_eq_flow (S : Hyp H) (t : ℝ) {x : H} {β : ℝ → H}
    (hc : Continuous β) (h0 : β 0 = x)
    (hd : ∀ s ∈ Icc (-1 : ℝ) 2,
      HasDerivWithinAt β (t • S.Y (β s)) (Icc (-1 : ℝ) 2) s) :
    EqOn β (fun s => flow S (t*s) x) (Icc (-1 : ℝ) 2) := by
  let γ : ℝ → H := fun s => flow S (t*s) x
  have hγd (s : ℝ) : HasDerivAt γ (t • S.Y (γ s)) s := by
    have hh := ((flow_spec S x).2 (t*s)).scomp s ((hasDerivAt_id s).const_mul t)
    simpa only [γ, mul_one, Function.comp_def, id_eq] using hh
  have hγ : Continuous γ := continuous_iff_continuousAt.mpr (fun s => (hγd s).continuousAt)
  let K := β '' Icc (-1 : ℝ) 2 ∪ γ '' Icc (-1 : ℝ) 2
  have hK : IsCompact K := (isCompact_Icc.image hc).union (isCompact_Icc.image hγ)
  obtain ⟨L, hL⟩ := QuantumNLS.TerraMultiRound17CompactPartial.field_lipschitz_on_compact S hK
  apply ODE_solution_unique_of_mem_Icc (v := fun _ z => t • S.Y z) (s := fun _ => K)
    (K := ‖t‖₊ * L) (fun _ _ => lipschitz_const_smul hL t)
    (by constructor <;> norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2)
    hc.continuousOn
    (fun s hs => (hd s ⟨hs.1.le,hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2))
    (fun s hs => Or.inl ⟨s, ⟨hs.1.le,hs.2.le⟩, rfl⟩)
    hγ.continuousOn (fun s _ => hγd s)
    (fun s hs => Or.inr ⟨s, ⟨hs.1.le,hs.2.le⟩, rfl⟩) ?_
  simpa only [γ, mul_zero, (flow_spec S x).1] using h0

/-- FTC makes the embedded real reference curve a fixed point of the
literal complex Picard operator. This proves reality and agreement by
contraction uniqueness, including negative original times. -/
theorem embedded_real_fixedPoint (S : Hyp H) {G : Cx H → Cx H} (hG : Continuous G)
    {a x : H} {r : ℝ} {β : ℝ → H} {t : ℝ}
    (hc : Continuous β) (h0 : β 0 = x)
    (hm : ∀ s, β s ∈ closedBall a r)
    (he : ∀ z ∈ closedBall a r, G (Cx.ι z) = Cx.ι (t • (S.Y z)))
    (hd : ∀ s ∈ Icc (-1 : ℝ) 2,
      HasDerivWithinAt β (t • S.Y (β s)) (Icc (-1 : ℝ) 2) s) :
    ∃ v : Path (Cx H), v ∈ closedBall (ContinuousMap.const Time (Cx.ι a)) r ∧
      picard G hG (1 : ℝ) (Cx.ι x,v) = v ∧
      ∀ s : Time, v s = Cx.ι (β s) := by
  let v : Path (Cx H) := ⟨fun s => Cx.ι (β s),
    (ιL.continuous.comp hc).comp continuous_subtype_val⟩
  have hv : v ∈ closedBall (ContinuousMap.const Time (Cx.ι a)) r := by
    rw [mem_closedBall, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (le_trans dist_nonneg (hm 0))).mpr
    intro s
    change ‖Cx.ι (β s) - Cx.ι a‖ ≤ r
    simpa only [← ι_sub, Cx.norm_ι, ← dist_eq_norm] using (show dist (β s) a ≤ r from hm s)
  refine ⟨v, hv, ?_, fun _ => rfl⟩
  ext s
  let α : ℝ → Cx H := fun s => Cx.ι (β s)
  have hα : Continuous α := ιL.continuous.comp hc
  have hαd (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : HasDerivAt α (G (α z)) z := by
    have hh := (hd z ⟨by linarith [hz.1], by linarith [hz.2]⟩).hasDerivAt
      (Icc_mem_nhds (by linarith [hz.1]) (by linarith [hz.2]))
    rw [he _ (hm z)]
    exact ιL.hasFDerivAt.comp_hasDerivAt z hh
  have hint : ∫ z in (0 : ℝ)..(s : ℝ), G (α z) = α s - α 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z hz => hαd z ((uIcc_subset_Icc (by constructor <;> norm_num) s.2) hz))
      ((hG.comp hα).intervalIntegrable _ _)
  have hext (z : ℝ) (hz : z ∈ uIcc (0 : ℝ) (s : ℝ)) :
      extend (QuantumNLS.Ext025A4AnalyticPath.superposition G hG v) z = G (α z) := by
    have hz' := (uIcc_subset_Icc (by constructor <;> norm_num) s.2) hz
    change G (Cx.ι (β (projIcc 0 1 zero_le_one z))) = G (Cx.ι (β z))
    rw [projIcc_of_mem _ hz']
  change Cx.ι x + (1 : ℂ) • (∫ z in (0 : ℝ)..(s : ℝ), _) = Cx.ι (β s)
  rw [one_smul, intervalIntegral.integral_congr hext, hint]
  dsimp [α]
  rw [h0]
  abel

end QuantumNLS.Ext025A4D01Analytic

namespace QuantumNLS.Ext025A4D01Analytic
open QuantumNLS.D01LocalPrimitive QuantumNLS.TerraMultiRound18Flow
open QuantumNLS.ProductTorusComplexification QuantumNLS.ProductTorusComplexMultilinear
open QuantumNLS.Ext025A4AnalyticIntegral QuantumNLS.Ext025A4RealFlow
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Local analyticity of the actual source flow, uniform in a neighborhood
of the center and in signed sufficiently small times. -/
theorem local_analytic_flow (S : Hyp H) (a : H) :
    ∃ ε > (0 : ℝ), ∃ τ > (0 : ℝ),
      ∀ x ∈ ball a ε, ∀ t : ℝ, |t| < τ → AnalyticAt ℝ (flow S t) x := by
  obtain ⟨R, hR, M, hM, K, Λ, hΛ, G, hc, hd, hLip, hb, hK, he⟩ :=
    local_field_data ((QuantumNLS.TerraMultiRound17D01Repair.analytic_field_and_local_solutions S).1 a)
  let τ := min (R / (16 * (M+1))) (1 / (2 * ((K : ℝ)+1)))
  have hτ : 0 < τ := lt_min (div_pos hR (by positivity)) (by positivity)
  refine ⟨R/4, by positivity, τ, hτ, fun x hx t ht => ?_⟩
  have htM : |t| * M < R/16 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 16*(M+1))).mp
      (ht.trans_le (min_le_left _ _))
    nlinarith [abs_nonneg t]
  have htK : |t| * (K : ℝ) < 1/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*((K : ℝ)+1))).mp
      (ht.trans_le (min_le_right _ _))
    nlinarith [abs_nonneg t, K.coe_nonneg]
  have hYr : LipschitzOnWith K S.Y (closedBall a (R/2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    have hzi : Cx.ι z ∈ closedBall (Cx.ι a) (R/2) := by
      simpa only [mem_closedBall, dist_eq_norm, ← ι_sub, Cx.norm_ι] using hz
    have hwi : Cx.ι w ∈ closedBall (Cx.ι a) (R/2) := by
      simpa only [mem_closedBall, dist_eq_norm, ← ι_sub, Cx.norm_ι] using hw
    have hh := hK.dist_le_mul _ hzi _ hwi
    rw [he z hz, he w hw] at hh
    simpa only [dist_eq_norm, ← ι_sub, Cx.norm_ι] using hh
  have hYb (z : H) (hz : z ∈ closedBall a (R/2)) : ‖S.Y z‖ ≤ M := by
    have hh : Cx.ι z ∈ closedBall (Cx.ι a) (R/2) := by
      simpa only [mem_closedBall, dist_eq_norm, ← ι_sub, Cx.norm_ι] using hz
    simpa only [he z hz, Cx.norm_ι] using hb _ hh
  let Gt : Cx H → Cx H := fun z => (t : ℂ) • G z
  have hct : Continuous Gt := hc.const_smul (t : ℂ)
  have hdt : DifferentiableOn ℂ Gt (ball (Cx.ι a) R) := hd.const_smul (t : ℂ)
  have hKt : LipschitzOnWith (‖t‖₊ * K) Gt (closedBall (Cx.ι a) (R/2)) := by
    simpa only [Complex.nnnorm_real] using lipschitz_const_smul hK (t : ℂ)
  have hbt (z : Cx H) (hz : z ∈ closedBall (Cx.ι a) (R/2)) : ‖Gt z‖ ≤ |t| *M := by
    change ‖(t : ℂ) • G z‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb z hz) (abs_nonneg t)
  have hLipt : ∀ z ∈ ball (Cx.ι a) R, ∀ w ∈ ball (Cx.ι a) R,
      ‖fderiv ℂ Gt z - fderiv ℂ Gt w‖ ≤ (|t| *Λ) * ‖z-w‖ := by
    intro z hz w hw
    rw [show fderiv ℂ Gt z = (t : ℂ) • fderiv ℂ G z from
      fderiv_const_smul (hd.differentiableAt (isOpen_ball.mem_nhds hz)) (t : ℂ),
      show fderiv ℂ Gt w = (t : ℂ) • fderiv ℂ G w from
      fderiv_const_smul (hd.differentiableAt (isOpen_ball.mem_nhds hw)) (t : ℂ),
      ← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hLip z hz w hw) (abs_nonneg t)
  have hsmall : (1 : ℝ≥0) * (‖t‖₊ * K) < 1 := by
    rw [one_mul]
    apply NNReal.coe_lt_coe.mp
    simpa only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one] using
      htK.trans (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨g, hg, hsol⟩ := local_holomorphic_solution hct (1 : ℝ≥0) (‖t‖₊*K)
    (by positivity : 0 ≤ R/2) (by linarith : R/2 < R) hdt
    (mul_nonneg (abs_nonneg t) hΛ) hLipt hbt
    (by norm_num; linarith : R/4 + (1 : ℝ)* (|t| *M) ≤ R/2)
    hKt hsmall
  have heq (y : H) (hy : y ∈ ball a (R/4)) :
      g (Cx.ι y) ⟨1, by constructor <;> norm_num⟩ = Cx.ι (flow S t y) := by
    let r : ℝ≥0 := ⟨R/2, by positivity⟩
    let δ : ℝ≥0 := ⟨R/4, by positivity⟩
    let Mt : ℝ≥0 := ⟨|t| *M, mul_nonneg (abs_nonneg t) hM⟩
    have hPL : IsPicardLindelof (fun _ z => t • S.Y z)
        (tmin := (-1 : ℝ)) (tmax := 2) ⟨0, by constructor <;> norm_num⟩ a r δ Mt (‖t‖₊*K) := by
      apply IsPicardLindelof.of_time_independent
      · intro z hz
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hYb z hz) (abs_nonneg t)
      · exact lipschitz_const_smul hYr t
      · change (|t| *M) * max (2-0) (0- -1) ≤ R/2 - R/4
        norm_num
        linarith
    obtain ⟨β, hβc, hβ0, hβm, _, hβd⟩ := QuantumNLS.Ext025A2.gp04_differential_existence hPL
      (show y ∈ closedBall a δ from ball_subset_closedBall hy)
    have hβflow := real_curve_eq_flow S t hβc hβ0 hβd
    have het (z : H) (hz : z ∈ closedBall a (R/2)) :
        Gt (Cx.ι z) = Cx.ι (t • S.Y z) := by
      dsimp [Gt]
      rw [he z hz, Cx.ι_smul]
      exact (ofReal_smul' t _).symm
    obtain ⟨v, hv, hfix, hvβ⟩ := embedded_real_fixedPoint S hct hβc hβ0 hβm het hβd
    have hyi : Cx.ι y ∈ ball (Cx.ι a) (R/4) := by
      simpa only [mem_ball, dist_eq_norm, ← ι_sub, Cx.norm_ι] using hy
    have hgs := hsol _ hyi
    have hfixg : picard Gt hct (1 : ℝ) (Cx.ι y,g (Cx.ι y)) = g (Cx.ι y) := by
      ext s
      exact (hgs.2 s).symm
    have hh := QuantumNLS.Ext025A4PicardStability.fixedPoint_initial_bound
      hct (1 : ℝ≥0) (‖t‖₊*K) hKt
      hsmall
      hgs.1 hv hfixg hfix
    have hgv : g (Cx.ι y) = v := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hh))
    rw [hgv, hvβ]
    congr 1
    simpa only [mul_one] using hβflow (x := 1) (by constructor <;> norm_num)
  let oneTime : Time := ⟨1, by constructor <;> norm_num⟩
  have hxi : Cx.ι x ∈ ball (Cx.ι a) (R/4) := by
    simpa only [mem_ball, dist_eq_norm, ← ι_sub, Cx.norm_ι] using hx
  have hax := ((ContinuousMap.evalCLM (R := ℂ) (M := Cx H) oneTime).analyticAt _).comp (hg _ hxi)
  have har : AnalyticAt ℝ (fun y : H => reL (g (Cx.ι y) oneTime)) x :=
    (reL.analyticAt _).comp (hax.restrictScalars.comp (ιL.analyticAt x))
  apply har.congr
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  change Cx.re (g (Cx.ι y) oneTime) = flow S t y
  rw [heq y hy]
  rfl

/-- The exact compact-local GP-04 proposition for the printed D01 source. -/
theorem compact_local_analyticity (S : Hyp H) :
    QuantumNLS.TerraMultiRound18AnalyticFlow.GP04CompactLocalAnalyticity S := by
  classical
  intro K hK
  choose ε hε τ hτ ha using local_analytic_flow S
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun a => ball a (ε a))
    (fun _ => isOpen_ball) (fun a _ => mem_iUnion.mpr ⟨a, mem_ball_self (hε a)⟩)
  by_cases hn : s.Nonempty
  · let d := s.inf' hn τ
    have hd : 0 < d := by
      dsimp [d]
      rw [Finset.lt_inf'_iff]
      exact fun a _ => hτ a
    refine ⟨d, hd, fun x hx t ht => ?_⟩
    obtain ⟨a, has, hxa⟩ := mem_iUnion₂.mp (hs hx)
    exact ha a x hxa t (ht.trans_le (Finset.inf'_le _ has))
  · refine ⟨1, zero_lt_one, fun x hx => ?_⟩
    obtain ⟨a, has, _⟩ := mem_iUnion₂.mp (hs hx)
    exact (hn ⟨a,has⟩).elim

end QuantumNLS.Ext025A4D01Analytic

#print axioms QuantumNLS.Ext025A4D01Analytic.real_curve_eq_flow
#print axioms QuantumNLS.Ext025A4D01Analytic.embedded_real_fixedPoint
#print axioms QuantumNLS.Ext025A4D01Analytic.local_analytic_flow
#print axioms QuantumNLS.Ext025A4D01Analytic.compact_local_analyticity

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4D01Analytic" then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
