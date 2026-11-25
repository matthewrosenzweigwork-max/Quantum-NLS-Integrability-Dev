import QuantumNLS.Ext025A4SourcePaths
import QuantumNLS.Ext025A2ODE
import QuantumNLS.Ext025A4D01Analytic
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Topology Filter
open scoped NNReal
namespace QuantumNLS.Ext025A4LocalComparison
open QuantumNLS.Ext025A4BanachComplexification
open QuantumNLS.Ext025A4AnalyticIntegral
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Uniqueness along an interior local solution needs Lipschitz control
only near that solution. The other curve need not be assumed to remain
in the chart. Continuity and local uniqueness propagate equality. -/
theorem curve_eq {f : V → V} {a : V} {r : ℝ} {K : ℝ≥0}
    (hK : LipschitzOnWith K f (closedBall a r))
    {β γ : ℝ → V} (hβ : Continuous β) (hγ : Continuous γ)
    (hβd : ∀ t ∈ Ioo (-1 : ℝ) 2, HasDerivAt β (f (β t)) t)
    (hγd : ∀ t, HasDerivAt γ (f (γ t)) t)
    (hβm : ∀ t ∈ Ioo (-1 : ℝ) 2, β t ∈ ball a r)
    (h0 : β 0 = γ 0) : EqOn β γ (Ioo (-1 : ℝ) 2) := by
  let J := Ioo (-1 : ℝ) 2
  let A : Set J := {t | β t = γ t}
  have hc : IsClosed A := isClosed_eq (hβ.comp continuous_subtype_val) (hγ.comp continuous_subtype_val)
  have ho : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hbm := hβm t t.2
    have hgm : γ t ∈ ball a r := by rw [← ht]; exact hbm
    have he : β =ᶠ[𝓝 (t : ℝ)] γ := by
      apply ODE_solution_unique_of_eventually (v := fun _ => f) (s := fun _ => closedBall a r)
        (Filter.Eventually.of_forall (fun _ => hK))
      · filter_upwards [isOpen_Ioo.mem_nhds t.2, hβ.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hbm)] with s hs hm
        exact ⟨hβd s hs, ball_subset_closedBall hm⟩
      · filter_upwards [hγ.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hgm)] with s hs
        exact ⟨hγd s, ball_subset_closedBall hs⟩
      · exact ht
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds he
  have : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp (convex_Ioo (-1 : ℝ) 2).isPreconnected
  have he : A = univ := (show IsClopen A from ⟨hc,ho⟩).eq_univ ⟨⟨0, by constructor <;> norm_num⟩, h0⟩
  intro t ht
  exact (show (⟨t,ht⟩ : J) ∈ A from he.symm ▸ mem_univ _)

/-- Bounded real Picard solutions embed as literal complex fixed points. -/
theorem embedded_fixedPoint {f : V → V} {G : Cx V → Cx V} (hG : Continuous G)
    {a x : V} {r d : ℝ} {β : ℝ → V}
    (hc : Continuous β) (h0 : β 0 = x)
    (hm : ∀ s, β s ∈ closedBall a r)
    (he : ∀ z ∈ closedBall a r, G (Cx.ι z) = Cx.ι (f z))
    (hd : ∀ s ∈ Icc (-1 : ℝ) 2,
      HasDerivWithinAt β (d • f (β s)) (Icc (-1 : ℝ) 2) s) :
    ∃ v : Path (Cx V), v ∈ closedBall (ContinuousMap.const Time (Cx.ι a)) r ∧
      picard G hG d (Cx.ι x,v) = v ∧ ∀ s : Time, v s = Cx.ι (β s) := by
  let v : Path (Cx V) := ⟨fun s => Cx.ι (β s), (Cx.ιL.continuous.comp hc).comp continuous_subtype_val⟩
  have hv : v ∈ closedBall (ContinuousMap.const Time (Cx.ι a)) r := by
    rw [mem_closedBall, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (le_trans dist_nonneg (hm 0))).mpr
    intro s
    change ‖Cx.ι (β s) - Cx.ι a‖ ≤ r
    simpa only [← Cx.ι_sub, Cx.norm_ι, ← dist_eq_norm] using (show dist (β s) a ≤ r from hm s)
  refine ⟨v, hv, ?_, fun _ => rfl⟩
  apply ContinuousMap.ext
  intro s
  let α : ℝ → Cx V := fun s => Cx.ι (β s)
  have hα : Continuous α := Cx.ιL.continuous.comp hc
  have hαd (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : HasDerivAt α (d • G (α z)) z := by
    have hh := (hd z ⟨by linarith [hz.1], by linarith [hz.2]⟩).hasDerivAt
      (Icc_mem_nhds (by linarith [hz.1]) (by linarith [hz.2]))
    rw [he _ (hm z)]
    simpa only [α, Function.comp_def, map_smul, Cx.ιL_apply] using
      (Cx.ιL : V →L[ℝ] Cx V).hasFDerivAt.comp_hasDerivAt z hh
  have hint : d • (∫ z in (0 : ℝ)..(s : ℝ), G (α z)) = α s - α 0 := by
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z hz => hαd z ((uIcc_subset_Icc (by constructor <;> norm_num) s.2) hz))
      (((hG.comp hα).const_smul d).intervalIntegrable _ _)
  have hext (z : ℝ) (hz : z ∈ uIcc (0 : ℝ) (s : ℝ)) :
      extend (QuantumNLS.Ext025A4AnalyticPath.superposition G hG v) z = G (α z) := by
    have hz' := (uIcc_subset_Icc (by constructor <;> norm_num) s.2) hz
    change G (Cx.ι (β (projIcc 0 1 zero_le_one z))) = G (Cx.ι (β z))
    rw [projIcc_of_mem _ hz']
  change Cx.ι x + (d : ℂ) • (∫ z in (0 : ℝ)..(s : ℝ), _) = Cx.ι (β s)
  rw [intervalIntegral.integral_congr hext, Cx.ofReal_smul, hint]
  dsimp [α]
  rw [h0]
  abel

/-- A short holomorphic step, with uniform amplification, agrees with any
actual real solution starting in its initial ball. Chart membership of
that actual solution is a consequence of uniqueness, not an input. -/
theorem local_step {f : V → V} {G : Cx V → Cx V} (hc : Continuous G)
    {a : V} {R M Λ : ℝ} (d K : ℝ≥0) (hR : 0 < R) (hM : 0 ≤ M)
    (hd : DifferentiableOn ℂ G (ball (Cx.ι a) R)) (hΛ : 0 ≤ Λ)
    (hLip : ∀ x ∈ ball (Cx.ι a) R, ∀ y ∈ ball (Cx.ι a) R,
      ‖fderiv ℂ G x - fderiv ℂ G y‖ ≤ Λ * ‖x-y‖)
    (hb : ∀ z ∈ closedBall (Cx.ι a) (R/2), ‖G z‖ ≤ M)
    (hK : LipschitzOnWith K G (closedBall (Cx.ι a) (R/2)))
    (he : ∀ x ∈ closedBall a (R/2), G (Cx.ι x) = Cx.ι (f x))
    (hsize : (d : ℝ)*M ≤ R/16) (hsmall : d*K < 1) :
    ∃ step : Cx V → Cx V,
      AnalyticOnNhd ℂ step (ball (Cx.ι a) (R/8)) ∧
      (∀ x ∈ ball (Cx.ι a) (R/8), ∀ y ∈ ball (Cx.ι a) (R/8),
        dist (step x) (step y) ≤ (1-(d : ℝ)*(K : ℝ))⁻¹ * dist x y) ∧
      ∀ x ∈ ball a (R/8), ∀ γ : ℝ → V,
        (∀ t, HasDerivAt γ ((d : ℝ) • f (γ t)) t) → γ 0 = x →
        step (Cx.ι x) = Cx.ι (γ 1) := by
  obtain ⟨q,hq,hs,hst⟩ := QuantumNLS.Ext025A4PicardStability.local_holomorphic_lipschitz_solution
    hc d K (by positivity : 0 ≤ R/2) (by linarith : R/2 < R) hd hΛ hLip hb
    (by linarith : R/8+(d : ℝ)*M ≤ R/2) hK hsmall
  let oneTime : Time := ⟨1,by constructor <;> norm_num⟩
  let step := fun z => q z oneTime
  have hKr : LipschitzOnWith K f (closedBall a (R/2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxi : Cx.ι x ∈ closedBall (Cx.ι a) (R/2) := by
      simpa only [mem_closedBall,dist_eq_norm,← Cx.ι_sub,Cx.norm_ι] using hx
    have hyi : Cx.ι y ∈ closedBall (Cx.ι a) (R/2) := by
      simpa only [mem_closedBall,dist_eq_norm,← Cx.ι_sub,Cx.norm_ι] using hy
    have hh := hK.dist_le_mul _ hxi _ hyi
    rw [he x hx,he y hy] at hh
    simpa only [dist_eq_norm,← Cx.ι_sub,Cx.norm_ι] using hh
  have hbr (x : V) (hx : x ∈ closedBall a (R/2)) : ‖f x‖ ≤ M := by
    have hxi : Cx.ι x ∈ closedBall (Cx.ι a) (R/2) := by
      simpa only [mem_closedBall,dist_eq_norm,← Cx.ι_sub,Cx.norm_ι] using hx
    simpa only [he x hx,Cx.norm_ι] using hb _ hxi
  refine ⟨step,fun z hz => ((ContinuousMap.evalCLM (R := ℂ) (M := Cx V) oneTime).analyticAt _).comp (hq z hz),?_,?_⟩
  · intro x hx y hy
    simpa only [step,dist_eq_norm,ContinuousMap.sub_apply] using
      ((q x-q y).norm_coe_le_norm oneTime).trans (hst x hx y hy)
  · intro x hx γ hγd hγ0
    let r : ℝ≥0 := ⟨R/4,by positivity⟩
    have hrr : (r : ℝ) ≤ R/2 := by change R/4 ≤ R/2; linarith
    have hrrlt : (r : ℝ) < R/2 := by change R/4 < R/2; linarith
    let δ : ℝ≥0 := ⟨R/8,by positivity⟩
    let m : ℝ≥0 := ⟨(d : ℝ)*M,mul_nonneg d.coe_nonneg hM⟩
    have hPL : IsPicardLindelof (fun _ z => (d : ℝ) • f z)
        (tmin := (-1 : ℝ)) (tmax := 2) ⟨0,by constructor <;> norm_num⟩ a r δ m (‖(d : ℝ)‖₊*K) := by
      apply IsPicardLindelof.of_time_independent
      · intro z hz
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg d.coe_nonneg]
        exact mul_le_mul_of_nonneg_left (hbr z (closedBall_subset_closedBall hrr hz)) d.coe_nonneg
      · exact QuantumNLS.Ext025A4D01Analytic.lipschitz_const_smul
          (hKr.mono (closedBall_subset_closedBall hrr)) (d : ℝ)
      · change ((d : ℝ)*M)*max (2-0) (0- -1) ≤ R/4-R/8
        norm_num
        linarith
    obtain ⟨β,hβ,hβ0,hβm,_,hβd⟩ := QuantumNLS.Ext025A2.gp04_differential_existence hPL (ball_subset_closedBall hx)
    have hβγ := curve_eq (QuantumNLS.Ext025A4D01Analytic.lipschitz_const_smul hKr (d : ℝ))
      hβ (continuous_iff_continuousAt.mpr (fun t => (hγd t).continuousAt))
      (fun t ht => (hβd t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      hγd (fun t _ => closedBall_subset_ball hrrlt (hβm t)) (hβ0.trans hγ0.symm)
    obtain ⟨v,hv,hfix,hvβ⟩ := embedded_fixedPoint hc hβ hβ0 hβm
      (fun z hz => he z (closedBall_subset_closedBall hrr hz)) hβd
    have hxi : Cx.ι x ∈ ball (Cx.ι a) (R/8) := by
      simpa only [mem_ball,dist_eq_norm,← Cx.ι_sub,Cx.norm_ι] using hx
    have hfixq : picard G hc d (Cx.ι x,q (Cx.ι x)) = q (Cx.ι x) := by
      apply ContinuousMap.ext
      intro t
      exact ((hs _ hxi).2 t).symm
    have hdist := QuantumNLS.Ext025A4PicardStability.fixedPoint_initial_bound hc d K hK hsmall
      (hs _ hxi).1 (closedBall_subset_closedBall hrr hv) hfixq hfix
    have hqv : q (Cx.ι x) = v := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hdist))
    change q (Cx.ι x) oneTime = _
    rw [hqv,hvβ]
    congr 1
    exact hβγ (by constructor <;> norm_num : (1 : ℝ) ∈ Ioo (-1 : ℝ) 2)
end QuantumNLS.Ext025A4LocalComparison

#print axioms QuantumNLS.Ext025A4LocalComparison.curve_eq
#print axioms QuantumNLS.Ext025A4LocalComparison.embedded_fixedPoint
#print axioms QuantumNLS.Ext025A4LocalComparison.local_step
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4LocalComparison" then
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
