import Armstrong.Frozen.RawBeta.GKRootedPiecewisePath38
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

theorem rawBetaPiecewisePath38OfCurveLift
    (φ : GKPotential38) (m : ℤ)
    (hIso : IsolatingFamily38 φ.1 (discC φ.1) (discR φ.1))
    (γ s : ℝ → ℂ)
    (hγcont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγC1 : ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1))
    (hscont : ContinuousOn s (Icc (0 : ℝ) 1))
    (hsquare : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      s t ^ 2 = perChar φ.1 (γ t))
    (hball : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      γ t ∈ ball (discC φ.1 m) (discR φ.1 m))
    (hslit : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      γ t ∈ GKOriginalSlit38 φ m)
    (hstart : γ 0 = lamMinus φ.1 m)
    (hend : γ 1 = muSeq φ.1 m)
    (hterminal : muSeq φ.1 m ≠ lamMinus φ.1 m →
      muSeq φ.1 m ≠ lamPlus φ.1 m →
      s 1 = antiDiscrim φ.1 (muSeq φ.1 m)) :
    Nonempty (GKRootedPiecewisePath38 φ m) := by
  let firstCurve : ℝ → ℂ := fun t => γ (t / 2)
  let firstSheet : ℝ → ℂ := fun t => s (t / 2)
  let lastCurve : ℝ → ℂ := fun t => γ ((t + 1) / 2)
  let lastSheet : ℝ → ℂ := fun t => s ((t + 1) / 2)
  have hhalfMap : MapsTo (fun t : ℝ => t / 2) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    constructor <;> dsimp <;> nlinarith
  have hhalfOpenMap : MapsTo (fun t : ℝ => t / 2) (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1) := by
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    constructor <;> dsimp <;> nlinarith
  have hshiftMap : MapsTo (fun t : ℝ => (t + 1) / 2) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    constructor <;> dsimp <;> nlinarith
  have hshiftOpenMap : MapsTo (fun t : ℝ => (t + 1) / 2) (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1) := by
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    constructor <;> dsimp <;> nlinarith
  have hhalfCont : ContinuousOn (fun t : ℝ => t / 2) (Icc (0 : ℝ) 1) := by
    simpa using (continuousOn_id.div_const (2 : ℝ))
  have hshiftCont : ContinuousOn (fun t : ℝ => (t + 1) / 2) (Icc (0 : ℝ) 1) := by
    have hsum : ContinuousOn (fun t : ℝ => t + 1) (Icc (0 : ℝ) 1) := by
      exact (continuous_add_const (1 : ℝ)).continuousOn
    exact hsum.div_const (2 : ℝ)
  have hhalfC1 : ContDiffOn ℝ 1 (fun t : ℝ => t / 2) (Icc (0 : ℝ) 1) := by
    simpa using (contDiff_id.div_const (2 : ℝ)).contDiffOn
  have hshiftC1 : ContDiffOn ℝ 1 (fun t : ℝ => (t + 1) / 2) (Icc (0 : ℝ) 1) := by
    have hconst : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)) := contDiff_const
    have hsum : ContDiff ℝ 1 (fun t : ℝ => t + 1) := by
      simpa using contDiff_id.add hconst
    exact (hsum.div_const (2 : ℝ)).contDiffOn
  have hfirstCurveCont : ContinuousOn firstCurve (Icc (0 : ℝ) 1) := by
    simpa [firstCurve] using hγcont.comp' hhalfCont hhalfMap
  have hfirstCurveC1 : ContDiffOn ℝ 1 firstCurve (Icc (0 : ℝ) 1) := by
    simpa [firstCurve, Function.comp_def] using hγC1.comp hhalfC1 hhalfMap
  have hfirstSheetCont : ContinuousOn firstSheet (Icc (0 : ℝ) 1) := by
    simpa [firstSheet] using hscont.comp' hhalfCont hhalfMap
  have hlastCurveCont : ContinuousOn lastCurve (Icc (0 : ℝ) 1) := by
    simpa [lastCurve] using hγcont.comp' hshiftCont hshiftMap
  have hlastCurveC1 : ContDiffOn ℝ 1 lastCurve (Icc (0 : ℝ) 1) := by
    simpa [lastCurve, Function.comp_def] using hγC1.comp hshiftC1 hshiftMap
  have hlastSheetCont : ContinuousOn lastSheet (Icc (0 : ℝ) 1) := by
    simpa [lastSheet] using hscont.comp' hshiftCont hshiftMap
  let firstArc : GKRootedC1Arc38 φ m := by
    refine ⟨(firstCurve, firstSheet), ?_⟩
    refine ⟨?_, ?_⟩
    · exact hfirstCurveCont
    refine ⟨?_, ?_⟩
    · exact hfirstCurveC1
    refine ⟨?_, ?_⟩
    · exact hfirstSheetCont
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hsquare (t / 2) (hhalfMap ht)
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hball (t / 2) (hhalfMap ht)
    intro t ht
    exact hslit (t / 2) (hhalfOpenMap ht)
  let lastArc : GKRootedC1Arc38 φ m := by
    refine ⟨(lastCurve, lastSheet), ?_⟩
    refine ⟨?_, ?_⟩
    · exact hlastCurveCont
    refine ⟨?_, ?_⟩
    · exact hlastCurveC1
    refine ⟨?_, ?_⟩
    · exact hlastSheetCont
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hsquare ((t + 1) / 2) (hshiftMap ht)
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hball ((t + 1) / 2) (hshiftMap ht)
    intro t ht
    exact hslit ((t + 1) / 2) (hshiftOpenMap ht)
  have hmid : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hmidSlit : γ (1 / 2) ∈ GKOriginalSlit38 φ m := hslit (1 / 2) hmid
  have hsplit : ((0 : ℝ) + 1) / 2 = (1 : ℝ) / 2 := by norm_num
  have hzeroHalf : (0 : ℝ) / 2 = 0 := by norm_num
  have honeHalf : ((1 : ℝ) + 1) / 2 = 1 := by norm_num
  have hjoin : GKRootedArcJoin38 φ m firstArc lastArc := by
    refine ⟨?_, ?_, ?_⟩
    · simp [GKArcCurve38, firstArc, lastArc, firstCurve, lastCurve, hsplit]
    · simp [GKArcSheet38, firstArc, lastArc, firstSheet, lastSheet, hsplit]
    · simpa [GKArcCurve38, firstArc, firstCurve] using hmidSlit
  have hchain : GKRootedArcChain38 φ m [firstArc, lastArc] := by
    simp [GKRootedArcChain38, hjoin]
  refine ⟨⟨(firstArc, ([], lastArc)), ?_⟩⟩
  refine ⟨hIso, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa using hchain
  refine ⟨?_, ?_⟩
  · simpa [GKArcCurve38, firstArc, firstCurve, hzeroHalf] using hstart
  refine ⟨?_, ?_⟩
  · simpa [GKArcCurve38, lastArc, lastCurve, honeHalf] using hend
  intro hμminus hμplus
  simpa [GKArcSheet38, lastArc, lastSheet, honeHalf] using hterminal hμminus hμplus

end
end NlsGge.GK38

#check @NlsGge.GK38.rawBetaPiecewisePath38OfCurveLift
#print axioms NlsGge.GK38.rawBetaPiecewisePath38OfCurveLift
