import Armstrong.Work.RawBetaContinuousSheet
import Armstrong.Work.RawBetaSpectralInput
import Armstrong.Work.RawBetaArcAssemblyV3

/-! The actual raw-beta path, including its continuous square-root sheet.
The terminal normalization is the antidiscriminant convention of GK I.15.
-/

set_option autoImplicit false
open Set Filter Topology Metric

namespace NlsGge.GK38
noncomputable section

theorem rawBetaRootedPiecewisePathExists38 (φ : GKPotential38) (m : ℤ) :
    Nonempty (GKRootedPiecewisePath38 φ m) := by
  obtain ⟨γ, hγcont, hγC1, hstart, hend, hball, hslit⟩ :=
    rawBetaUnrootedCurveExists38 φ m
  have hper : Continuous (perChar φ.1) :=
    continuousOn_univ.mp (analyticOnNhd_perChar_z φ.1).continuousOn
  have hcont : ContinuousOn (fun t => perChar φ.1 (γ t)) (Icc (0 : ℝ) 1) :=
    hper.comp_continuousOn hγcont
  have hzero : perChar φ.1 (γ 0) = 0 := by
    rw [hstart]
    exact rawBetaPerCharLowerTipZero38 φ m
  have hnonzero : ∀ t ∈ Ioo (0 : ℝ) 1, perChar φ.1 (γ t) ≠ 0 := by
    intro t ht
    exact rawBetaPerCharNonzeroOnSlit38 φ m (γ t) (hslit t ht)
  have hterminal : antiDiscrim φ.1 (muSeq φ.1 m) ^ 2 = perChar φ.1 (γ 1) := by
    rw [hend]
    exact rawBetaDirichletTerminalSquare38 φ m
  obtain ⟨s, hscont, hsquare, hsone⟩ :=
    rawBetaContinuousSquareRootWithTerminal38 (fun t => perChar φ.1 (γ t))
      hcont hzero hnonzero (antiDiscrim φ.1 (muSeq φ.1 m)) hterminal
  exact rawBetaPiecewisePath38OfCurveLift φ m (isolating_family38 φ.1 φ.2)
    γ s hγcont hγC1 hscont hsquare hball hslit hstart hend (fun _ _ => hsone)

end
end NlsGge.GK38
