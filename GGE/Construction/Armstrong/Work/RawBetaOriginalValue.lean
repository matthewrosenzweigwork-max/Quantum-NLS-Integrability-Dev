import Armstrong.Work.RawBetaOverlap
import Armstrong.Work.RawBetaActualCoefficient
import Armstrong.Work.RawBetaPathPrimitive
import Mathlib.Analysis.Convex.PathConnected

/-! Transfer a coefficient on any certified filled disc to the actual
same-family all-path source predicate on the original disc.
The terminal comparison is applied on the convex overlap of the two genuine
discs, containing both the lower periodic tip and the Dirichlet terminal.
-/

set_option autoImplicit false
open Set Metric

namespace NlsGge.GK38
noncomputable section

/-- A coefficient on any supplied full isolating family realizes the original
all-admissible-path beta value, using the same numerator and zero period. -/
theorem rawBetaSourceValueOfFixedCoefficient38
    (n m : ℤ) (hmn : m ≠ n)
    (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (C : ℤ → ℂ) (ρ : ℤ → ℝ) (hfam : IsolatingFamily38 φ.1 C ρ)
    (hperiod : abelianPeriod38 m φ.1 (p6PsiNumerator38 n (F n) φ.1) = 0)
    (T : ℂ → ℂ) (hT : AnalyticOnNhd ℂ T (ball (C m) (ρ m)))
    (hTode : ∀ z ∈ ball (C m) (ρ m),
      perChar φ.1 z * deriv T z + (deriv (perChar φ.1) z / 2) * T z =
        p6PsiNumerator38 n (F n) φ.1 z) :
    GKSourceBetaValue38 n m hmn F φ
      (antiDiscrim φ.1 (muSeq φ.1 m) * T (muSeq φ.1 m)) := by
  obtain ⟨S, hS, hSode⟩ :=
    rawBetaPsiCoefficientOfZeroPeriod38 n m (F n) φ.1 φ.2 hperiod
  obtain ⟨c, N, hgeom, hspec⟩ := hfam
  obtain ⟨c₀, N₀, hgeom₀, hspec₀⟩ := isolating_family38 φ.1 φ.2
  have ha : lamMinus φ.1 m ∈ ball (C m) (ρ m) :=
    (hspec.1 m).1 (left_mem_segment ℝ _ _)
  have ha₀ : lamMinus φ.1 m ∈ ball (discC φ.1 m) (discR φ.1 m) :=
    (hspec₀.1 m).1 (left_mem_segment ℝ _ _)
  have hz : muSeq φ.1 m ∈ ball (C m) (ρ m) := (hspec.1 m).2.1
  have hz₀ : muSeq φ.1 m ∈ ball (discC φ.1 m) (discR φ.1 m) :=
    (hspec₀.1 m).2.1
  let U : Set ℂ := ball (C m) (ρ m) ∩ ball (discC φ.1 m) (discR φ.1 m)
  have hU : IsOpen U := isOpen_ball.inter isOpen_ball
  have hUc : IsPreconnected U :=
    ((convex_ball (C m) (ρ m)).inter
      (convex_ball (discC φ.1 m) (discR φ.1 m))).isPreconnected
  have hQ : DifferentiableOn ℂ (perChar φ.1) U :=
    (analyticOnNhd_perChar_z φ.1).differentiableOn.mono (subset_univ U)
  have he : antiDiscrim φ.1 (muSeq φ.1 m) * T (muSeq φ.1 m) =
      antiDiscrim φ.1 (muSeq φ.1 m) * S (muSeq φ.1 m) :=
    rawBetaTerminalEqualityOfSharedODE38 U hU hUc (perChar φ.1) T S
      (p6PsiNumerator38 n (F n) φ.1) hQ
      (hT.differentiableOn.mono inter_subset_left)
      (hS.differentiableOn.mono inter_subset_right)
      (fun z hzU => hTode z hzU.1) (fun z hzU => hSode z hzU.2)
      (lamMinus φ.1 m) (muSeq φ.1 m) (antiDiscrim φ.1 (muSeq φ.1 m))
      ⟨ha, ha₀⟩ ⟨hz, hz₀⟩ (rawBetaPerCharLowerTipZero38 φ m)
      (rawBetaDirichletTerminalSquare38 φ m)
  have hall := rawBetaAllPathsOfPrimitiveCoefficient38 n m F φ S hS
    (fun z hzSlit => hSode z hzSlit.1)
  obtain ⟨p⟩ := rawBetaRootedPiecewisePathExists38 φ m
  rw [he]
  exact ⟨p, hall p, hall⟩

end
end NlsGge.GK38
