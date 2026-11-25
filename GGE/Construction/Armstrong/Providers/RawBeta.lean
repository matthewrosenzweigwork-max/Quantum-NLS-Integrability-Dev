import NlsGge.GK38.AbelianPsiTheorem141
import NlsGge.GK38.AbelianPeriods
import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.IsolatingDefs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Armstrong.Work.RawBetaActualCoefficient
import Armstrong.Work.RawBetaPathPrimitive

set_option autoImplicit false
open NlsGge NlsGge.GK38 Set Filter Topology Metric MeasureTheory intervalIntegral
namespace Armstrong.Providers.RawBeta
noncomputable section

theorem gkBetaSourceWellDefined38
    (W : Set PotPair := by assumption)
    (hWopen : IsOpen W := by assumption)
    (hreal : range realSlice ⊆ W := by assumption)
    (hWgk : W ⊆ gkW := by assumption)
    (F : (n : ℤ) → PotPair → P2Space38 n := by assumption)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W := by assumption)
    (hFn : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W →
      p2Fn38 n (φ, F n φ) = 0 := by assumption)
    (hperiod : ∀ n : ℤ, ∀ φ : PotPair, φ ∈ W → ∀ m : ℤ,
      abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) =
        if m = n then 2 * (Real.pi : ℂ) else 0 := by assumption) :
    ∀ n : ℤ, ∀ φ : PotPair, ∀ hφ : φ ∈ W,
      ∀ m : ℤ, ∀ hmn : m ≠ n,
        (∃! β : ℂ,
          GKSourceBetaValue38 n m hmn F ⟨φ, hWgk hφ⟩ β) ∧
        (∀ β : ℂ,
          GKSourceBetaValue38 n m hmn F ⟨φ, hWgk hφ⟩ β →
          (muSeq φ m = lamMinus φ m ∨ muSeq φ m = lamPlus φ m) → β = 0) := by
  intro n φ hφ m hmn
  have hzero : abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) = 0 := by
    simpa only [if_neg hmn] using hperiod n φ hφ m
  obtain ⟨R, hR, hODE⟩ :=
    rawBetaPsiCoefficientOfZeroPeriod38 n m (F n) φ (hWgk hφ) hzero
  refine ⟨rawBetaUniqueSourceValueOfPrimitiveCoefficient38
    n m hmn F ⟨φ, hWgk hφ⟩ R hR (fun z hz => hODE z hz.1), ?_⟩
  intro β hβ htip
  exact rawBetaSourceValueEqZeroAtTip38
    n m hmn F ⟨φ, hWgk hφ⟩ β hβ htip

end
end Armstrong.Providers.RawBeta

set_option pp.all true in
#check @Armstrong.Providers.RawBeta.gkBetaSourceWellDefined38
#print Armstrong.Providers.RawBeta.gkBetaSourceWellDefined38
#print axioms Armstrong.Providers.RawBeta.gkBetaSourceWellDefined38
