import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.RCLike.Sqrt
import NlsGge.GK38.ContourAction
import NlsGge.GK38.ActionPlaneReal
import Mathlib.Analysis.Analytic.Uniqueness
import NlsGge.GK38.TauGamma
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.GK38.EigenvalueCompactnessStrong
import NlsGge.GK38.RealTypeSpectrumConstant
import NlsGge.Hierarchy.ALPlaneConsistency38
import NlsGge.Spectral.ActualGapHeightHolderE02_38

set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.AblowitzLadik
open NlsGge.HierarchyRiccati.Core NlsGge.Analysis
namespace NlsGge.GK38
noncomputable section

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance


/-- A genuine period-one L2 plane wave opening the requested signed label. -/
def a5OpenWitness38 (n : ℤ) : PhysicalL2 :=
  planeL2 n.natAbs (planeWaveCoeff38 n.natAbs (-n) 1)

/-- Every signed label has an actual real-slice witness with symmetric gap square exactly four. -/
theorem a5OpenWitness_gamma2_38 (n : ℤ) :
    gamma2 (realSlice (a5OpenWitness38 n)) n = 4 := by
  have hguard : (-n).natAbs ≤ n.natAbs := by simp
  have hends := planeWaveOpenEndpoints38 n.natAbs (-n) hguard 1
  simp only [neg_neg, abs_one] at hends
  rw [(tauGamma_real38 (a5OpenWitness38 n) n).2]
  change (((actualGapUpperAllE02_38 (planeL2 n.natAbs (planeWaveCoeff38 n.natAbs (-n) 1)) n -
    actualGapLowerAllE02_38 (planeL2 n.natAbs (planeWaveCoeff38 n.natAbs (-n) 1)) n) ^ 2 : ℝ) : ℂ) = 4
  rw [hends.1, hends.2]
  push_cast
  ring

/-- The all-index actual open-gap witness, without an assumed extension or contour bridge. -/
theorem a5OpenGapNonempty38 :
    ∀ n : ℤ, ∃ u : PhysicalL2, gamma2 (realSlice u) n ≠ 0 := by
  intro n
  refine ⟨a5OpenWitness38 n, ?_⟩
  rw [a5OpenWitness_gamma2_38]
  norm_num

/-- A candidate normalized action extension on the full certified neighbourhood. -/
def XiSqSpec38 (n : ℤ) (g : PotPair → ℂ) : Prop :=
  AnalyticOnNhd ℂ g gkW ∧
    ∀ φ ∈ gkW, gamma2 φ n ≠ 0 → gamma2 φ n * g φ = 4 * gkActionC38 φ n

/-- An actual noncollapsed neighbourhood at every signed index. -/
theorem a5OpenWitness_ne_eventually38 (n : ℤ) :
    ∀ᶠ φ in 𝓝 (realSlice (a5OpenWitness38 n)), φ ∈ gkW ∧ gamma2 φ n ≠ 0 := by
  have hW := realSlice_mem_gkW (a5OpenWitness38 n)
  have hne : gamma2 (realSlice (a5OpenWitness38 n)) n ≠ 0 := by
    rw [a5OpenWitness_gamma2_38]
    norm_num
  have hWevt : ∀ᶠ φ in 𝓝 (realSlice (a5OpenWitness38 n)), φ ∈ gkW :=
    isOpen_gkW.mem_nhds hW
  exact hWevt.and ((gamma2_analytic n _ hW).continuousAt.eventually_ne hne)

/-- Candidate uniqueness is EqOn on W and does not assume or construct existence. -/
theorem xiSqCandidate_unique38 (n : ℤ) (g h : PotPair → ℂ)
    (hg : XiSqSpec38 n g) (hh : XiSqSpec38 n h) : Set.EqOn g h gkW := by
  apply hg.1.eqOn_of_preconnected_of_eventuallyEq hh.1 isPreconnected_gkW
    (realSlice_mem_gkW (a5OpenWitness38 n))
  filter_upwards [a5OpenWitness_ne_eventually38 n] with φ hφ
  apply mul_left_cancel₀ hφ.2
  exact (hg.2 φ hφ.1 hφ.2).trans (hh.2 φ hφ.1 hφ.2).symm

/-- A candidate's multiplied identity extends over every complex collapsed gap. -/
theorem xiSqCandidate_multiplied38 (n : ℤ) (g : PotPair → ℂ)
    (hg : XiSqSpec38 n g) :
    ∀ φ ∈ gkW, gamma2 φ n * g φ = 4 * gkActionC38 φ n := by
  apply ((gamma2_analytic n).mul hg.1).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const.mul (action_analytic38 n)) isPreconnected_gkW
    (realSlice_mem_gkW (a5OpenWitness38 n))
  filter_upwards [a5OpenWitness_ne_eventually38 n] with φ hφ
  exact hg.2 φ hφ.1 hφ.2

/-- The full unconditional existence target remains a separate, unproved proposition. -/
def XiSqExistence38 : Prop :=
  ∀ n : ℤ, ∃ g : PotPair → ℂ, XiSqSpec38 n g ∧
    ∀ g' : PotPair → ℂ, XiSqSpec38 n g' → Set.EqOn g g' gkW

def XiSqIdentity38 : Prop :=
  ∀ (n : ℤ) (g : PotPair → ℂ), XiSqSpec38 n g →
    ∀ φ ∈ gkW, gamma2 φ n * g φ = 4 * gkActionC38 φ n

def OpenGapNonempty38 : Prop :=
  ∀ n : ℤ, ∃ u : PhysicalL2, gamma2 (realSlice u) n ≠ 0

def XiSqNearOne38 : Prop :=
  ∀ g : ℤ → PotPair → ℂ, (∀ n : ℤ, XiSqSpec38 n (g n)) →
    ∀ φ₀ ∈ gkW, ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ N : ℕ, ∀ φ ∈ U, ∀ n : ℤ, N < n.natAbs →
        g n φ ∈ Complex.slitPlane ∧ ‖g n φ - 1‖ < (1 / 2 : ℝ)

def XiSqrtL2NearOne38 : Prop :=
  ∀ g : ℤ → PotPair → ℂ, (∀ n : ℤ, XiSqSpec38 n (g n)) →
    ∀ φ₀ ∈ gkW, IsLocUnifL2Seq (fun φ n => Complex.sqrt (g n φ) - 1) φ₀

def XiSqrtAnalytic38 : Prop :=
  ∀ (n : ℤ) (g : PotPair → ℂ), XiSqSpec38 n g →
    AnalyticOnNhd ℂ (fun φ => Complex.sqrt (g φ))
      {φ : PotPair | φ ∈ gkW ∧ g φ ∈ Complex.slitPlane}

def XiSqRealPositive38 : Prop :=
  ∀ g : ℤ → PotPair → ℂ, (∀ n : ℤ, XiSqSpec38 n (g n)) →
    ∀ (u : PhysicalL2) (n : ℤ),
      (g n (realSlice u)).im = 0 ∧ 0 < (g n (realSlice u)).re

def ActionXiIdentity38 : Prop :=
  ∀ (n : ℤ) (g : PotPair → ℂ), XiSqSpec38 n g →
    ∀ φ ∈ gkW,
      gkActionC38 φ n = Complex.sqrt (g φ) ^ 2 * gamma2 φ n / 4

/-- Principal-root analyticity is asserted only on its true slit-plane locus. -/
theorem xiSqrtCandidate_analytic38 : XiSqrtAnalytic38 := by
  intro n g hg
  change AnalyticOnNhd ℂ (fun φ => g φ ^ (2⁻¹ : ℂ)) _
  exact (hg.1.mono (fun _ hφ => hφ.1)).cpow analyticOnNhd_const (fun _ hφ => hφ.2)

/-- The square identity is algebraic even at zero, with no root analyticity assumption. -/
theorem actionXiCandidate_identity38 : ActionXiIdentity38 := by
  intro n g hg φ hφ
  have hsquare : Complex.sqrt (g φ) ^ 2 = g φ :=
    Complex.cpow_nat_inv_pow (g φ) (by decide : (2 : ℕ) ≠ 0)
  rw [hsquare]
  have hprod := xiSqCandidate_multiplied38 n g hg φ hφ
  linear_combination -(1 / 4 : ℂ) * hprod

/-- Full multiplied identity, including complex collapsed gaps, as the exact selected contract. -/
theorem a5XiSqIdentity38 : XiSqIdentity38 := xiSqCandidate_multiplied38

/-- Exact all-index nonemptiness contract. -/
theorem a5OpenGapNonemptyContract38 : OpenGapNonempty38 := a5OpenGapNonempty38

end
end NlsGge.GK38
