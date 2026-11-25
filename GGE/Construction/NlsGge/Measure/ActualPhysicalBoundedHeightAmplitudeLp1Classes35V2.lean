import NlsGge.Measure.ActualPhysicalBoundedHeightAmplitudeLp1Prerequisite35V3
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- The actual 00-channel zero-extended amplitude as a full-real-line L¹
class, indexed by the closed physical endpoint/height rectangle. -/
def actualPhysicalHeightAmplitude00Lp1_35V2
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) : Lp (α := ℝ) ℂ 1 (volume : Measure ℝ) := by
  let h : MemLp (actualPhysicalHeightAmplitude00_35V3 u p.1 p.2) 1 volume :=
    actualPhysicalHeightAmplitude00_memLpOne35V3 u p.1.2.1 p.1.2.2
      hY₀ p.2.2.1 p.2.2.2
  exact MemLp.toLp (actualPhysicalHeightAmplitude00_35V3 u p.1 p.2) h

/-- The actual 11-channel zero-extended amplitude as a full-real-line L¹
class, with the original unstarred source representative. -/
def actualPhysicalHeightAmplitude11Lp1_35V2
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) : Lp (α := ℝ) ℂ 1 (volume : Measure ℝ) := by
  let h : MemLp (actualPhysicalHeightAmplitude11_35V3 u p.1 p.2) 1 volume :=
    actualPhysicalHeightAmplitude11_memLpOne35V3 u p.1.2.1 p.1.2.2
      hY₀ p.2.2.1 p.2.2.2
  exact MemLp.toLp (actualPhysicalHeightAmplitude11_35V3 u p.1 p.2) h

/-- The bundled 00 class has the actual zero-extended source amplitude as its
full-volume almost-everywhere representative. -/
theorem actualPhysicalHeightAmplitude00Lp1_35V2_coe_ae
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) :
    (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀ p : ℝ → ℂ) =ᵐ[volume]
      actualPhysicalHeightAmplitude00_35V3 u p.1 p.2 := by
  let h : MemLp (actualPhysicalHeightAmplitude00_35V3 u p.1 p.2) 1 volume :=
    actualPhysicalHeightAmplitude00_memLpOne35V3 u p.1.2.1 p.1.2.2
      hY₀ p.2.2.1 p.2.2.2
  change (MemLp.toLp (actualPhysicalHeightAmplitude00_35V3 u p.1 p.2) h : ℝ → ℂ) =ᵐ[volume]
    actualPhysicalHeightAmplitude00_35V3 u p.1 p.2
  exact MemLp.coeFn_toLp h

/-- The bundled 11 class has the actual zero-extended source amplitude as its
full-volume almost-everywhere representative. -/
theorem actualPhysicalHeightAmplitude11Lp1_35V2_coe_ae
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) :
    (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ p : ℝ → ℂ) =ᵐ[volume]
      actualPhysicalHeightAmplitude11_35V3 u p.1 p.2 := by
  let h : MemLp (actualPhysicalHeightAmplitude11_35V3 u p.1 p.2) 1 volume :=
    actualPhysicalHeightAmplitude11_memLpOne35V3 u p.1.2.1 p.1.2.2
      hY₀ p.2.2.1 p.2.2.2
  change (MemLp.toLp (actualPhysicalHeightAmplitude11_35V3 u p.1 p.2) h : ℝ → ℂ) =ᵐ[volume]
    actualPhysicalHeightAmplitude11_35V3 u p.1 p.2
  exact MemLp.coeFn_toLp h

end NlsGge.SpectralFoundations
end
