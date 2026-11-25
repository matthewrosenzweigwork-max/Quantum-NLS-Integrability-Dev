import NlsGge.GK38.GradFundamentalKernelAlgebra
import NlsGge.GK38.GradFundamentalRemainder

/-! # K1: independent potential and spectral variation integrals.
GK Chapter I, Proposition3.1. Integrability is established before defining or
using the interval integrals.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

theorem continuous_fundAdj38 (φ : PotPair) (z : ℂ) :
    Continuous (fun s => (ext38 (fundContP φ z) s).adjugate) := by
  simp only [Matrix.adjugate_fin_two]
  have hm := continuous_ext38 (fundContP φ z)
  fun_prop

theorem intervalIntegrable_fundPotentialKer38 (φ : PotPair) (z : ℂ)
    (h : PotPair) (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    IntervalIntegrable (fun s => ((ext38 (fundContP φ z) s).adjugate *
      potCoeff38 h s * ext38 (fundContP φ z) s) i j) volume 0 (t : ℝ) :=
  intervalIntegrable_triple_entry_of_mem h (continuous_fundAdj38 φ z)
    (continuous_ext38 _) t.2 i j

theorem intervalIntegrable_fundSpectralKer38 (φ : PotPair) (z : ℂ)
    (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    IntervalIntegrable (fun s => ((ext38 (fundContP φ z) s).adjugate *
      spectralCoeff38 * ext38 (fundContP φ z) s) i j) volume 0 (t : ℝ) := by
  have hc : Continuous (fun s => ((ext38 (fundContP φ z) s).adjugate *
      spectralCoeff38 * ext38 (fundContP φ z) s) i j) := by
    have ha := continuous_fundAdj38 φ z
    have hm := continuous_ext38 (fundContP φ z)
    fun_prop
  exact hc.intervalIntegrable _ _

def fundPotentialIntegral38 (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) (h : PotPair) : PairMat38 :=
  fundPair φ z t * Matrix.of (fun i j => ∫ s in (0 : ℝ)..(t : ℝ),
    ((ext38 (fundContP φ z) s).adjugate * potCoeff38 h s * ext38 (fundContP φ z) s) i j)

def fundSpectralIntegral38 (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) : PairMat38 :=
  fundPair φ z t * Matrix.of (fun i j => ∫ s in (0 : ℝ)..(t : ℝ),
    ((ext38 (fundContP φ z) s).adjugate * spectralCoeff38 * ext38 (fundContP φ z) s) i j)

end
end NlsGge.GK38
