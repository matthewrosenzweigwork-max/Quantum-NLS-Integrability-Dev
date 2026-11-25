import Mathlib
import NlsGge.Atomic.G4.G4039Host
import NlsGge.Atomic.G4.G4039
import NlsGge.Atomic.G4.G4041
import NlsGge.ThirdConsultation.G1.G1098Reindex
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.GK38.Defs

                                                                                                    
                                                                           
                                                                                                                                        
                                                                                               
                                                                                                                                          
                                                                                                                                 
                                                              
                                                                           
                                                                                                                                                 
                                                                                                                                                  
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G4042Aux

/-- Coordinatewise real part `ℓ²(Bool × ℤ, ℂ) → ℓ²(Bool × ℤ, ℝ)` as a bounded `ℝ`-linear map. -/
def reCart : CartesianComplex →L[ℝ] CartesianReal :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun j => (x j).re,
        (lp.memℓp x).mono' (fun j => by simpa using Complex.abs_re_le_norm (x j))⟩
      map_add' := fun x y => lp.ext (funext fun j => by simp <;> rfl)
      map_smul' := fun c x => lp.ext (funext fun j => by simp) }
    1 (fun x => by
      simpa using lp.norm_mono (p := 2) (by norm_num)
        (x := (⟨fun j => (x j).re,
          (lp.memℓp x).mono' (fun j => by simpa using Complex.abs_re_le_norm (x j))⟩ : CartesianReal))
        (y := x) (fun j => by simpa using Complex.abs_re_le_norm (x j)))

theorem reCart_apply (x : CartesianComplex) (j : Bool × ℤ) : reCart x j = (x j).re := rfl

/-- On the source domain `birkhoffCartesian` has the Cartesian sequence as its coordinates. -/
theorem coord_of_mem (φ : PotPair) (hφ : φ ∈ sourceBetaW) (n : ℤ) :
    birkhoffCartesian φ (true, n) = cartesianX n φ ∧
    birkhoffCartesian φ (false, n) = cartesianY n φ := by
  obtain ⟨V, hVn, -, C, -, hV⟩ := G4039 φ hφ
  exact (hV φ (mem_of_mem_nhds hVn)).2.2 n

/-- Coordinates of `birkhoffCartesian` are analytic on `sourceBetaW` (G4-041 + G4-039). -/
theorem coords_analytic (j : Bool × ℤ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => birkhoffCartesian φ j) sourceBetaW := by
  obtain ⟨b, n⟩ := j
  cases b
  · exact (G4041 n).2.congr sourceFamily.V_open (fun φ hφ => (coord_of_mem φ hφ n).2.symm)
  · exact (G4041 n).1.congr sourceFamily.V_open (fun φ hφ => (coord_of_mem φ hφ n).1.symm)

/-- Local boundedness of `birkhoffCartesian` on `sourceBetaW` (G4-039). -/
theorem locally_bounded :
    ∀ φ₀ ∈ sourceBetaW, ∃ r > 0, ∃ C : ℝ, ∀ y ∈ Metric.ball φ₀ r, ‖birkhoffCartesian y‖ ≤ C := by
  intro φ₀ hφ₀
  obtain ⟨V, hVn, -, C, -, hV⟩ := G4039 φ₀ hφ₀
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hVn
  exact ⟨r, hr, C, fun y hy => (hV y (hrV hy)).2.1⟩

theorem complex_analytic : AnalyticOnNhd ℂ birkhoffCartesian sourceBetaW := by
  obtain ⟨σ⟩ : Nonempty ((Bool × ℤ) ≃ ℤ) := nonempty_equiv_of_countable
  exact NlsGge.Atomic.G1098Reindex.analyticOnNhd_of_coords_of_locBdd_reindex σ birkhoffCartesian
    sourceFamily.V_open coords_analytic locally_bounded

theorem real_eq_comp :
    realBirkhoffCartesian = fun u => reCart (birkhoffCartesian (realSlice u)) := by
  funext u
  have hmem : realSlice u ∈ sourceBetaW := sourceFamily.V_real (mem_range_self u)
  apply lp.ext
  funext j
  obtain ⟨b, n⟩ := j
  cases b
  · rw [realBirkhoffCartesian_false, reCart_apply, (coord_of_mem _ hmem n).2]
    rfl
  · rw [realBirkhoffCartesian_true, reCart_apply, (coord_of_mem _ hmem n).1]
    rfl

end G4042Aux

theorem G4042 :
  AnalyticOnNhd ℂ birkhoffCartesian sourceBetaW ∧
  (∀ u : PhysicalL2, Memℓp (realCartesianSequence u) 2) ∧
  AnalyticOnNhd ℝ realBirkhoffCartesian Set.univ := by
  refine ⟨G4042Aux.complex_analytic, fun u => realCartesianSequence_memℓp u, ?_⟩
  rw [G4042Aux.real_eq_comp]
  intro u _
  have hmem : realSlice u ∈ sourceBetaW := sourceFamily.V_real (mem_range_self u)
  have h1 : AnalyticAt ℝ birkhoffCartesian (realSlice u) :=
    (G4042Aux.complex_analytic (realSlice u) hmem).restrictScalars
  exact (G4042Aux.reCart.analyticAt _).comp (h1.comp (realSlice.analyticAt u))

end
end NlsGge.GKDefinitionDesign
