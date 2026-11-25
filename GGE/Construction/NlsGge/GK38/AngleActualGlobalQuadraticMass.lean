import NlsGge.GK38.AngleGlobalLocalQuadraticMass
import NlsGge.GK38.AbelianActualCommonComplexInverseNeighborhood

/-! Actual global normalized omitted roots have locally uniform quadratic
quotient square mass on ONE common complex neighborhood of the ENTIRE real
L2 slice, before ALL signed n. Global branches come from actual real-trace
and inverse-continuation gluing; the local mass is transferred on explicit
common balls. No global-root or uniformity oracle is a premise. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem angleActual_global_normalized_locally_uniform_quadratic_quotients38 :
    ∃ W : Set PotPair, IsOpen W ∧ range realSlice ⊆ W ∧ W ⊆ gkW ∧
      ∃ F : (n : ℤ) → PotPair → P2Space38 n,
        (∀ n : ℤ, AnalyticOnNhd ℂ (F n) W) ∧
        (∀ n : ℤ, ∀ φ ∈ W, p2Fn38 n (φ,F n φ)=0 ∧
          (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ,y)) (F n φ)).IsInvertible) ∧
        (∀ n : ℤ, ∀ u : PhysicalL2, ∃ t : P3RealSpace38 n,
          t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 ∧
          F n (realSlice u)=p3RealInclude38 n t) ∧
        ∀ φ ∈ W, ∃ r B : ℝ, 0 < r ∧ 0 < B ∧ ball φ r ⊆ W ∧
          ∀ ψ ∈ ball φ r, ∀ n : ℤ, ∃ A : P2Space38 n,
            (∀ m : P2Index38 n,
              A m=(countingCenter38 m.1+F n ψ m-tauN ψ m.1)/gamma2 ψ m.1) ∧
            Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
            (∑' m : P2Index38 n,‖A m‖^2) ≤ B ∧
            ∀ m : P2Index38 n,
              countingCenter38 m.1+F n ψ m=tauN ψ m.1+gamma2 ψ m.1*A m := by
  classical
  obtain ⟨W,hW,hreal,hWW,hbranches⟩ := p6Actual_common_complex_normalized_inverse_neighborhood38
  choose F hFa hFspec hFreal using hbranches
  have hlocal (u : PhysicalL2) : ∃ ρ B : ℝ, 0 < ρ ∧ 0 < B ∧
      ball (realSlice u) ρ ⊆ W ∧ ∀ n : ℤ, ∀ φ ∈ ball (realSlice u) ρ,
        ∃ A : P2Space38 n,
          (∀ m : P2Index38 n,
            A m=(countingCenter38 m.1+F n φ m-tauN φ m.1)/gamma2 φ m.1) ∧
          Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
          (∑' m : P2Index38 n,‖A m‖^2) ≤ B ∧
          ∀ m : P2Index38 n,
            countingCenter38 m.1+F n φ m=tauN φ m.1+gamma2 φ m.1*A m := by
    obtain ⟨C,R,hfam⟩ := exists_isolating_family38 (realSlice u) (realSlice_mem_gkW u)
    exact angleGlobal_normalized_local_quadratic_quotient_lp38 W hW hWW F hFa hFspec hFreal
      u (hreal ⟨u,rfl⟩) C R hfam
  choose ρ B hρ hB hρW hmass using hlocal
  let V : Set PotPair := ⋃ u : PhysicalL2, ball (realSlice u) (ρ u)
  have hV : IsOpen V := isOpen_iUnion (fun _ => isOpen_ball)
  have hVW : V ⊆ W := by
    intro φ hφ
    obtain ⟨u,hu⟩ := mem_iUnion.mp hφ
    exact hρW u hu
  have hRV : range realSlice ⊆ V := by
    rintro φ ⟨u,rfl⟩
    exact mem_iUnion.mpr ⟨u,mem_ball_self (hρ u)⟩
  refine ⟨V,hV,hRV,hVW.trans hWW,F,
    fun n => (hFa n).mono hVW,
    fun n φ hφ => hFspec n φ (hVW hφ),hFreal,?_⟩
  intro φ hφ
  obtain ⟨u,hu⟩ := mem_iUnion.mp hφ
  obtain ⟨r,hr,hrball⟩ := Metric.exists_ball_subset_ball hu
  have hrV : ball φ r ⊆ V := fun ψ hψ => mem_iUnion.mpr ⟨u,hrball hψ⟩
  exact ⟨r,B u,hr,hB u,hrV,fun ψ hψ n => hmass u n ψ (hrball hψ)⟩

end
end NlsGge.GK38
