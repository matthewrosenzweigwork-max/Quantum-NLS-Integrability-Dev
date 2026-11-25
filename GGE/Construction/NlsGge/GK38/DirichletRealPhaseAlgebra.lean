import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.DirichletRealPhaseInteger

/-! Actual Dirichlet boundary reality and the scalar clockwise half-turn index. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_root_iff_endpoint_real38 (u : PhysicalL2) (x : ℝ) :
    dirichletChar (realSlice u) (x : ℂ) = 0 ↔
      (dirichletState38 u (x : ℂ) ⟨1, zero_le_one, le_rfl⟩ 0).im = 0 := by
  let t : DirichletTime38 := ⟨1, zero_le_one, le_rfl⟩
  have hs := dirichletState_real_star38 u x t
  have hb : dirichletChar (realSlice u) (x : ℂ) = 0 ↔
      dirichletState38 u (x : ℂ) t 0 = dirichletState38 u (x : ℂ) t 1 := by
    have h := dirichletChar_zero_iff_boundary38 (realSlice u) (x : ℂ)
    rw [monodromyPair_eq_fundPair] at h
    exact h
  rw [hb]
  constructor
  · intro h
    have hi := congrArg Complex.im (hs.trans h.symm)
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  · intro h
    change (dirichletState38 u (x : ℂ) t 0).im = 0 at h
    have he : star (dirichletState38 u (x : ℂ) t 0) = dirichletState38 u (x : ℂ) t 0 := by
      apply Complex.ext
      · simp [Complex.star_def]
      · simp [Complex.star_def, h]
    exact he.symm.trans hs


end
end NlsGge.GK38
