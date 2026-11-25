import Mathlib
import QuantumNLS.ResetMoserProcedure
import QuantumNLS.Local021Equiv
import QuantumNLS.Local021Scale2

/-!
# LOCAL-021, stage 4b: scaling of the flow `S` and its inverse

`Sm_scale`: `S^A(s z) = s S^B(z)` and `Si_scale`: `(S^A)⁻¹(s w) = s (S^B)⁻¹(w)` (ODE uniqueness, `MoserData.flow_unique`), from `ScaleΩ PA PB s`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.Local021

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp

variable {PA PB : PrintedHyp}

theorem Yf_scale (BA : PrintedBounds PA) (BB : PrintedBounds PB) {s : ℝ} (hs : 0 < s) (h : ScaleΩ PA PB s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : K} (hz : ‖z‖ < (moserDataN PB.toHyp BB.toNative).R0)
    (hsz : s * ‖z‖ < (moserDataN PA.toHyp BA.toNative).R0) :
    (moserDataN PA.toHyp BA.toNative).Yf t (s • z) = s • (moserDataN PB.toHyp BB.toNative).Yf t z := by
  have hRB : (moserDataN PB.toHyp BB.toNative).R0 ≤ PB.R := (moserR0_le_R PB.toHyp BB.toNative).trans BB.ρR
  have hRA : (moserDataN PA.toHyp BA.toNative).R0 ≤ PA.R := (moserR0_le_R PA.toHyp BA.toNative).trans BA.ρR
  have hzB : z ∈ ball (0 : K) PB.R := by rw [mem_ball_zero_iff]; linarith
  have hszA : s • z ∈ ball (0 : K) PA.R := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hs]; linarith
  rw [← PA.moserY_eq_Yf BA t hszA, ← PB.moserY_eq_Yf BB t hzB]
  exact moserY_scale BA BB hs h ht hzB hszA

theorem Sm_scale (BA : PrintedBounds PA) (BB : PrintedBounds PB) {s : ℝ} (hs : 0 < s) (h : ScaleΩ PA PB s)
    {z : K} (hz : ‖z‖ < (moserDataN PB.toHyp BB.toNative).R0 / 4)
    (hsz : s * ‖z‖ < (moserDataN PA.toHyp BA.toNative).R0 / 4) :
    (moserDataN PA.toHyp BA.toNative).Sfl 1 (s • z) = s • (moserDataN PB.toHyp BB.toNative).Sfl 1 z := by
  set MA := moserDataN PA.toHyp BA.toNative with hMA
  set MB := moserDataN PB.toHyp BB.toNative with hMB
  have hpA := MA.R0_pos
  have hpB := MB.R0_pos
  have hder : ∀ t, HasDerivAt (fun x => s • MB.Sfl x z) (s • MB.Yf (sig t) (MB.Sfl t z)) t := fun t =>
    (MB.Sfl_deriv hz.le t).const_smul s
  have hszA : ‖s • z‖ < MA.R0 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]; exact hsz
  have := MA.flow_unique hszA (γ := fun x => s • MB.Sfl x z) (by simp [MB.Sfl_zero])
    (fun t _ => (hder t).continuousAt.continuousWithinAt)
    (fun t ht => by
      have h1 := (hder t).hasDerivWithinAt (s := Ici t)
      rw [sig_eq (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩] at h1
      rw [Yf_scale BA BB hs h ⟨ht.1, ht.2.le⟩ (by rw [MB.norm_Sfl]; linarith) (by rw [MB.norm_Sfl]; linarith)]
      exact h1)
    (fun t _ => by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hs, MB.norm_Sfl]; linarith) 1
    ⟨zero_le_one, le_rfl⟩
  exact this.symm

theorem Si_scale (BA : PrintedBounds PA) (BB : PrintedBounds PB) {s : ℝ} (hs : 0 < s) (h : ScaleΩ PA PB s)
    {w : K} (hw : ‖w‖ < (moserDataN PB.toHyp BB.toNative).R0 / 4)
    (hsw : s * ‖w‖ < (moserDataN PA.toHyp BA.toNative).R0 / 4) :
    (moserDataN PA.toHyp BA.toNative).Tinv (s • w) = s • (moserDataN PB.toHyp BB.toNative).Tinv w := by
  set MA := moserDataN PA.toHyp BA.toNative with hMA
  set MB := moserDataN PB.toHyp BB.toNative with hMB
  have h1 : ‖MB.Tinv w‖ < MB.R0 / 4 := by rwa [MB.norm_Tinv]
  have h2 : s * ‖MB.Tinv w‖ < MA.R0 / 4 := by rwa [MB.norm_Tinv]
  have h3 := Sm_scale BA BB hs h h1 h2
  have e : w = MB.Sfl 1 (MB.Tinv w) := (MB.Sfl_one_Tinv w).symm
  calc MA.Tinv (s • w) = MA.Tinv (s • MB.Sfl 1 (MB.Tinv w)) := by rw [← e]
    _ = MA.Tinv (MA.Sfl 1 (s • MB.Tinv w)) := by rw [h3]
    _ = s • MB.Tinv w := MA.Tinv_Sfl_one _

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.Sm_scale
#print axioms QuantumNLS.Local021.Si_scale
