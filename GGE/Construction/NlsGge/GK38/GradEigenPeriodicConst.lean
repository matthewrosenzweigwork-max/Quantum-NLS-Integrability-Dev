import NlsGge.GK38.GradEigenStateL2
import NlsGge.GK38.PairPotentialProbe
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem constant_nilpotent_fundamental (a b z : ℂ) (hz : z^2=a*b) (t : Time) :
    fundPair (constL2 a,constL2 b) z t =
      1+(t : ℝ) • zsCoeffPair (fun _ => a) (fun _ => b) z 0 := by
  let N := zsCoeffPair (fun _ => a) (fun _ => b) z 0
  let D : ℝ → PairMat38 := fun s => 1+s • N
  have hNsq : N*N=0 := by
    change zsCoeffPair (fun _ => a) (fun _ => b) z 0 *
      zsCoeffPair (fun _ => a) (fun _ => b) z 0=0
    rw [zsCoeffPair_const_sq,hz,sub_self,zero_smul]
  have hND (s : ℝ) : N*D s=N := by simp [D,mul_add,hNsq]
  have hentry (i j : Fin 2) (s : ℝ) : HasDerivAt (fun r => D r i j) (N i j) s := by
    have h := ((hasDerivAt_id s).smul_const (N i j)).const_add ((1 : PairMat38) i j)
    simpa only [D,Matrix.add_apply,Matrix.smul_apply,one_smul,id_eq] using! h
  change fundPair (constL2 a,constL2 b) z t=D (t : ℝ)
  apply fundPair_eq_of_ac_ae_ode38 (constL2 a,constL2 b) z D
  · simp [D]
  · intro i j
    have h : ContDiff ℝ 1 (fun s : ℝ => D s i j) := by
      simp only [D,Matrix.add_apply,Matrix.smul_apply]
      fun_prop
    exact h.contDiffOn.absolutelyContinuousOnInterval
  · intro i j
    filter_upwards [zsCoeffPot38_const_ae a b z] with s hs _
    rw [hs]
    change HasDerivAt (fun r => D r i j) ((N*D s) i j) s
    rw [hND]
    exact hentry i j s

theorem constant_nilpotent_state (a b z : ℂ) (hz : z^2=a*b) (v : PairVec38)
    (hv : Matrix.mulVec (zsCoeffPair (fun _ => a) (fun _ => b) z 0) v=0) (t : Time) :
    state (constL2 a,constL2 b) z v t=v := by
  rw [state_eq_mulVec,constant_nilpotent_fundamental a b z hz,
    Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,hv,smul_zero,add_zero]

end
end NlsGge.GK38.GradEigen38
