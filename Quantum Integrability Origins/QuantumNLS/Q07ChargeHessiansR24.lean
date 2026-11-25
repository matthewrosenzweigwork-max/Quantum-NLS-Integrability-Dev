import QuantumNLS.Q07ChargeBoundsR24
import QuantumNLS.Q07RealCalculusR24

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set Metric Filter Topology
namespace QuantumNLS.Q07ChargeHessiansR24
open RiccatiSobolevBanach Q07ChargeBoundsR24 Q07RealCalculusR24
variable {L S : ℝ} [Fact (0 < L)] {M : ℕ}

theorem charge_hessians (hS : 1+(M : ℝ) ≤ S) (hM : 1 ≤ M) (κ : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Ell2, ‖u‖ ≤ B+2 → ∀ v w : Ell2,
      |fderiv ℝ (fderiv ℝ (realCharge (L := L) hS κ n)) u v w| ≤ C*‖v‖*‖w‖ := by
  let ρ := |B|+8
  let K := majorant (L := L) S M κ ρ n
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hK : 0 ≤ K := majorant_nonneg hS κ hρ n
  refine ⟨36*K,by positivity,?_⟩
  intro u hu v w
  let p := slice u
  have hp : ‖p‖ ≤ B+2 := by simpa only [p,norm_slice] using hu
  have han : ∀ q, AnalyticAt ℂ (cxCharge (L := L) hS κ n) q := cxCharge_analytic hS hM κ n hn
  have hb : ∀ q ∈ ball p 2, ‖cxCharge (L := L) hS κ n q‖ ≤ K := by
    intro q hq
    apply cxCharge_bound hS κ hρ n hn q
    have ht := norm_le_norm_add_norm_sub' q p
    have hdist : ‖q-p‖ < 2 := by simpa only [mem_ball,dist_eq_norm] using hq
    dsimp [ρ]
    linarith [le_abs_self B]
  have hbound := GP05AcceptedBridgeR16.uniform_real_derivatives
    (I := Unit) (f := fun _ : Unit => cxCharge (L := L) hS κ n)
    (a := p) (R := 2) (C := K) (by norm_num) hK (fun _ => 1) (by simp)
    (fun _ q hq => (han q).differentiableAt.differentiableWithinAt)
    (fun _ q hq => by simpa using hb q hq) 2 () p (mem_ball_self (by norm_num))
  have hnorm : ‖fderiv ℝ (fderiv ℝ (cxCharge (L := L) hS κ n)) p‖ ≤ 36*K := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    norm_num at hbound
    exact hbound
  have hdiff : ∀ q, ContDiffAt ℝ 2 (cxCharge (L := L) hS κ n) q :=
    fun q => (han q).contDiffAt.restrict_scalars ℝ
  have he := linear_twice slice Complex.reCLM (U := univ) isOpen_univ (mem_univ _)
    (fun q _ => (hdiff q).differentiableAt (by norm_num))
    (((hdiff p).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  change |fderiv ℝ (fderiv ℝ (fun x => Complex.reCLM (cxCharge (L := L) hS κ n (slice x)))) u v w| ≤ _
  rw [he.2.2]
  refine (Complex.abs_re_le_norm _).trans ?_
  calc _ ≤ ‖fderiv ℝ (fderiv ℝ (cxCharge (L := L) hS κ n)) p (slice v)‖*‖slice w‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ (cxCharge (L := L) hS κ n)) p‖*‖slice v‖)*‖slice w‖ := by
      gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (36*K*‖v‖)*‖w‖ := by simp only [norm_slice]; gcongr
end QuantumNLS.Q07ChargeHessiansR24
