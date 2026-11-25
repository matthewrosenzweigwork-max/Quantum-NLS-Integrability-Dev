import Mathlib
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST031
import NlsGge.Atomic.KST.KST035
import NlsGge.Atomic.KST.KST037
import NlsGge.Atomic.KST.KST038
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host

                                                                                                        
                                                                                                    
                                                                                                         
                                                                                                                 
                                                                                                                 
                                                                                                                      
                                                                                                                    
                                                                   
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST002

namespace NlsGge.ThirdConsultation.KST

theorem kst041_isClosed_componentBall (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (R : ℝ) :
    IsClosed (componentBall ω R) := by
  have : componentBall ω R = ⋂ ch : Bool, {x : Weighted ω | ‖x ch‖ ≤ R} := by
    ext x; simp [componentBall]
  rw [this]
  refine isClosed_iInter fun ch => isClosed_le ?_ continuous_const
  exact continuous_norm.comp (PiLp.continuous_apply 2 _ ch)

theorem kst041_convex_componentBall (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (R : ℝ) :
    Convex ℝ (componentBall ω R) := by
  intro x hx y hy a b ha hb hab ch
  calc ‖(a • x + b • y) ch‖ = ‖a • x ch + b • y ch‖ := by simp
    _ ≤ ‖a • x ch‖ + ‖b • y ch‖ := norm_add_le _ _
    _ = a * ‖x ch‖ + b * ‖y ch‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * R + b * R := by
        gcongr
        · exact hx ch
        · exact hy ch
    _ = R := by rw [← add_mul, hab, one_mul]

theorem kst041_norm_le_of_componentBall (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (R : ℝ) (x : Weighted ω)
    (hx : x ∈ componentBall ω R) : ‖x‖ ≤ 2 * R := by
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (hx true)
  have h := PiLp.norm_sq_eq_of_L2 _ x
  rw [Fintype.sum_bool] at h
  have h1 := hx true
  have h2 := hx false
  have h3 : ‖x true‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (x true)]
  have h4 : ‖x false‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (x false)]
  have h5 : ‖x‖ ^ 2 ≤ (2 * R) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' h5 (by linarith) |>.2

theorem kst041 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (v : ℤ → ℝ) (hv : SecondaryWeight v) :
  let ω := productWeight w v
  let hω := productOneLe hw.one_le hv.1.1
  letI := weightFact ω hω
  let F := adaptedFourier ω hω (adaptedThreshold w M)
  IsComplete (componentBall ω M) ∧
  componentBall ω (M/2) ⊆ F '' componentBall ω M ∧
  ∀ y ∈ componentBall ω (M/2),
    Set.MapsTo (fun x => y-(F x-x)) (componentBall ω M) (componentBall ω M) ∧
    (∀ x ∈ componentBall ω M, ∀ z ∈ componentBall ω M,
      ‖(y-(F x-x))-(y-(F z-z))‖ ≤ (1/8 : ℝ)*‖x-z‖) ∧
    ∃! x : Weighted ω, x ∈ componentBall ω M ∧ F x = y := by
  intro ω hω
  letI := weightFact ω hω
  intro F
  have hM0 : 0 < M := by linarith
  have h37 := kst037 w Cw M hM hw hunbounded v hv
  have h38 : F 0 = 0 ∧ Set.InjOn F (componentBall ω M) ∧ _ ∧ _ :=
    kst038 w Cw M hM hw hunbounded v hv
  obtain ⟨hF0, hinj, -, -⟩ := h38
  have hconv := kst041_convex_componentBall ω M
  have hdiffF : ∀ z ∈ componentBall ω M, DifferentiableAt ℂ F z := fun z hz =>
    (h37 z hz).1.differentiableAt
  have hbound : ∀ z ∈ componentBall ω M,
      ‖fderiv ℂ F z - ContinuousLinearMap.id ℂ (Weighted ω)‖ ≤ (1/8 : ℝ) :=
    fun z hz => (h37 z hz).2
  have hLip : ∀ x ∈ componentBall ω M, ∀ y ∈ componentBall ω M,
      ‖F x - F y - (x - y)‖ ≤ (1/8 : ℝ) * ‖x - y‖ := by
    intro x hx y hy
    have := hconv.norm_image_sub_le_of_norm_fderiv_le' (f := F)
      (φ := ContinuousLinearMap.id ℂ (Weighted ω)) (C := (1/8 : ℝ)) hdiffF hbound hy hx
    simpa using this
  have h0mem : (0 : Weighted ω) ∈ componentBall ω M := fun ch => by simpa using hM0.le
  have hcomplete : IsComplete (componentBall ω M) :=
    (kst041_isClosed_componentBall ω M).isComplete
  -- the displacement `F x - x` is small on the ball
  have hdisp : ∀ x ∈ componentBall ω M, ‖F x - x‖ ≤ M / 4 := by
    intro x hx
    have h1 := hLip x hx 0 h0mem
    rw [hF0, sub_zero, sub_zero] at h1
    have h2 := kst041_norm_le_of_componentBall ω M x hx
    linarith
  have hmaps : ∀ y ∈ componentBall ω (M/2),
      Set.MapsTo (fun x => y-(F x-x)) (componentBall ω M) (componentBall ω M) := by
    intro y hy x hx ch
    have h1 : ‖(y - (F x - x)) ch‖ ≤ ‖y ch‖ + ‖F x - x‖ := by
      calc ‖(y - (F x - x)) ch‖ = ‖y ch - (F x - x) ch‖ := by simp
        _ ≤ ‖y ch‖ + ‖(F x - x) ch‖ := norm_sub_le _ _
        _ ≤ ‖y ch‖ + ‖F x - x‖ := by gcongr; exact PiLp.norm_apply_le _ ch
    have h2 := hy ch
    have h3 := hdisp x hx
    linarith
  have hcontr : ∀ y ∈ componentBall ω (M/2), ∀ x ∈ componentBall ω M, ∀ z ∈ componentBall ω M,
      ‖(y-(F x-x))-(y-(F z-z))‖ ≤ (1/8 : ℝ)*‖x-z‖ := by
    intro y _ x hx z hz
    have e : (y-(F x-x))-(y-(F z-z)) = -(F x - F z - (x - z)) := by abel
    rw [e, norm_neg]
    exact hLip x hx z hz
  have hexists : ∀ y ∈ componentBall ω (M/2), ∃ x, x ∈ componentBall ω M ∧ F x = y := by
    intro y hy
    haveI : CompleteSpace (componentBall ω M) := hcomplete.completeSpace_coe
    haveI : Nonempty (componentBall ω M) := ⟨⟨0, h0mem⟩⟩
    let T : componentBall ω M → componentBall ω M := (hmaps y hy).restrict _ _ _
    have hT : ContractingWith (1/8 : NNReal) T := by
      refine ⟨by rw [show (1/8 : NNReal) = 8⁻¹ by norm_num]; norm_num, ?_⟩
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have h := hcontr y hy a a.2 b b.2
      have e : dist (T a) (T b) = ‖(y-(F a-a))-(y-(F b-b))‖ := by
        rw [Subtype.dist_eq, dist_eq_norm]; rfl
      have e2 : dist a b = ‖(a : Weighted ω) - b‖ := by rw [Subtype.dist_eq, dist_eq_norm]
      have e3 : (((1/8 : NNReal) : ℝ)) = 1/8 := by norm_num
      rw [e, e2, e3]
      exact h
    obtain ⟨p, hp, -⟩ := hT.exists_fixedPoint ⟨0, h0mem⟩ (edist_ne_top _ _)
    refine ⟨(p : Weighted ω), p.2, ?_⟩
    have := congrArg Subtype.val hp
    set x : Weighted ω := (p : Weighted ω)
    have e : F x = y := by
      have h' : y - (F x - x) = x := this
      have h2 : y = x + (F x - x) := sub_eq_iff_eq_add.mp h'
      rw [add_sub_cancel] at h2
      exact h2.symm
    exact e
  refine ⟨hcomplete, ?_, fun y hy => ⟨hmaps y hy, hcontr y hy, ?_⟩⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hexists y hy
    exact ⟨x, hx, hxy⟩
  · obtain ⟨x, hx, hxy⟩ := hexists y hy
    exact ⟨x, ⟨hx, hxy⟩, fun x' ⟨hx', hx'y⟩ => hinj hx' hx (hx'y.trans hxy.symm)⟩

end NlsGge.ThirdConsultation.KST
end
