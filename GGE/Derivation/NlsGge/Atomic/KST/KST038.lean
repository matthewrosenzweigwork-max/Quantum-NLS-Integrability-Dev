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
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host

/- KST-038 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST038.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-038"
   (identical in gpt6pro_followup1..10; no Pro round 5-12 entry touches KST-038).  No repair of the head.
   Route (source Proposition 5.1/(67)): F 0 = 0 because the free potential has vanishing adapted coefficients
   (b, c vanish since potentialParameter n 0 = 0, low Fourier coefficients of 0 vanish; KST-035 coefficient identity
   weightedCoeffs (F x) = adaptedCoefficients (wp x) at x = 0).  The componentwise M ball is convex; by KST-037
   F - id is differentiable on it with ||d(F - id)|| <= 1/8, so the mean-value inequality
   `Convex.norm_image_sub_le_of_norm_fderiv_le` gives ||(Fx - x) - (Fy - y)|| <= (1/8)||x - y||, from which injectivity
   and the 7/8, 9/8, 8/7 bounds follow by the triangle inequality; y = 0 gives the (1/2, 2) bounds. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST002

namespace NlsGge.ThirdConsultation.KST

section ZeroCoefficients

open NlsGge.Atomic.KST016 NlsGge.Pilot

theorem kst038_adaptedCoefficients_zero (N : ℕ) :
    adaptedCoefficients N (0 : Potential) = 0 := by
  funext channel m
  have hb : ∀ (n : ℤ) (z : ℂ), b (0 : Potential) n z = 0 := by
    intro n z
    have hp : potentialParameter n (0 : Potential) = 0 := map_zero _
    simp [b, abc, localABC, localCorrection, hp]
  have hc : ∀ (n : ℤ) (z : ℂ), c (0 : Potential) n z = 0 := by
    intro n z
    have hp : potentialParameter n (0 : Potential) = 0 := map_zero _
    simp [c, abc, localABC, localCorrection, hp]
  have hf : rawFourier (0 : Potential) channel m = 0 := by
    unfold rawFourier
    show physicalFourier ((0 : PhysicalL2) : PhysicalCircle → ℂ) m = 0
    rw [← physicalFourierL2_apply]
    simp
  unfold adaptedCoefficients
  split_ifs
  · exact hf
  · exact hc _ _
  · exact hb _ _

end ZeroCoefficients

theorem kst038 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (v : ℤ → ℝ) (hv : SecondaryWeight v) :
  let ω := productWeight w v
  let hω := productOneLe hw.one_le hv.1.1
  letI := weightFact ω hω
  let F := adaptedFourier ω hω (adaptedThreshold w M)
  F 0 = 0 ∧ Set.InjOn F (componentBall ω M) ∧
  (∀ x ∈ componentBall ω M, ∀ y ∈ componentBall ω M,
    (7/8 : ℝ)*‖x-y‖ ≤ ‖F x-F y‖ ∧ ‖F x-F y‖ ≤ (9/8 : ℝ)*‖x-y‖ ∧
    ‖x-y‖ ≤ (8/7 : ℝ)*‖F x-F y‖) ∧
  (∀ x ∈ componentBall ω M, (1/2 : ℝ)*‖x‖ ≤ ‖F x‖ ∧ ‖F x‖ ≤ 2*‖x‖) := by
  intro ω hω
  letI := weightFact ω hω
  intro F
  have hM0 : 0 < M := by linarith
  have h37 := kst037 w Cw M hM hw hunbounded v hv
  obtain ⟨-, -, hmain⟩ := kst035 w Cw M hM hw hunbounded
  -- the origin lies in the ball
  have h0mem : (0 : Weighted ω) ∈ componentBall ω M := fun ch => by simpa using hM0.le
  have h0mem2 : (0 : Weighted ω) ∈ componentBall ω (2*M) := fun ch => by simpa using (by linarith : (0:ℝ) ≤ 2*M)
  -- F 0 = 0
  have hF0 : F 0 = 0 := by
    have hco := (hmain v hv 0 h0mem2).1
    have hwp : weightedPotential ω hω (0 : Weighted ω) = 0 := by
      rw [← KST033S.wpCLM_apply ω hω]
      exact map_zero _
    rw [hwp, kst038_adaptedCoefficients_zero] at hco
    have hy : ∀ ch m, (F 0) ch m = 0 := fun ch m => congrFun (congrFun hco ch) m
    have hnorm : ∀ ch, ‖(F 0) ch‖ = 0 := by
      intro ch
      have h2 := NlsGge.Pilot.weightedHilbert_hasSum (fun k => periodOneWeight ω k ^ 2) ((F 0) ch)
      have h3 : (fun m : ℤ => periodOneWeight ω m ^ 2 * ‖((F 0) ch : ℤ → ℂ) m‖ ^ 2) = fun _ => 0 := by
        funext m
        have := hy ch m
        simp [this]
      rw [h3] at h2
      have h4 := h2.unique hasSum_zero
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h4
    apply PiLp.ext
    intro ch
    exact norm_eq_zero.1 (hnorm ch)
  -- convexity of the componentwise ball
  have hconv : Convex ℝ (componentBall ω M) := by
    intro x hx y hy a b ha hb hab ch
    calc ‖(a • x + b • y) ch‖ = ‖a • x ch + b • y ch‖ := by simp
      _ ≤ ‖a • x ch‖ + ‖b • y ch‖ := norm_add_le _ _
      _ = a * ‖x ch‖ + b * ‖y ch‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * M + b * M := by
          gcongr
          · exact hx ch
          · exact hy ch
      _ = M := by rw [← add_mul, hab, one_mul]
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
  have hpair : ∀ x ∈ componentBall ω M, ∀ y ∈ componentBall ω M,
      (7/8 : ℝ)*‖x-y‖ ≤ ‖F x-F y‖ ∧ ‖F x-F y‖ ≤ (9/8 : ℝ)*‖x-y‖ ∧
      ‖x-y‖ ≤ (8/7 : ℝ)*‖F x-F y‖ := by
    intro x hx y hy
    have hl := hLip x hx y hy
    have e1 : F x - F y = (x - y) + (F x - F y - (x - y)) := by abel
    have e2 : x - y = (F x - F y) - (F x - F y - (x - y)) := by abel
    have u1 := norm_add_le (x - y) (F x - F y - (x - y))
    have u2 := norm_sub_le (F x - F y) (F x - F y - (x - y))
    rw [← e1] at u1
    rw [← e2] at u2
    refine ⟨by linarith, by linarith, by linarith⟩
  refine ⟨hF0, ?_, hpair, ?_⟩
  · intro x hx y hy hxy
    have h1 := (hpair x hx y hy).1
    rw [hxy, sub_self, norm_zero] at h1
    have : ‖x - y‖ = 0 := by
      have := norm_nonneg (x - y)
      linarith
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · intro x hx
    have h1 := hpair x hx 0 h0mem
    rw [hF0, sub_zero, sub_zero] at h1
    have h2 := norm_nonneg x
    refine ⟨by linarith [h1.1], by linarith [h1.2.1]⟩

end NlsGge.ThirdConsultation.KST
end
