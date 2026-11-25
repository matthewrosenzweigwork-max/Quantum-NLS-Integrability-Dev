import Mathlib
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST019
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST031
import NlsGge.Atomic.KST.KST032
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST031Support
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.Atomic.G4.G4011

/- KST033Support PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST033Support.lean.
   SUPPORTING module (no packet increment).  Analytic half of KST-033 (Lemma 5.1(ii)): (1) x |-> weightedPotential is a
   bounded complex-linear map of norm <= 1 (coefficients are preserved, weights >= 1); (2) ball transfer to
   physicalComponentBall; (3) restriction compatibility; (4) joint analyticity of (z, phi) |-> a phi n z at points with
   unit 1 - q (KST016 localABC + KST018 isUnit_free_of_strips, as in KST029Support.abc_analyticOnNhd); (5) Picard
   iterates z_0 = nπ, z_{k+1} = nπ + a(z_k): analytic in x on the open ball, uniformly 1/23-geometrically convergent to
   diagonalZero (KST-032), hence the limit is analytic (G4-011 locally uniform limits). -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal

namespace NlsGge.ThirdConsultation.KST.KST033S

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST004 NlsGge.Atomic.KST006 NlsGge.Pilot

theorem physical_ext {f g : PhysicalL2} (h : ∀ m, physicalFourier f m = physicalFourier g m) :
    f = g := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext m
  rw [physicalFourierL2_apply, physicalFourierL2_apply]
  exact h m

theorem physicalFourier_add (f g : PhysicalL2) (m : ℤ) :
    physicalFourier (f + g : PhysicalL2) m = physicalFourier f m + physicalFourier g m := by
  rw [← physicalFourierL2_apply, ← physicalFourierL2_apply, ← physicalFourierL2_apply, map_add]
  first | done | rfl | simp

theorem physicalFourier_smul (c : ℂ) (f : PhysicalL2) (m : ℤ) :
    physicalFourier (c • f : PhysicalL2) m = c * physicalFourier f m := by
  rw [← physicalFourierL2_apply, ← physicalFourierL2_apply, map_smul]
  first | done | rfl | simp

section Wp

variable (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]

theorem wp_fourier (x : Weighted ω) (b : Bool) (m : ℤ) :
    physicalFourier (weightedPotential ω hω x b) m = (x b : ℤ → ℂ) m :=
  weightedPairPhysical_fourier (periodOneWeight ω) (fun m => hω (2*m)) x b m

theorem wp_add (x y : Weighted ω) :
    weightedPotential ω hω (x + y) = weightedPotential ω hω x + weightedPotential ω hω y := by
  apply PiLp.ext
  intro b
  apply physical_ext
  intro m
  rw [PiLp.add_apply, physicalFourier_add, wp_fourier ω hω, wp_fourier ω hω, wp_fourier ω hω]
  first | done | rfl | simp

theorem wp_smul (c : ℂ) (x : Weighted ω) :
    weightedPotential ω hω (c • x) = c • weightedPotential ω hω x := by
  apply PiLp.ext
  intro b
  apply physical_ext
  intro m
  rw [PiLp.smul_apply, physicalFourier_smul, wp_fourier ω hω, wp_fourier ω hω]
  first | done | rfl | simp

theorem wp_comp_sq_le (x : Weighted ω) (b : Bool) :
    ‖weightedPotential ω hω x b‖ ^ 2 ≤ ‖x b‖ ^ 2 := by
  have h1 := hasSum_physicalFourier_sq (weightedPotential ω hω x b)
  have h2 : HasSum (fun m : ℤ => periodOneWeight ω m ^ 2 * ‖(x b : ℤ → ℂ) m‖ ^ 2) (‖x b‖ ^ 2) :=
    weightedHilbert_hasSum (fun k => periodOneWeight ω k ^ 2) (x b)
  refine hasSum_le (fun m => ?_) h1 h2
  show ‖physicalFourier (weightedPotential ω hω x b) m‖ ^ 2 ≤
    periodOneWeight ω m ^ 2 * ‖(x b : ℤ → ℂ) m‖ ^ 2
  rw [wp_fourier ω hω]
  have h3 : 1 ≤ periodOneWeight ω m ^ 2 := by
    have h4 := hω (2*m)
    have e : periodOneWeight ω m = ω (2*m) := rfl
    rw [e]
    nlinarith
  calc ‖(x b : ℤ → ℂ) m‖ ^ 2 = 1 * ‖(x b : ℤ → ℂ) m‖ ^ 2 := by ring
    _ ≤ periodOneWeight ω m ^ 2 * ‖(x b : ℤ → ℂ) m‖ ^ 2 := by gcongr

theorem wp_norm_le (x : Weighted ω) : ‖weightedPotential ω hω x‖ ≤ ‖x‖ := by
  have h : ‖weightedPotential ω hω x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_bool, Fintype.sum_bool]
    exact add_le_add (wp_comp_sq_le ω hω x true) (wp_comp_sq_le ω hω x false)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- `x ↦ weightedPotential ω hω x` as a bounded complex-linear map. -/
def wpCLM : Weighted ω →L[ℂ] PhysicalPairLp :=
  LinearMap.mkContinuous
    { toFun := weightedPotential ω hω
      map_add' := wp_add ω hω
      map_smul' := fun c x => wp_smul ω hω c x }
    1 (fun x => by rw [one_mul]; exact wp_norm_le ω hω x)

theorem wpCLM_apply (x : Weighted ω) : wpCLM ω hω x = weightedPotential ω hω x := rfl

theorem wp_analyticAt (x : Weighted ω) : AnalyticAt ℂ (weightedPotential ω hω) x := by
  have e : (⇑(wpCLM ω hω)) = weightedPotential ω hω := funext (wpCLM_apply ω hω)
  rw [← e]
  exact (wpCLM ω hω).analyticAt x

theorem isOpen_componentOpenBall (R : ℝ) : IsOpen (componentOpenBall ω R) := by
  have h : componentOpenBall ω R = ⋂ ch : Bool, {x : Weighted ω | ‖x ch‖ < R} := by
    ext x
    simp [componentOpenBall]
  rw [h]
  exact isOpen_iInter_of_finite fun ch => isOpen_lt (by fun_prop) continuous_const

theorem componentOpenBall_subset (R : ℝ) : componentOpenBall ω R ⊆ componentBall ω R :=
  fun _ hx ch => (hx ch).le

theorem wp_mem_ball (x : Weighted ω) (R : ℝ) (hx : x ∈ componentBall ω R) :
    weightedPotential ω hω x ∈ physicalComponentBall ω R := by
  intro ch
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (hx ch)
  have h2 : HasSum (fun m : ℤ => ω (2*m) ^ 2 * ‖(x ch : ℤ → ℂ) m‖ ^ 2) (‖x ch‖ ^ 2) :=
    weightedHilbert_hasSum (fun k => periodOneWeight ω k ^ 2) (x ch)
  have hnn : ∀ m : ℤ, 0 ≤ ω (2*m) ^ 2 * ‖(x ch : ℤ → ℂ) m‖ ^ 2 := fun m => by positivity
  calc (∑' m : ℤ, ENNReal.ofReal
        (ω (2*m) ^ 2 * ‖physicalFourier (weightedPotential ω hω x ch) m‖ ^ 2))
      = ∑' m : ℤ, ENNReal.ofReal (ω (2*m) ^ 2 * ‖(x ch : ℤ → ℂ) m‖ ^ 2) := by
        refine tsum_congr fun m => ?_
        rw [wp_fourier ω hω]
    _ = ENNReal.ofReal (∑' m : ℤ, ω (2*m) ^ 2 * ‖(x ch : ℤ → ℂ) m‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn h2.summable).symm
    _ = ENNReal.ofReal (‖x ch‖ ^ 2) := by rw [h2.tsum_eq]
    _ ≤ ENNReal.ofReal (R ^ 2) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (x ch), hx ch])

end Wp

theorem wp_restriction (ω ν : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k) (hν : ∀ k, 1 ≤ ν k)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] [Fact (∀ m : ℤ, 0 < periodOneWeight ν m ^ 2)]
    (hων : ∀ k, ν k ^ 2 ≤ ω k ^ 2) (x : Weighted ω) :
    weightedPotential ν hν (weightedRestriction ω ν hων x) = weightedPotential ω hω x := by
  apply PiLp.ext
  intro b
  apply physical_ext
  intro m
  rw [wp_fourier ν hν, wp_fourier ω hω]
  first | done | rfl | simp [weightedRestriction, weightedComparison_apply]

/-! ### Joint analyticity of the reduced diagonal coefficient -/

theorem mem_domain (n : ℤ) (φ : PhysicalPairLp) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hu : IsUnit (1 - qOperator φ n z hz)) :
    (z, φ) ∈ NlsGge.Atomic.KST016.localInverseDomain n (center n) (center_mem_strip n) := by
  have hfree : IsUnit (NlsGge.Atomic.KST016.localFreeFactor n (center n)
      (center_mem_strip n) (z, φ)) :=
    isUnit_free_of_strips n (center n) z (center_mem_strip n) hz
  refine ⟨hfree, ?_⟩
  rw [NlsGge.Atomic.KST016.qOperator_local_resolvent_identity φ n (center n) z
    (center_mem_strip n) hz hfree]
  exact hu

theorem a_analyticAt (n : ℤ) (φ : PhysicalPairLp) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hu : IsUnit (1 - qOperator φ n z hz)) :
    AnalyticAt ℂ (fun p : ℂ × PhysicalPairLp => a p.2 n p.1) (z, φ) := by
  have hA := NlsGge.Atomic.KST016.localABC_analyticOnNhd n (center n) (center_mem_strip n)
    (z, φ) (mem_domain n φ z hz hu)
  exact ((ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)).analyticAt _).comp hA

/-! ### Picard iterates -/

def iter (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (n : ℤ) : ℕ → Weighted ω → ℂ
  | 0 => fun _ => center n
  | k + 1 => fun x => center n + a (weightedPotential ω hω x) n (iter ω hω n k x)

theorem iter_succ (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (n : ℤ) (k : ℕ) (x : Weighted ω) :
    iter ω hω n (k + 1) x = center n + a (weightedPotential ω hω x) n (iter ω hω n k x) := rfl

section Iter

variable (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M) (hw : UnboundedWeight w) (n : ℤ)
  (hn : diagonalThreshold w M ≤ n.natAbs) (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
  [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
  (hball : ∀ x ∈ componentBall ω (2*M), weightedPotential ω hω x ∈ physicalComponentBall w (2*M))

include hM hw hn hball

theorem iter_mem (k : ℕ) (x : Weighted ω) (hx : x ∈ componentBall ω (2*M)) :
    iter ω hω n k x ∈ Metric.closedBall (center n) (Real.pi / 48) := by
  induction k with
  | zero => exact Metric.mem_closedBall_self (by positivity)
  | succ k ih =>
    rw [iter_succ]
    exact (kst032 w M hM hw _ (hball x hx) n hn).1 ih

theorem iter_dist (k : ℕ) (x : Weighted ω) (hx : x ∈ componentBall ω (2*M)) :
    ‖iter ω hω n k x - diagonalZero n (weightedPotential ω hω x)‖ ≤
      Real.pi / 48 * (1 / 23 : ℝ) ^ k := by
  obtain ⟨-, hlip, hmem, hfix, -⟩ := kst032 w M hM hw _ (hball x hx) n hn
  set φ := weightedPotential ω hω x with hφ
  set σ := diagonalZero n φ with hσ
  induction k with
  | zero =>
    have h1 : ‖σ - center n‖ ≤ Real.pi / 48 := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.1 hmem
    have e : iter ω hω n 0 x - σ = -(σ - center n) := by
      show center n - σ = -(σ - center n)
      ring
    rw [e, norm_neg]
    simpa using h1
  | succ k ih =>
    have hik := iter_mem w M hM hw n hn ω hω hball k x hx
    have h1 := hlip (iter ω hω n k x) hik σ hmem
    have e : iter ω hω n (k + 1) x - σ =
        (center n + a φ n (iter ω hω n k x)) - (center n + a φ n σ) := by
      rw [iter_succ]
      conv_lhs => rw [hfix]
    rw [e]
    calc _ ≤ (1 / 23 : ℝ) * ‖iter ω hω n k x - σ‖ := h1
      _ ≤ (1 / 23 : ℝ) * (Real.pi / 48 * (1 / 23 : ℝ) ^ k) := by gcongr
      _ = Real.pi / 48 * (1 / 23 : ℝ) ^ (k + 1) := by ring

theorem iter_analyticAt (k : ℕ) (x : Weighted ω) (hx : x ∈ componentBall ω (2*M)) :
    AnalyticAt ℂ (iter ω hω n k) x := by
  induction k with
  | zero => exact analyticAt_const
  | succ k ih =>
    have hz := iter_mem w M hM hw n hn ω hω hball k x hx
    have hzs : iter ω hω n k x ∈ spectralStrip n :=
      closedBall_subset_strip n
        (Metric.closedBall_subset_closedBall (by linarith [Real.pi_pos]) hz)
    obtain ⟨-, hall⟩ := (kst031 w M hM hw).2.1
    have hu : IsUnit (1 - qOperator (weightedPotential ω hω x) n (iter ω hω n k x) hzs) :=
      ((hall _ (hball x hx) n hn).2.1 _ hzs).2
    have hG := a_analyticAt n (weightedPotential ω hω x) (iter ω hω n k x) hzs hu
    have hpair : AnalyticAt ℂ
        (fun y : Weighted ω => (iter ω hω n k y, weightedPotential ω hω y)) x :=
      ih.prod (wp_analyticAt ω hω x)
    have hcomp : AnalyticAt ℂ
        ((fun p : ℂ × PhysicalPairLp => a p.2 n p.1) ∘
          (fun y : Weighted ω => (iter ω hω n k y, weightedPotential ω hω y))) x :=
      AnalyticAt.comp (g := fun p : ℂ × PhysicalPairLp => a p.2 n p.1)
        (f := fun y : Weighted ω => (iter ω hω n k y, weightedPotential ω hω y)) hG hpair
    show AnalyticAt ℂ
      (fun y : Weighted ω => center n + a (weightedPotential ω hω y) n (iter ω hω n k y)) x
    exact analyticAt_const.add hcomp

/-- Conclusion 1 of KST-033: the diagonal zero is analytic on the open component ball. -/
theorem diagonalZero_analyticOnNhd :
    AnalyticOnNhd ℂ (fun x : Weighted ω => diagonalZero n (weightedPotential ω hω x))
      (componentOpenBall ω (2*M)) := by
  have hU := isOpen_componentOpenBall ω (2*M)
  have hsub := componentOpenBall_subset ω (2*M)
  refine NlsGge.Atomic.G4.analyticOnNhd_of_locally_uniform_limit (f := iter ω hω n) hU
    (fun k x hx => iter_analyticAt w M hM hw n hn ω hω hball k x (hsub hx)) ?_
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Tendsto (fun k : ℕ => Real.pi / 48 * (1 / 23 : ℝ) ^ k) atTop (𝓝 0) := by
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 23 : ℝ)) (by norm_num)
      (by norm_num)
    simpa using h0.const_mul (Real.pi / 48)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with k hk x hx
  rw [dist_comm, dist_eq_norm]
  exact lt_of_le_of_lt (iter_dist w M hM hw n hn ω hω hball k x (hsub hx)) hk

end Iter

end NlsGge.ThirdConsultation.KST.KST033S
end
