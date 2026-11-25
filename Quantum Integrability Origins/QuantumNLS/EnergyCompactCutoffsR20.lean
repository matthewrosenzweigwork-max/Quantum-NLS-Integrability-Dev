import QuantumNLS.SourceEnergyRealizationR13
import QuantumNLS.Ext025A12Normal

/-! Bounded continuous cutoffs for R-C17D95AA, on the exact arbitrary-A
square root constructed in frozen r13. All multipliers used here are bounded.
The unbounded half is used only on its exact domain, never as a domain-preserving map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace ComplexOrder
namespace QuantumNLS.EnergyCompactCutoffsR20
open CFCCutoffsR13 BoundedInverseR13 InverseSquareRootR13
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Global bound for the scalar root-cutoff multiplier, including negative t. -/
theorem rootCut_bound (n : ℕ) (t : ℝ) :
    |rootCut n t| ≤ (Real.sqrt (1/(2*((n : ℝ)+1))))⁻¹ := by
  have ha : 0 < 1/(2*((n : ℝ)+1)) := by positivity
  have hb : 0 < Real.sqrt (max t (1/(2*((n : ℝ)+1)))) :=
    Real.sqrt_pos.mpr (ha.trans_le (le_max_right _ _))
  have hc : 0 ≤ rootCut n t := div_nonneg (cut_nonneg n t) hb.le
  rw [abs_of_nonneg hc]
  unfold rootCut
  calc
    _ ≤ 1 / Real.sqrt (max t (1/(2*((n : ℝ)+1)))) :=
      div_le_div_of_nonneg_right (cut_le_one n t) hb.le
    _ ≤ 1 / Real.sqrt (1/(2*((n : ℝ)+1))) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr ha)
        (Real.sqrt_le_sqrt (le_max_right _ _))
    _ = _ := one_div _

/-- The actual bounded operator has the explicit scalar bound. -/
theorem rootCutoff_bound (R : E →L[ℂ] E) (n : ℕ) :
    ‖rootCutoff R n‖ ≤ (Real.sqrt (1/(2*((n : ℝ)+1))))⁻¹ := by
  apply norm_cfc_le (by positivity)
  intro t _
  exact (Real.norm_eq_abs _).trans_le (rootCut_bound n t)

/-- The inverse-root multiplier is bounded by one on the actual spectrum. -/
theorem inverseRoot_bound (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A) :
    ‖rootInv A hA h‖ ≤ 1 := by
  have hs := CStarRing.norm_star_mul_self (x := rootInv A hA h)
  rw [(rootInv_selfAdjoint A hA h).star_eq,rootInv_square] at hs
  have hi := inverse_norm A hA h
  nlinarith [norm_nonneg (rootInv A hA h)]

theorem complement_norm (R : E →L[ℂ] E) (n : ℕ) : ‖1-cutoff R n‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr (cutoff_le_one R n))).mpr
  have hp := cutoff_nonneg R n
  simpa only [sub_le_self_iff] using hp

/-- Strong spectral exhaustion converges in norm after a compact operator. -/
theorem compact_left (R : E →L[ℂ] E) (hR : 0 ≤ R) (hd : DenseRange R) (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) :
    Tendsto (fun n => (1 - cutoff R n) * T) atTop (𝓝 0) := by
  obtain ⟨K,hK,hTK⟩ := hT.image_closedBall_subset_compact 1
  have hU := Metric.tendstoUniformly_iff.mp (ContinuousExhaustionR13.uniform_compact R hR hd K hK)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (norm_nonneg _)
  · intro ε hε
    filter_upwards [hU (ε/2) (by linarith)] with n hn
    have hb : ‖(1-cutoff R n)*T‖ ≤ ε/2 := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith)
      intro x hx
      have hxK : T x ∈ K := hTK ⟨x,by simp [Metric.mem_closedBall,dist_zero_right,hx],rfl⟩
      have hi := hn ⟨T x,hxK⟩
      change dist (T x) (cutoff R n (T x)) < ε/2 at hi
      change ‖T x-cutoff R n (T x)‖ ≤ ε/2
      simpa only [dist_eq_norm] using hi.le
    linarith

/-- The right compact tail follows from the left tail of T* T. This avoids
assuming norm convergence of the spectral projections themselves. -/
theorem compact_right (R : E →L[ℂ] E) (hR : 0 ≤ R) (hd : DenseRange R) (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) :
    Tendsto (fun n => T * (1 - cutoff R n)) atTop (𝓝 0) := by
  have hTT : IsCompactOperator (T.adjoint * T) := hT.clm_comp T.adjoint
  have hleft := compact_left R hR hd (T.adjoint*T) hTT
  have hsq (n : ℕ) : ‖T*(1-cutoff R n)‖^2 ≤
      ‖(1-cutoff R n)*(T.adjoint*T)‖ := by
    let Z := 1-cutoff R n
    have hZ : Z.adjoint = Z := by
      simp only [Z,map_sub,ContinuousLinearMap.adjoint_one,cutoff_symmetric R n]
    have he : (T*Z).adjoint*(T*Z) = (Z*(T.adjoint*T))*Z := by
      change star (T*Z)*(T*Z) = (Z*(star T*T))*Z
      rw [star_mul,show star Z = Z from hZ]
      simp only [mul_assoc]
    calc
      ‖T*Z‖^2 = ‖(T*Z).adjoint*(T*Z)‖ := by
        simpa only [ContinuousLinearMap.mul_def,pow_two] using
          (ContinuousLinearMap.norm_adjoint_comp_self (T*Z)).symm
      _ = ‖(Z*(T.adjoint*T))*Z‖ := congrArg norm he
      _ ≤ ‖Z*(T.adjoint*T)‖ * ‖Z‖ := norm_mul_le _ _
      _ ≤ ‖Z*(T.adjoint*T)‖ * 1 :=
        mul_le_mul_of_nonneg_left (complement_norm R n) (norm_nonneg _)
      _ = _ := mul_one _
  have hz : Tendsto (fun n => ‖T*(1-cutoff R n)‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hsq (by simpa using hleft.norm)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _)] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hz

/-- The precise compact norm-compression step in R-C17D95AA. -/
theorem compact_compression (R : E →L[ℂ] E) (hR : 0 ≤ R) (hd : DenseRange R) (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) :
    Tendsto (fun n => cutoff R n*T*cutoff R n) atTop (𝓝 T) := by
  have hleft := compact_left R hR hd T hT
  have hright := compact_right R hR hd T hT
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using hleft.norm.add hright.norm)
  intro n
  have hP : ‖cutoff R n‖ ≤ 1 :=
    cutoff_norm R n
  have he : T-cutoff R n*T*cutoff R n =
      (1-cutoff R n)*T+cutoff R n*(T*(1-cutoff R n)) := by noncomm_ring
  rw [norm_sub_rev,he]
  apply (norm_add_le _ _).trans
  apply add_le_add (le_refl _)
  calc
    ‖cutoff R n*(T*(1-cutoff R n))‖ ≤
        ‖cutoff R n‖*‖T*(1-cutoff R n)‖ := norm_mul_le _ _
    _ ≤ 1*‖T*(1-cutoff R n)‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ = _ := one_mul _


/-- Every use of square-root-domain preservation is justified by this exact
bounded factorization: the cutoff maps the entire ambient space into Q(A). -/
theorem cutoff_form_domain (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)
    (n : ℕ) (x : E) :
    cutoff (inverse A hA h) n x ∈ (half A hA h).domain :=
  ArbitraryEnergyTraceR13.cutoff_mem A hA h n x

end QuantumNLS.EnergyCompactCutoffsR20
