import QuantumNLS.Q07ChargeAnalyticR24
import QuantumNLS.Q07SobolevCutsR16

/-! Exact DEF-002 Sobolev norm and dense smooth Fourier approximations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open Set Metric Filter Topology MeasureTheory
open scoped ContDiff
namespace QuantumNLS.Q07SobolevModelR24
open RiccatiSobolevBanach RiccatiSobolevE1 RiccatiSobolevE2b
open ComplexifiedSobolevField ClassicalCharges Sobolev Sobolev.PosWeight
open RiccatiPointwiseDisc RiccatiPointwise
variable {L S : ℝ} [Fact (0 < L)]

/-- The exact isometric DEF-002 Fourier coordinates, with no norm equivalence loss. -/
def coordinates (hs : 0 ≤ S) : H02 L S ≃ₗᵢ[ℂ] Ell2 :=
  (fourierHs (L := L) (one_le_def002 L hs)).trans (toL2ᵢ (def002 L S))

lemma toField_coordinates (hs : 0 ≤ S) (u : H02 L S) (k : ℤ) :
    toField L S (coordinates hs u) k = Fourier.coeff L u.val k := by
  have he : Real.sqrt ((def002 L S).w k) = pw L S k := by
    change Real.sqrt (wt L S k) = _
    rw [wt_eq_pw_sq,Real.sqrt_sq_eq_abs,abs_of_pos (pw_pos L S k)]
  change ((Real.sqrt ((def002 L S).w k) : ℂ)*
    (fourierHs (L := L) (one_le_def002 L hs) u).val k) / (pw L S k : ℂ) = _
  rw [he,fourierHs_val,Fourier.fourierL2_apply]
  exact mul_div_cancel_left₀ _ (pw_ne_zero L S k)

lemma fieldMap_coordinates (hs : 0 ≤ S) (u : H02 L S) :
    fieldMap L S hs (coordinates hs u) = u.val := by
  apply (Fourier.fourierL2 L).injective
  ext k
  simp only [Fourier.fourierL2_apply,coeff_fieldMap,toField_coordinates]

def model (hs : 0 ≤ S) (x : Ell2) : H02 L S := (coordinates (L := L) hs).symm x

@[simp] lemma model_val (hs : 0 ≤ S) (x : Ell2) : (model (L := L) hs x).val = fieldMap L S hs x := by
  have h := fieldMap_coordinates (L := L) hs ((coordinates (L := L) hs).symm x)
  simpa only [model,LinearIsometryEquiv.apply_symm_apply] using h.symm

@[simp] lemma norm_model (hs : 0 ≤ S) (x : Ell2) : ‖model (L := L) hs x‖ = ‖x‖ :=
  (coordinates (L := L) hs).symm.norm_map x

lemma class_mem (hs : 0 ≤ S) {B : ℝ} (x : Ell2) (hx : ‖x‖ ≤ B) :
    fieldMap L S hs x ∈ Q07SobolevCutsR16.sobolevClass (L := L) S B :=
  ⟨model (L := L) hs x,by simpa using hx,model_val hs x⟩

/-- Finite Fourier sums in the exact H^S coordinates. -/
def approx (x : Ell2) (J : Finset ℤ) : Ell2 := ∑ k ∈ J, lp.single 2 k (x k)

lemma approx_tendsto (x : Ell2) : Tendsto (approx x) atTop (𝓝 x) :=
  lp.hasSum_single (by norm_num) x

lemma approx_apply (x : Ell2) (J : Finset ℤ) (k : ℤ) :
    approx x J k = if k ∈ J then x k else 0 := by
  classical
  unfold approx
  rw [lp.coeFn_sum,Finset.sum_apply]
  change (∑ i ∈ J, Pi.single i (x i) k) = _
  exact Finset.sum_pi_single k x J

lemma approx_norm_le (x : Ell2) (J : Finset ℤ) : ‖approx x J‖ ≤ ‖x‖ := by
  apply (norm_le_of_pointwise (C := 1) zero_le_one ?_).trans_eq (one_mul _)
  intro k
  classical
  rw [approx_apply]
  split_ifs <;> simp

lemma approx_smooth (x : Ell2) (J : Finset ℤ) :
    SmoothPeriodic L (physRep L S (approx x J)) := by
  classical
  have he : physRep L S (approx x J) = fun t =>
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
        ∑ k ∈ J, (x k / (pw L S k : ℂ))*ex L k t := by
    funext t
    unfold physRep series
    simp_rw [toField,approx_apply]
    rw [tsum_eq_sum (s := J)]
    · congr 1
      apply Finset.sum_congr rfl
      intro k hk
      simp only [ite_eq_left hk]
    · intro k hk
      simp only [ite_eq_right hk,zero_div,zero_mul]
  rw [he]
  constructor
  · apply contDiff_const.mul
    apply ContDiff.sum
    intro k hk
    unfold ex
    exact contDiff_const.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  · intro t
    change (((Real.sqrt L)⁻¹ : ℝ) : ℂ)*(∑ k ∈ J, (x k/(pw L S k : ℂ))*ex L k (t+L)) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ)*(∑ k ∈ J, (x k/(pw L S k : ℂ))*ex L k t)
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [RiccatiPointwise.ex_add_period (Fact.out : 0 < L).ne' k t]

end QuantumNLS.Q07SobolevModelR24
