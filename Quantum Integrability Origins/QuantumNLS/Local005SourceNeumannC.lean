import QuantumNLS.Local005FinalB
import QuantumNLS.Local002Analytic

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Metric
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace QuantumNLS.Local005.SourceC
open QuantumNLS.LocalSpectral
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.Local002

abbrev Op (L : ℝ) := H2 L →L[ℂ] H2 L
abbrev ContourOp (L r : ℝ) (n : ℤ) := C(sphere (center L n) r, Op L)

def free (L κ : ℝ) (n : ℤ) (z : ℂ) : Op L :=
  LocalSpectral.resolvent L κ (fun _ => 0) (parity n) z

def potentialConstant (L r κ : ℝ) : ℝ :=
  2 * Real.sqrt κ * resolventConstant L r

theorem potentialConstant_nonneg (L r κ : ℝ) : 0 ≤ potentialConstant L r κ := by
  unfold potentialConstant resolventConstant
  positivity

variable {L r κ : ℝ} [Fact (0 < L)]

theorem free_isResolvent (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    (n : ℤ) {z : ℂ} (hz : OnGamma L r n z) :
    IsResolvent L κ (fun _ => 0) (parity n) z (free L κ n z) := by
  rw [free, sourceResolvent_eq_candidate κ hL hr hsmall hz]
  exact freeResolventCandidate_isResolvent κ hL hr hsmall hz

 #print axioms free_isResolvent

/-- The bounded product is the actual source potential times the actual free inverse. -/

theorem potential_isMulOp (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) :
    IsMulOp κ (free L κ n z) (u : ℝ → ℂ)
      (potentialResolvent κ hκ.le hL n hr hsmall hz u) := by
  intro f
  have h := potentialResolventOutput_coe κ hκ.le hL n hr hsmall hz u f
  filter_upwards [h] with x hx
  change potentialResolventOutput κ hκ.le hL n hr hsmall hz u f x = _
  rw [hx]
  change potentialPt κ (u x) _ = Vpt κ (u x) _
  simp only [Vpt, lopPt, Local002.Jm_zero, smul_zero, zero_add]
  rfl

#print axioms potential_isMulOp

theorem mop_data (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) :
    IsMulOp κ (free L κ n z) (u : ℝ → ℂ) (Mop κ (free L κ n z) u) ∧
      ‖Mop κ (free L κ n z) u‖ ≤ potentialConstant L r κ * ‖u‖ := by
  have h := potential_isMulOp hL hκ hr hsmall n hz u
  rw [Mop_eq h]
  exact ⟨h, (reset_free_resolvent_estimates κ hL hκ n hr hsmall hz u).2.2.2⟩

#print axioms mop_data

theorem free_continuous (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    (n : ℤ) : ContinuousOn (free L κ n) (sphere (center L n) r) := by
  apply continuousOn_resolvent _ (M := r⁻¹) (by positivity)
  intro z hz
  have hg : OnGamma L r n z := mem_sphere_iff_norm.mp hz
  exact ⟨free L κ n z, free_isResolvent hL hr hsmall n hg,
    sourceResolvent_norm_le hL κ n hr hsmall hg⟩

theorem mop_continuous (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L) :
    Continuous (fun z : sphere (center L n) r => Mop κ (free L κ n z) u) := by
  have hK := potentialConstant_nonneg L r κ
  apply lip_of_mop (free L κ n) (M := potentialConstant L r κ / r) (by positivity)
  · intro z hz w hw v Tz Tw hTz hTw
    have hzg : OnGamma L r n z := mem_sphere_iff_norm.mp hz
    have hwg : OnGamma L r n w := mem_sphere_iff_norm.mp hw
    have hnz : ‖Tz‖ ≤ potentialConstant L r κ * ‖v‖ := by
      have he := hTz.unique (mop_data hL hκ hr hsmall n hzg v).1
      rw [he]
      exact (mop_data hL hκ hr hsmall n hzg v).2
    rw [mulop_sub (free_isResolvent hL hr hsmall n hzg)
      (free_isResolvent hL hr hsmall n hwg) hTz hTw, norm_smul]
    have hn : ‖Tz * free L κ n w‖ ≤ potentialConstant L r κ * ‖v‖ * r⁻¹ :=
      (norm_mul_le _ _).trans (mul_le_mul hnz
        (sourceResolvent_norm_le hL κ n hr hsmall hwg)
        (norm_nonneg _) (mul_nonneg hK (norm_nonneg _)))
    calc
      _ ≤ ‖w - z‖ * (potentialConstant L r κ * ‖v‖ * r⁻¹) :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev]; ring
  · intro z hz v
    exact ⟨_, (mop_data hL hκ hr hsmall n (mem_sphere_iff_norm.mp hz) v).1⟩

def freeContour (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    (n : ℤ) : ContourOp L r n :=
  ⟨fun z => free L κ n z, (free_continuous hL hr hsmall n).restrict⟩

def potentialContour (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L) : ContourOp L r n :=
  ⟨fun z => Mop κ (free L κ n z) u, mop_continuous hL hκ hr hsmall n u⟩

theorem potentialContour_norm (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L) :
    ‖potentialContour hL hκ hr hsmall n u‖ ≤ potentialConstant L r κ * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (potentialConstant_nonneg L r κ) (norm_nonneg _))).2
  intro z
  exact (mop_data hL hκ hr hsmall n (mem_sphere_iff_norm.mp z.2) u).2

/-- Identification with the source resolvent, proved from its two graph inverse laws. -/
theorem source_resolvent_eq_inverse (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L)
    (hu : potentialConstant L r κ * ‖u‖ < 1) (z : sphere (center L n) r) :
    LocalSpectral.resolvent L κ (u : ℝ → ℂ) (parity n) z =
      (freeContour (κ := κ) hL hr hsmall n *
        Ring.inverse (1 - potentialContour hL hκ hr hsmall n u)) z := by
  let T := potentialContour hL hκ hr hsmall n u
  have hT : ‖T‖ < 1 := (potentialContour_norm hL hκ hr hsmall n u).trans_lt hu
  have hTz : ‖T z‖ < 1 := (T.norm_coe_le_norm z).trans_lt hT
  have hg : OnGamma L r n z := mem_sphere_iff_norm.mp z.2
  obtain ⟨S, R, h1, h2, hR, hRes, _, _⟩ := resolvent_of_neumann
    (free_isResolvent (κ := κ) hL hr hsmall n hg)
    (mop_data hL hκ hr hsmall n hg u).1 hTz
  change (1 - T z) * S = 1 at h1
  have hinv : Ring.inverse (1 - T) = ↑(Units.oneSub T hT)⁻¹ :=
    NormedRing.inverse_one_sub T hT
  have he : ((↑(Units.oneSub T hT)⁻¹ : ContourOp L r n) z) * (1 - T z) = 1 := by
    have e := congrArg (fun F : ContourOp L r n => F z) (Units.inv_mul (Units.oneSub T hT))
    simpa only [Units.val_oneSub, ContinuousMap.mul_apply, ContinuousMap.one_apply,
      ContinuousMap.sub_apply] using e
  have hS : ((↑(Units.oneSub T hT)⁻¹ : ContourOp L r n) z) = S := by
    calc
      _ = ((↑(Units.oneSub T hT)⁻¹ : ContourOp L r n) z) * ((1 - T z) * S) := by
        rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, he, one_mul]
  rw [resolvent_eq hRes]
  change R = (freeContour (κ := κ) hL hr hsmall n * Ring.inverse (1 - T)) z
  rw [hinv, ContinuousMap.mul_apply, hS, hR]
  rfl

/-- Operator-norm Neumann convergence, uniform on the entire source contour. -/
theorem source_neumann_uniform (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (n : ℤ) (u : ScalarInterval L)
    (hu : potentialConstant L r κ * ‖u‖ < 1) :
    HasSum (fun k : ℕ => freeContour (κ := κ) hL hr hsmall n *
      potentialContour hL hκ hr hsmall n u ^ k)
      (freeContour (κ := κ) hL hr hsmall n *
        Ring.inverse (1 - potentialContour hL hκ hr hsmall n u)) := by
  let T : ContourOp L r n := potentialContour hL hκ hr hsmall n u
  let F : ContourOp L r n := freeContour (κ := κ) hL hr hsmall n
  have hT : ‖T‖ < 1 := (potentialContour_norm hL hκ hr hsmall n u).trans_lt hu
  have hs : HasSum (fun k : ℕ => T ^ k) (Ring.inverse (1 - T)) :=
    hasSum_geom_series_inverse T hT
  exact HasSum.mul_left F hs

#print axioms free_isResolvent
#print axioms potential_isMulOp
#print axioms mop_data
#print axioms mop_continuous
#print axioms source_resolvent_eq_inverse
#print axioms source_neumann_uniform
end QuantumNLS.Local005.SourceC
