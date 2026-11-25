import Mathlib
import QuantumNLS.Local007Gauge

/-! LOCAL-020 stage S8b: Liouville `det U(L) = 1` for the actual transfer matrix and the reflection law
`Δ_{v}(-z) = Δ_u(z)` whenever `v(x) = u(-x)` a.e. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Matrix Interval
namespace QuantumNLS.Local020DiscR
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.SpatialTransfer (balCoef coef Mat2)
open QuantumNLS.L1SpatialTransfer QuantumNLS.L2SpatialTransfer
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L : ℝ} [Fact (0 < L)]

theorem entry_norm_le (M : Mat2) (i j : Fin 2) : ‖M i j‖ ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖M i j‖₊ ≤ ∑ j', ‖M i j'‖₊ := Finset.single_le_sum (f := fun j' => ‖M i j'‖₊) (fun _ _ => zero_le') (Finset.mem_univ j)
  have h2 : ∑ j', ‖M i j'‖₊ ≤ Finset.univ.sup fun i => ∑ j', ‖M i j'‖₊ :=
    Finset.le_sup (f := fun i => ∑ j', ‖M i j'‖₊) (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

/-- The entry functional as a continuous linear map. -/
def entryCLM (i j : Fin 2) : Mat2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun M => by rw [one_mul]; exact entry_norm_le M i j)

theorem entryCLM_apply (i j : Fin 2) (M : Mat2) : entryCLM i j M = M i j := rfl

theorem entry_lipschitz (i j : Fin 2) : LipschitzWith 1 (fun M : Mat2 => M i j) := by
  refine LipschitzWith.of_dist_le_mul fun M N => ?_
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have := entry_norm_le (M - N) i j
  simpa using this

/-- **Liouville**: the actual transfer matrix has determinant one. -/
theorem det_transfer (κ : ℝ) (u : L2T L) (z : ℂ) : Matrix.det (spatialTransfer κ u z L) = 1 := by
  obtain ⟨h0, hac, hder, -⟩ := spatialTransfer_spec κ u z
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  set U := spatialTransfer κ u z with hU
  have eac : ∀ i j, AbsolutelyContinuousOnInterval (fun x => U x i j) 0 L := fun i j =>
    (entry_lipschitz i j).comp_absolutelyContinuousOnInterval hac
  have dac : AbsolutelyContinuousOnInterval (fun x => Matrix.det (U x)) 0 L := by
    have : (fun x => Matrix.det (U x)) = fun x => U x 0 0 * U x 1 1 - U x 0 1 * U x 1 0 := by
      funext x; rw [Matrix.det_fin_two]
    rw [this]
    exact ((eac 0 0).fun_smul (eac 1 1)).sub ((eac 0 1).fun_smul (eac 1 0))
  have hz : ∀ᵐ x, x ∈ uIcc (0 : ℝ) L → HasDerivAt (fun x => Matrix.det (U x)) 0 x := by
    have := (ae_restrict_iff' measurableSet_Icc).1 hder
    filter_upwards [this] with x hx hxm
    have hxI : x ∈ Icc 0 L := by simpa [uIcc_of_le hL] using hxm
    have hUx := hx hxI
    have e : ∀ i j, HasDerivAt (fun y => U y i j)
        ((balCoef κ (L2SpatialTransfer.profile u) z x * U x) i j) x := fun i j =>
      ((entryCLM i j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hUx
    have hd := ((e 0 0).mul (e 1 1)).sub ((e 0 1).mul (e 1 0))
    have hfun : (fun y => Matrix.det (U y)) = fun y => U y 0 0 * U y 1 1 - U y 0 1 * U y 1 0 := by
      funext y; rw [Matrix.det_fin_two]
    rw [hfun]
    refine hd.congr_deriv ?_
    simp only [Matrix.mul_apply, Fin.sum_univ_two, balCoef, coef]
    simp
    ring
  obtain ⟨C, hC⟩ := dac.const_of_ae_hasDerivAt_zero hz
  have e0 := hC 0 (by simp [uIcc_of_le hL, hL])
  have eL := hC L (by simp [uIcc_of_le hL, hL])
  have h1 : Matrix.det (U 0) = 1 := by rw [h0]; simp
  rw [h1] at e0
  show Matrix.det (U L) = 1
  rw [eL, ← e0]

open QuantumNLS.Local007Gauge (Jm Jm_mul_Jm Jc_apply trace_Jc)
open QuantumNLS.L2SpatialTransfer (profile spatialTransfer discriminant)

theorem profile_refl {u v : L2T L} (hv : (v : AddCircle L → ℂ) =ᵐ[volume] fun x => u (-x)) :
    (fun x : ℝ => profile v x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)] fun x => profile u (L - x) := by
  have h := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae_eq_comp hv
  simp only [zero_add] at h
  filter_upwards [h] with x hx
  have e : (((L - x : ℝ)) : AddCircle L) = -(x : AddCircle L) := by
    rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  simp only [profile, Function.comp] at hx ⊢
  rw [hx, e]

theorem balCoef_refl (κ : ℝ) {u v : L2T L} (hv : (v : AddCircle L → ℂ) =ᵐ[volume] fun x => u (-x)) (z : ℂ) :
    (fun x => balCoef κ (profile v) (-z) x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)]
      fun x => -(Jm * balCoef κ (profile u) z (L - x) * Jm) := by
  filter_upwards [profile_refl hv] with x hx
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jm, balCoef, coef, hx, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem trace_adjugate (M : Mat2) : Matrix.trace (Matrix.adjugate M) = Matrix.trace M := by
  rw [Matrix.adjugate_fin_two]
  simp [Matrix.trace_fin_two]; ring

/-- **Reversal.**  `Δ_v(-z) = Δ_u(z)` whenever `v(x) = u(-x)` a.e. -/
theorem disc_refl (κ : ℝ) {u v : L2T L} (hv : (v : AddCircle L → ℂ) =ᵐ[volume] fun x => u (-x)) (z : ℂ) :
    discriminant κ v (-z) = discriminant κ u z := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  let A := balCoef κ (profile u) z
  let AR := balCoef κ (profile v) (-z)
  let U := spatialTransfer κ u z
  let UR := spatialTransfer κ v (-z)
  let M := U L
  have hdet : Matrix.det M = 1 := det_transfer κ u z
  have hMA : M * Matrix.adjugate M = 1 := by rw [Matrix.mul_adjugate, hdet]; simp
  have hiA : IntervalIntegrable A volume 0 L :=
    intervalIntegrable_coef (intervalIntegrable_profile u) _ _ z
  have hiR : IntervalIntegrable AR volume 0 L :=
    intervalIntegrable_coef (intervalIntegrable_profile v) _ _ (-z)
  have hc : ContinuousOn U (Icc 0 L) := continuousOn_transfer hL hiA
  have hcR : ContinuousOn UR (Icc 0 L) := continuousOn_transfer hL hiR
  have hp : IntervalIntegrable (fun x => A x * U x) volume 0 L :=
    hiA.mul_continuousOn (by rw [uIcc_of_le hL]; exact hc)
  set Q : Mat2 := Matrix.adjugate M * Jm with hQ
  let N : ℝ → Mat2 := fun x => Jm * U (L - x) * Q
  have hNc : ContinuousOn N (Icc 0 L) := by
    have h1 : ContinuousOn (fun x => U (L - x)) (Icc 0 L) :=
      hc.comp (continuous_const.sub continuous_id).continuousOn
        (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    exact (continuousOn_const.mul h1).mul continuousOn_const
  let Φ : Mat2 →L[ℝ] Mat2 := ContinuousLinearMap.mulLeftRight ℝ Mat2 Jm Q
  have hΦ : ∀ X, Φ X = Jm * X * Q := fun X => rfl
  have hNe : ∀ x ∈ Icc 0 L, N x = 1 + ∫ s in (0 : ℝ)..x, AR s * N s := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxL : x ≤ L := hx.2
    -- the reflected integrand
    have hint1 : IntervalIntegrable (fun s => A (L - s) * U (L - s)) volume 0 x := by
      have h := hp.comp_sub_left L
      simp only [sub_self, sub_zero] at h
      exact (h.symm).mono_set (by
        rw [uIcc_of_le hx0, uIcc_of_le hL]; exact Icc_subset_Icc_right hxL)
    -- U(L-x) = M - ∫_0^x A(L-s)U(L-s)
    have hU1 : U (L - x) = M - ∫ s in (0 : ℝ)..x, A (L - s) * U (L - s) := by
      have e1 : U (L - x) = 1 + ∫ s in (0 : ℝ)..(L - x), A s * U s :=
        spatialTransfer_integral_eq κ u z (show L - x ∈ Icc 0 L from ⟨by linarith, by linarith⟩)
      have e2 : U L = 1 + ∫ s in (0 : ℝ)..L, A s * U s :=
        spatialTransfer_integral_eq κ u z (show L ∈ Icc 0 L from ⟨hL, le_rfl⟩)
      have hs : ∫ s in (0 : ℝ)..L, A s * U s =
          (∫ s in (0 : ℝ)..(L - x), A s * U s) + ∫ s in (L - x)..L, A s * U s :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hp.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le hL]; exact Icc_subset_Icc_right (by linarith)))
          (hp.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le hL]; exact Icc_subset_Icc (by linarith) le_rfl))).symm
      have hr : ∫ s in (0 : ℝ)..x, A (L - s) * U (L - s) = ∫ s in (L - x)..L, A s * U s := by
        have := intervalIntegral.integral_comp_sub_left (a := 0) (b := x) (fun s => A s * U s) L
        simpa using this
      rw [hr]
      rw [e1]
      show 1 + _ = U L - _
      rw [e2, hs]; abel
    -- a.e. identity for the reflected coefficient
    have JJ : ∀ Y : Mat2, Jm * (Jm * Y) = Y := fun Y => by
      rw [← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
    have hae : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) x → AR s * N s =
        -(Φ (A (L - s) * U (L - s))) := by
      have h1 := (ae_restrict_iff' measurableSet_Ioc).1 (balCoef_refl κ hv z)
      filter_upwards [h1] with s hs hsI
      rw [uIoc_of_le hx0] at hsI
      have hs' : AR s = -(Jm * A (L - s) * Jm) := hs ⟨hsI.1, hsI.2.trans hxL⟩
      rw [hs', hΦ, neg_mul]
      congr 1
      calc Jm * A (L - s) * Jm * N s = Jm * A (L - s) * (Jm * (Jm * U (L - s) * Q)) := by
            show Jm * A (L - s) * Jm * (Jm * U (L - s) * Q) = _
            rw [Matrix.mul_assoc]
        _ = Jm * A (L - s) * (U (L - s) * Q) := by
            rw [Matrix.mul_assoc Jm (U (L - s)) Q, JJ]
        _ = Jm * (A (L - s) * U (L - s)) * Q := by simp only [Matrix.mul_assoc]
    have hΦint : ∫ s in (0 : ℝ)..x, Φ (A (L - s) * U (L - s)) =
        Φ (∫ s in (0 : ℝ)..x, A (L - s) * U (L - s)) := Φ.intervalIntegral_comp_comm hint1
    rw [intervalIntegral.integral_congr_ae (by filter_upwards [hae] with s hs hsI using hs hsI),
      intervalIntegral.integral_neg, hΦint]
    have hMQ : Jm * M * Q = 1 := by
      rw [hQ]
      calc Jm * M * (Matrix.adjugate M * Jm) = Jm * (M * Matrix.adjugate M) * Jm := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hMA, Matrix.mul_one, Jm_mul_Jm]
    show Jm * U (L - x) * Q = _
    rw [hU1, Matrix.mul_sub, Matrix.sub_mul, hMQ, hΦ, sub_eq_add_neg]
  have := integral_solution_unique hL hiR hcR hNc (fun x hx => spatialTransfer_integral_eq κ v (-z) hx) hNe
  have hLx := this (show L ∈ Icc 0 L from ⟨hL, le_rfl⟩)
  unfold discriminant
  change Matrix.trace (UR L) = _
  rw [hLx]
  change Matrix.trace (Jm * U (L - L) * Q) = Matrix.trace M
  have h0 : U 0 = 1 := (spatialTransfer_spec κ u z).1
  rw [sub_self, h0, hQ, Matrix.mul_one]
  have := trace_Jc (Matrix.adjugate M)
  rw [Jc_apply] at this
  rw [← Matrix.mul_assoc, this, trace_adjugate]

end QuantumNLS.Local020DiscR

#print axioms QuantumNLS.Local020DiscR.disc_refl
#print axioms QuantumNLS.Local020DiscR.det_transfer
