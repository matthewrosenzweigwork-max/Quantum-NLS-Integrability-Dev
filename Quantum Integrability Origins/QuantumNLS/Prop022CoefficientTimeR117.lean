import QuantumNLS.Prop022ActualProfileR117
import Mathlib.Analysis.Calculus.MeanValue

/-! Operator-norm coefficient time differentiation along the constructed
factorial trajectory. The derivative majorants are proved, not supplied. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace Topology ContDiff NNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022CoefficientTimeR117
open TensorCarrier PhysicalTensor BetheCoefficientTransform
open Prop022TensorCompressionR115 Prop022FactorialCoefficientsR115
open Prop022FactorialMajorantR115 Prop022TensorCalculusR116 Prop022ActualProfileR117
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup
local instance (priority := 1200) opAddGroup : AddCommGroup (HN L 1 →L[ℂ] HN L 1) :=
  (inferInstance : NormedAddCommGroup (HN L 1 →L[ℂ] HN L 1)).toAddCommGroup
local instance (priority := 1200) opRealNS : NormedSpace ℝ (HN L 1 →L[ℂ] HN L 1) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance (priority := 1200) opRealModule : Module ℝ (HN L 1 →L[ℂ] HN L 1) :=
  (opRealNS (L := L)).toModule
local instance (priority := 1200) opRealSMul : SMul ℝ (HN L 1 →L[ℂ] HN L 1) :=
  (opRealNS (L := L)).toSMul
local instance (n : ℕ) : AddCommGroup (HilbertTensorPower ℂ (L2T L) n) :=
  (inferInstance : NormedAddCommGroup (HilbertTensorPower ℂ (L2T L) n)).toAddCommGroup

lemma power_sub_bound (m : ℕ) (u v : L2T L) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖power m u - power m v‖ ≤ (m : ℝ) * ‖u-v‖ := by
  change ‖(htpow m u : HilbertTensorPower ℂ (L2T L) m) - htpow m v‖ ≤ _
  simpa using Ext025A8.tensorPower_lipschitz m (S := 1) (by norm_num) hu.le hv.le

lemma insertion_sub_bound (r k : ℕ) (u v : L2T L) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖insertion r k u - insertion r k v‖ ≤ (r : ℝ) * ‖u-v‖ := by
  apply opNorm_le_bound _ (by positivity)
  intro x
  change ‖(physSector L (r+k)).orthogonalProjectionOnto
      ((splitIsometry r k).symm (htmul (htpow r u) (x : HilbertTensorPower ℂ (L2T L) k))) -
    (physSector L (r+k)).orthogonalProjectionOnto
      ((splitIsometry r k).symm (htmul (htpow r v) (x : HilbertTensorPower ℂ (L2T L) k)))‖ ≤ _
  rw [← map_sub, ← map_sub]
  have he : htmul ((htpow r u : HilbertTensorPower ℂ (L2T L) r) - htpow r v)
      (x : HilbertTensorPower ℂ (L2T L) k) =
      htmul (𝕜 := ℂ) (htpow r u) (x : HilbertTensorPower ℂ (L2T L) k) - htmul (htpow r v) (x : HilbertTensorPower ℂ (L2T L) k) := by
    simp [htmul, TensorProduct.sub_tmul, UniformSpace.Completion.coe_sub]
  rw [← he]
  calc
    _ ≤ ‖(splitIsometry r k).symm
        (htmul ((htpow r u : HilbertTensorPower ℂ (L2T L) r) - htpow r v)
          (x : HilbertTensorPower ℂ (L2T L) k))‖ :=
      Submodule.norm_orthogonalProjectionOnto_apply_le _ _
    _ = ‖(htpow r u : HilbertTensorPower ℂ (L2T L) r) - htpow r v‖ * ‖x‖ := by
      rw [LinearIsometryEquiv.norm_map, norm_htmul]; rfl
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      simpa using Ext025A8.tensorPower_lipschitz r (S := 1) (by norm_num) hu.le hv.le

section Compression
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
lemma compression_sub (I J : E →L[ℂ] F) (B : F →L[ℂ] F)
    (hI : ‖I‖ ≤ 1) (hJ : ‖J‖ ≤ 1) :
    ‖I.adjoint ∘L B ∘L I - J.adjoint ∘L B ∘L J‖ ≤ 2 * ‖B‖ * ‖I-J‖ := by
  have he : I.adjoint ∘L B ∘L I - J.adjoint ∘L B ∘L J =
      (I.adjoint-J.adjoint) ∘L B ∘L I + J.adjoint ∘L B ∘L (I-J) := by
    ext x
    simp only [sub_apply, add_apply, comp_apply, map_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(I.adjoint-J.adjoint) ∘L B ∘L I‖ + ‖J.adjoint ∘L B ∘L (I-J)‖ := norm_add_le _ _
    _ ≤ ‖I.adjoint-J.adjoint‖ * (‖B‖ * ‖I‖) + ‖J.adjoint‖ * (‖B‖ * ‖I-J‖) := by
      apply add_le_add
      · exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      · exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖I-J‖ * (‖B‖ * 1) + 1 * (‖B‖ * ‖I-J‖) := by
      rw [← map_sub adjoint, adjoint.norm_map, adjoint.norm_map]
      gcongr
    _ = _ := by ring

lemma adjoint_apply_sub (I J : E →L[ℂ] F) (B : F →L[ℂ] F) (x y : F)
    (hJ : ‖J‖ ≤ 1) (hx : ‖x‖ ≤ 1) :
    ‖I.adjoint (B x) - J.adjoint (B y)‖ ≤ ‖B‖ * (‖I-J‖ + ‖x-y‖) := by
  have he : I.adjoint (B x) - J.adjoint (B y) =
      (I.adjoint-J.adjoint) (B x) + J.adjoint (B (x-y)) := by
    simp only [sub_apply, map_sub]; abel
  rw [he]
  calc
    _ ≤ ‖(I.adjoint-J.adjoint) (B x)‖ + ‖J.adjoint (B (x-y))‖ := norm_add_le _ _
    _ ≤ ‖I.adjoint-J.adjoint‖ * (‖B‖ * ‖x‖) + ‖J.adjoint‖ * (‖B‖ * ‖x-y‖) := by
      apply add_le_add
      · exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _))
      · exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _))
    _ ≤ ‖I-J‖ * (‖B‖ * 1) + 1 * (‖B‖ * ‖x-y‖) := by
      rw [← map_sub adjoint, adjoint.norm_map, adjoint.norm_map]
      gcongr
    _ = _ := by ring
end Compression

lemma mixed_sub_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (r : ℕ)
    (u v : L2T L) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖mixedTerm B u r - mixedTerm B v r‖ ≤
      2 * ((r+1 : ℕ) : ℝ)^3 * ‖B (r+1)‖ * ‖u-v‖ := by
  have hc := compression_sub (insertion r 1 u) (insertion r 1 v) (B (r+1))
    (insertion_unit r 1 u hu) (insertion_unit r 1 v hv)
  have hi := insertion_sub_bound r 1 u v hu hv
  have hb : ‖(insertion r 1 u).adjoint ∘L B (r+1) ∘L insertion r 1 u -
      (insertion r 1 v).adjoint ∘L B (r+1) ∘L insertion r 1 v‖ ≤
      2 * ‖B (r+1)‖ * ((r : ℝ) * ‖u-v‖) :=
    hc.trans (mul_le_mul_of_nonneg_left hi (by positivity))
  apply opNorm_le_bound _ (by positivity)
  intro x
  change ‖(((r+1 : ℕ) : ℂ)^2) •
    (((insertion r 1 u).adjoint ∘L B (r+1) ∘L insertion r 1 u) x) -
    (((r+1 : ℕ) : ℂ)^2) •
    (((insertion r 1 v).adjoint ∘L B (r+1) ∘L insertion r 1 v) x)‖ ≤ _
  rw [← smul_sub, norm_smul, norm_pow, Complex.norm_natCast]
  have hx : ‖((insertion r 1 u).adjoint ∘L B (r+1) ∘L insertion r 1 u) x -
      ((insertion r 1 v).adjoint ∘L B (r+1) ∘L insertion r 1 v) x‖ ≤
      (2 * ‖B (r+1)‖ * ((r : ℝ) * ‖u-v‖)) * ‖x‖ :=
    (le_opNorm (_ - _) x).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg x))
  calc
    _ ≤ ((r+1 : ℕ) : ℝ)^2 * ((2 * ‖B (r+1)‖ * ((r : ℝ) * ‖u-v‖)) * ‖x‖) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ ((r+1 : ℕ) : ℝ)^2 * ((2 * ‖B (r+1)‖ * (((r+1 : ℕ) : ℝ) * ‖u-v‖)) * ‖x‖) := by
      gcongr; norm_num
    _ = _ := by ring

lemma pair_sub_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (r : ℕ)
    (u v : L2T L) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖Prop022TensorCompressionR115.pairTerm B u r - Prop022TensorCompressionR115.pairTerm B v r‖ ≤
      2 * ((r+2 : ℕ) : ℝ)^3 * ‖B (r+2)‖ * ‖u-v‖ := by
  rw [Prop022TensorCompressionR115.pairTerm, Prop022TensorCompressionR115.pairTerm,
    ← smul_sub, norm_smul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hp : ‖power (r+2) u‖ ≤ 1 := by rw [power_norm, hu, one_pow]
  have hc := adjoint_apply_sub (insertion r 2 u) (insertion r 2 v) (B (r+2))
    (power (r+2) u) (power (r+2) v) (insertion_unit r 2 v hv) hp
  have hi := insertion_sub_bound r 2 u v hu hv
  have hd := power_sub_bound (r+2) u v hu hv
  calc
    _ ≤ (((r+2 : ℕ) : ℝ) * ((r+1 : ℕ) : ℝ)) *
        (‖B (r+2)‖ * ((r : ℝ) * ‖u-v‖ + ((r+2 : ℕ) : ℝ) * ‖u-v‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hc.trans (mul_le_mul_of_nonneg_left (add_le_add hi hd) (norm_nonneg _))
    _ ≤ (((r+2 : ℕ) : ℝ) * ((r+2 : ℕ) : ℝ)) *
        (‖B (r+2)‖ * (((r+2 : ℕ) : ℝ) * ‖u-v‖ + ((r+2 : ℕ) : ℝ) * ‖u-v‖)) := by
      gcongr <;> norm_num
    _ = _ := by ring

/-- Actual path speed yields a global norm difference estimate. -/
lemma profile_lipschitz (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L)) :
    let u := profile B M A hA hB hs u₀
    ∀ t s, ‖u t - u s‖ ≤ (M * ∑' n, weight 1 A (n+1)) * ‖t-s‖ := by
  dsimp only
  have h := profile_spec B M A hA hB hs u₀
  let K : ℝ≥0 := ⟨M * ∑' n, weight 1 A (n+1),
    mul_nonneg hM (tsum_nonneg (fun n => by unfold weight; positivity))⟩
  have hl : LipschitzWith K (profile B M A hA hB hs u₀) :=
    lipschitzWith_of_nnnorm_deriv_le (fun t => (h.2.2.2.1 t).differentiableAt) (fun t => by
      change ‖deriv (profile B M A hA hB hs u₀) t‖ ≤ (K : ℝ)
      rw [(h.2.2.2.1 t).deriv]
      exact h.2.2.2.2 t)
  exact hl.norm_sub_le

section Series
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
/-- Uniformly summable derivative bounds give a C1 sum. -/
lemma series_C1 (f : ℕ → ℝ → E) (c : ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ 1 (f n)) (hc : Summable c)
    (hd : ∀ n t, ‖deriv (f n) t‖ ≤ c n) (h0 : Summable (fun n => f n 0)) :
    ContDiff ℝ 1 (fun t => ∑' n, f n t) ∧
      (∀ t, HasDerivAt (fun s => ∑' n, f n s) (∑' n, deriv (f n) t) t) := by
  have hh (t : ℝ) := hasDerivAt_tsum hc
    (fun n t => ((hf n).differentiable (by norm_num) t).hasDerivAt) hd h0 t
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun t => (hh t).differentiableAt, ?_⟩, hh⟩
  have he : deriv (fun s => ∑' n, f n s) = fun t => ∑' n, deriv (f n) t :=
    funext (fun t => (hh t).deriv)
  rw [he]
  exact continuous_tsum (fun n => (hf n).continuous_deriv_one) hc hd
end Series

/-- Both coefficients are C1 on the actual trajectory, with differentiated
series identities and uniform derivative bounds. No profile hypotheses remain. -/
theorem actual_coefficients_C1
    (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) :
    let u := profile B M A hA hB hs u₀
    let K := M * ∑' n, weight 1 A (n+1)
    ContDiff ℝ 1 (fun t => numberCoefficient B (u t)) ∧
    ContDiff ℝ 1 (fun t => pairCoefficient B (u t)) ∧
    (∀ t, HasDerivAt (fun s => numberCoefficient B (u s))
      (∑' r, deriv (fun s => mixedTerm B (u s) r) t) t) ∧
    (∀ t, HasDerivAt (fun s => pairCoefficient B (u s))
      (∑' r, deriv (fun s => Prop022TensorCompressionR115.pairTerm B (u s) r) t) t) ∧
    (∀ t, ‖deriv (fun s => numberCoefficient B (u s)) t‖ ≤
      (2*K*M) * ∑' r, weight 3 A (r+1)) ∧
    (∀ t, ‖deriv (fun s => pairCoefficient B (u s)) t‖ ≤
      (2*K*M) * ∑' r, weight 3 A (r+2)) := by
  dsimp only
  let u := profile B M A hA hB hs u₀
  let K := M * ∑' n, weight 1 A (n+1)
  have hK : 0 ≤ K := mul_nonneg hM (tsum_nonneg (fun n => by unfold weight; positivity))
  have hp := profile_spec B M A hA hB hs u₀
  have hl := profile_lipschitz B M A hM hA hB hs u₀
  have hm (r : ℕ) (t : ℝ) : ‖deriv (fun s => mixedTerm B (u s) r) t‖ ≤
      (2*K*M) * weight 3 A (r+1) := by
    have hd : ‖deriv (fun s => mixedTerm B (u s) r) t‖ ≤
        2 * ((r+1 : ℕ) : ℝ)^3 * ‖B (r+1)‖ * K := by
      apply norm_deriv_le_of_lip' (by positivity)
      exact Filter.Eventually.of_forall (fun s =>
        (mixed_sub_bound B r (u s) (u t) (hp.2.2.1 s) (hp.2.2.1 t)).trans (by
          calc
            _ ≤ 2 * ((r+1 : ℕ) : ℝ)^3 * ‖B (r+1)‖ * (K * ‖s-t‖) := by gcongr; exact hl s t
            _ = _ := by ring))
    apply hd.trans
    calc
      _ ≤ 2 * ((r+1 : ℕ) : ℝ)^3 * (M * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ)) * K := by
        gcongr; exact hB (r+1) (by omega)
      _ = _ := by unfold weight; ring
  have hb (r : ℕ) (t : ℝ) : ‖deriv (fun s => Prop022TensorCompressionR115.pairTerm B (u s) r) t‖ ≤
      (2*K*M) * weight 3 A (r+2) := by
    have hd : ‖deriv (fun s => Prop022TensorCompressionR115.pairTerm B (u s) r) t‖ ≤
        2 * ((r+2 : ℕ) : ℝ)^3 * ‖B (r+2)‖ * K := by
      apply norm_deriv_le_of_lip' (by positivity)
      exact Filter.Eventually.of_forall (fun s =>
        (pair_sub_bound B r (u s) (u t) (hp.2.2.1 s) (hp.2.2.1 t)).trans (by
          calc
            _ ≤ 2 * ((r+2 : ℕ) : ℝ)^3 * ‖B (r+2)‖ * (K * ‖s-t‖) := by gcongr; exact hl s t
            _ = _ := by ring))
    apply hd.trans
    calc
      _ ≤ 2 * ((r+2 : ℕ) : ℝ)^3 * (M * A^(r+2) / Real.sqrt ((2*(r+2)).factorial : ℝ)) * K := by
        gcongr; exact hB (r+2) (by omega)
      _ = _ := by unfold weight; ring
  have hsm := ((summable_nat_add_iff 1).mpr (weight_summable 3 A hA)).mul_left (2*K*M)
  have hsb := ((summable_nat_add_iff 2).mpr (weight_summable 3 A hA)).mul_left (2*K*M)
  have hcm := series_C1 (fun r s => mixedTerm B (u s) r) _
    (fun r => (mixedTerm_smooth B r 1).comp hp.2.1) hsm hm
    (mixed_summable B M A hA hB (u 0) (hp.2.2.1 0))
  have hcb := series_C1 (fun r s => Prop022TensorCompressionR115.pairTerm B (u s) r) _
    (fun r => (pairTerm_smooth B r 1).comp hp.2.1) hsb hb
    (Prop022FactorialCoefficientsR115.pair_summable B M A hA hB (u 0) (hp.2.2.1 0))
  refine ⟨hcm.1, hcb.1, hcm.2, hcb.2, ?_, ?_⟩
  · intro t
    change ‖deriv (fun s => ∑' r, mixedTerm B (u s) r) t‖ ≤ (2*K*M) * ∑' r, weight 3 A (r+1)
    rw [(hcm.2 t).deriv]
    simpa only [tsum_mul_left] using tsum_of_norm_bounded hsm.hasSum (fun r => hm r t)
  · intro t
    change ‖deriv (fun s => ∑' r, Prop022TensorCompressionR115.pairTerm B (u s) r) t‖ ≤
      (2*K*M) * ∑' r, weight 3 A (r+2)
    rw [(hcb.2 t).deriv]
    simpa only [tsum_mul_left] using tsum_of_norm_bounded hsb.hasSum (fun r => hb r t)
end QuantumNLS.Prop022CoefficientTimeR117
#print axioms QuantumNLS.Prop022CoefficientTimeR117.insertion_sub_bound
#print axioms QuantumNLS.Prop022CoefficientTimeR117.actual_coefficients_C1

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022CoefficientTimeR117." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022CoefficientTimeR117." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R117 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
