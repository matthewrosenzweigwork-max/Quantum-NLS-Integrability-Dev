import QuantumNLS.RiccatiPicardBall
import QuantumNLS.ComplexifiedSobolevField

/-! Elementary H^a resolvent convergence for the energy-moment route.
Ell2 at weight a is the existing complete Fourier Sobolev model. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped Topology
open Filter Complex
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
namespace QuantumNLS.RootEnergyMomentResolvent

def y (n : ℕ) : ℝ := (n : ℝ)+1
def z (n : ℕ) : ℂ := (y n : ℂ) * Complex.I
lemma y_pos (n : ℕ) : 0 < y n := by unfold y; positivity
lemma z_im (n : ℕ) : (z n).im = y n := by simp [z]
lemma z_pos (n : ℕ) : 0 < (z n).im := by rw [z_im]; exact y_pos n

def scaledR (L : ℝ) (n : ℕ) : Ell2 →L[ℂ] Ell2 :=
  (y n : ℂ) • ropCLM L (z n) (z_pos n)

lemma scaledR_norm (L : ℝ) (n : ℕ) (x : Ell2) : ‖scaledR L n x‖ ≤ ‖x‖ := by
  change ‖(y n : ℂ) • ropCLM L (z n) (z_pos n) x‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (y_pos n).le]
  calc
    _ ≤ y n * ((z n).im⁻¹ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_ropCLM_le L (z n) (z_pos n) x) (y_pos n).le
    _ = ‖x‖ := by rw [z_im, ← mul_assoc, mul_inv_cancel₀ (y_pos n).ne', one_mul]

lemma scaledR_apply (L : ℝ) (n : ℕ) (x : Ell2) (k : ℤ) :
    scaledR L n x k = x k / (1 + Complex.I * (freq L k : ℂ) / (y n : ℂ)) := by
  change (y n : ℂ) * (x k / (Complex.I * ((freq L k : ℂ)-z n))) = _
  have hy : (y n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (y_pos n).ne'
  have hd : Complex.I * ((freq L k : ℂ)-z n) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by
      intro he
      have hi := congrArg Complex.im he
      simp only [Complex.sub_im, Complex.ofReal_im, z_im, Complex.zero_im] at hi
      have hp := y_pos n
      linarith)
  have he : 1 + Complex.I * (freq L k : ℂ) / (y n : ℂ) =
      (Complex.I * ((freq L k : ℂ)-z n)) / (y n : ℂ) := by
    unfold z
    field_simp
    linear_combination (y n : ℂ) * Complex.I_mul_I
  rw [he]
  field_simp [hy, hd]

lemma scaledR_coordinate_bound (L : ℝ) (n : ℕ) (x : Ell2) (k : ℤ) :
    ‖scaledR L n x k‖ ≤ ‖x k‖ := by
  change ‖(y n : ℂ) * (x k / (Complex.I * ((freq L k : ℂ)-z n)))‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (y_pos n).le]
  calc
    _ ≤ y n * ((z n).im⁻¹ * ‖x k‖) :=
      mul_le_mul_of_nonneg_left
        (norm_div_I_mul_le (x k) (freq L k) (z n) (z_pos n)) (y_pos n).le
    _ = ‖x k‖ := by rw [z_im, ← mul_assoc, mul_inv_cancel₀ (y_pos n).ne', one_mul]

lemma scaledR_coordinate_limit (L : ℝ) (x : Ell2) (k : ℤ) :
    Tendsto (fun n => scaledR L n x k) atTop (nhds (x k)) := by
  have hi : Tendsto (fun n => (y n)⁻¹) atTop (nhds (0 : ℝ)) := by
    simpa only [y, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (nhds 0))
  have hiC := Complex.continuous_ofReal.continuousAt.tendsto.comp hi
  have hden := (tendsto_const_nhds (x := (1 : ℂ))).add
    ((tendsto_const_nhds (x := Complex.I * (freq L k : ℂ))).mul hiC)
  have ht := (tendsto_const_nhds (x := x k)).div hden (by simp : (1 : ℂ) + Complex.I * ↑(freq L k) * ↑(0 : ℝ) ≠ 0)
  convert ht using 1
  · funext n
    simp [scaledR_apply, div_eq_mul_inv]
  · simp

/-- Strong convergence Y(Y+∂x)⁻¹→1 in every fixed Fourier Sobolev norm.
No regularity beyond membership of this complete space is required. -/
lemma scaledR_strong (L : ℝ) (x : Ell2) :
    Tendsto (fun n => scaledR L n x) atTop (nhds x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (G := ℝ)
    (f := fun (n : ℕ) k => ‖scaledR L n x k-x k‖^2) (g := fun _ => 0)
    (bound := fun k => 4 * ‖x k‖^2) ((summable_sq x).mul_left 4)
    (fun k => by simpa using ((scaledR_coordinate_limit L x k).sub (tendsto_const_nhds (x := x k))).norm.pow 2)
    (Eventually.of_forall fun n k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := (norm_sub_le (scaledR L n x k) (x k)).trans
        (add_le_add (scaledR_coordinate_bound L n x k) (le_refl _))
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
      nlinarith only [hsq])
  rw [tsum_zero] at ht
  have hs : Tendsto (fun n => ‖scaledR L n x-x‖^2) atTop (nhds (0 : ℝ)) := by
    convert ht using 1
    funext n
    rw [norm_sq_eq_tsum]
    rfl
  have ht' := hs.sqrt
  rw [Real.sqrt_zero] at ht'
  exact ht'.congr fun n => Real.sqrt_sq (norm_nonneg _)

/-- Strong convergence also holds for a convergent varying argument. -/
lemma scaledR_varying (L : ℝ) {f : ℕ → Ell2} {x : Ell2}
    (hf : Tendsto f atTop (nhds x)) :
    Tendsto (fun n => scaledR L n (f n)) atTop (nhds x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp hf)
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp (scaledR_strong L x)
  have ht := h1.add h2
  rw [add_zero] at ht
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) ht
  have he : scaledR L n (f n)-x =
      scaledR L n (f n-x)+(scaledR L n x-x) := by rw [map_sub]; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (scaledR_norm L n (f n-x)) (le_refl _))

open QuantumNLS.RiccatiPicardBall QuantumNLS.ComplexifiedSobolevField

def beta (u : Ell2) : ℝ := ‖u‖+1
lemma beta_pos (u : Ell2) : 0 < beta u := by unfold beta; positivity

def smallCondition (L a κ : ℝ) (u : Ell2) (n : ℕ) : Prop :=
  16 * |κ/L| * Cmul L a^2 * beta u^2 ≤ y n^2

lemma smallCondition_eventually (L a κ : ℝ) (u : Ell2) :
    ∀ᶠ n in atTop, smallCondition L a κ u n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (16 * |κ/L| * Cmul L a^2 * beta u^2 + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 1 ≤ y n := by unfold y; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hny : (n : ℝ) ≤ y n := by unfold y; linarith
  unfold smallCondition
  nlinarith [sq_nonneg (y n-1)]

lemma picard_exists {L a : ℝ} (hL : 0 < L) (ha : 1/2 < a) (κ : ℝ)
    (u : Ell2) (n : ℕ) (hc : smallCondition L a κ u n) :
    ∃ r : Ell2, ‖r‖ ≤ 2 * beta u / y n ∧
      riccatiT hL ha (z_pos n) (κ/L) u (jEll u) r = r ∧
      ∀ r' : Ell2, ‖r'‖ ≤ 4 * beta u / y n →
        riccatiT hL ha (z_pos n) (κ/L) u (jEll u) r' = r' → r' = r := by
  have hC : 16 * |κ/L| * Cmul L a^2 * beta u^2 ≤ (z n).im^2 := by
    simpa only [smallCondition, z_im] using hc
  have hu : ‖u‖ ≤ beta u := by unfold beta; linarith
  have hv : ‖jEll u‖ ≤ beta u := by rw [norm_jEll]; exact hu
  simpa only [z_im] using riccatiT_fixed_exists_unique hL ha (z_pos n)
    (κ/L) (beta u) (beta_pos u) hC u (jEll u) hu hv

/-- A specific small H^a solution, chosen from a proved contraction. Only a
finite prefix, irrelevant to the limit, is filled with zero. -/
def branch {L a : ℝ} (hL : 0 < L) (ha : 1/2 < a) (κ : ℝ) (u : Ell2) (n : ℕ) : Ell2 := by
  classical
  exact if hc : smallCondition L a κ u n then
    Classical.choose (picard_exists hL ha κ u n hc)
  else 0

lemma branch_eventually {L a : ℝ} (hL : 0 < L) (ha : 1/2 < a) (κ : ℝ) (u : Ell2) :
    ∀ᶠ n in atTop,
      ‖branch hL ha κ u n‖ ≤ 2 * beta u / y n ∧
      riccatiT hL ha (z_pos n) (κ/L) u (jEll u) (branch hL ha κ u n) =
        branch hL ha κ u n ∧
      ∀ r' : Ell2, ‖r'‖ ≤ 4 * beta u / y n →
        riccatiT hL ha (z_pos n) (κ/L) u (jEll u) r' = r' →
          r' = branch hL ha κ u n := by
  filter_upwards [smallCondition_eventually L a κ u] with n hn
  simp only [branch, dite_eq_left hn]
  exact Classical.choose_spec (picard_exists hL ha κ u n hn)

lemma fixedpoint_scaled_error {L a : ℝ} (hL : 0 < L) (ha : 1/2 < a)
    (κ : ℝ) (u r : Ell2) (n : ℕ)
    (hr : riccatiT hL ha (z_pos n) (κ/L) u (jEll u) r = r)
    (hn : ‖r‖ ≤ 2 * beta u / y n) :
    ‖(y n : ℂ) • r-scaledR L n u‖ ≤
      (4 * |κ/L| * Cmul L a^2 * ‖u‖ * beta u^2) * ((y n)⁻¹)^2 := by
  let w := mulBil hL ha (jEll u) (mulBil hL ha r r)
  have he0 : r-ropCLM L (z n) (z_pos n) u =
      -((κ/L : ℝ) : ℂ) • ropCLM L (z n) (z_pos n) w := by
    calc
      _ = riccatiT hL ha (z_pos n) (κ/L) u (jEll u) r -
          ropCLM L (z n) (z_pos n) u := by rw [hr]
      _ = _ := by simp only [riccatiT, neg_smul]; dsimp only [w]; abel
  have he : (y n : ℂ) • r-scaledR L n u = -((κ/L : ℝ) : ℂ) • scaledR L n w := by
    change (y n : ℂ) • r-(y n : ℂ) • ropCLM L (z n) (z_pos n) u =
      -((κ/L : ℝ) : ℂ) • ((y n : ℂ) • ropCLM L (z n) (z_pos n) w)
    rw [← smul_sub, he0, smul_smul, smul_smul, mul_comm]
  have hC : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hβ := beta_pos u
  have hy := y_pos n
  have hw : ‖w‖ ≤ Cmul L a * ‖u‖ * (Cmul L a * ‖r‖ * ‖r‖) := by
    have h1 := norm_mulBil_le hL ha (jEll u) (mulBil hL ha r r)
    rw [norm_jEll] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (norm_mulBil_le hL ha r r)
      (mul_nonneg hC (norm_nonneg u)))
  rw [he, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |κ/L| * ‖w‖ := mul_le_mul_of_nonneg_left (scaledR_norm L n w) (abs_nonneg _)
    _ ≤ |κ/L| * (Cmul L a * ‖u‖ * (Cmul L a * ‖r‖ * ‖r‖)) :=
      mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ ≤ |κ/L| * (Cmul L a * ‖u‖ *
        (Cmul L a * (2 * beta u / y n) * (2 * beta u / y n))) := by gcongr
    _ = _ := by ring

/-- The actual chosen small branch obeys Yr_Y→u in the Sobolev norm. -/
lemma branch_scaled_limit {L a : ℝ} (hL : 0 < L) (ha : 1/2 < a) (κ : ℝ) (u : Ell2) :
    Tendsto (fun n => (y n : ℂ) • branch hL ha κ u n) atTop (nhds u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hi : Tendsto (fun n => (y n)⁻¹) atTop (nhds (0 : ℝ)) := by
    simpa only [y, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (nhds 0))
  have ht := ((hi.pow 2).const_mul
    (4 * |κ/L| * Cmul L a^2 * ‖u‖ * beta u^2)).add
      (tendsto_iff_norm_sub_tendsto_zero.mp (scaledR_strong L u))
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ ht
  filter_upwards [branch_eventually hL ha κ u] with n hn
  have he : (y n : ℂ) • branch hL ha κ u n-u =
      ((y n : ℂ) • branch hL ha κ u n-scaledR L n u)+(scaledR L n u-u) := by abel
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add (fixedpoint_scaled_error hL ha κ u _ n hn.2.1 hn.1) (le_refl _))

/-- The nonlinear rescaled resolvent term converges in the same H^a norm.
All small-solution and varying-argument facts are proved above. -/
lemma nonlinear_scaled_limit {L a : ℝ} (hL : 0 < L) (ha : 1/2 < a) (κ : ℝ) (u : Ell2) :
    Tendsto (fun n => scaledR L n
      (mulBil hL ha (jEll u)
        (mulBil hL ha ((y n : ℂ) • branch hL ha κ u n)
          ((y n : ℂ) • branch hL ha κ u n)))) atTop
      (nhds (mulBil hL ha (jEll u) (mulBil hL ha u u))) := by
  have hc : Continuous (fun v : Ell2 => mulBil hL ha (jEll u) (mulBil hL ha v v)) :=
    (mulBil hL ha (jEll u)).continuous.comp
      ((mulBil hL ha).continuous.clm_apply continuous_id)
  exact scaledR_varying L (hc.continuousAt.tendsto.comp (branch_scaled_limit hL ha κ u))

#print axioms scaledR_strong
#print axioms scaledR_varying
#print axioms branch_eventually
#print axioms branch_scaled_limit
#print axioms nonlinear_scaled_limit
end QuantumNLS.RootEnergyMomentResolvent

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentResolvent." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentResolvent." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
