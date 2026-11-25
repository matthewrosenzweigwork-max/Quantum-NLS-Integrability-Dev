import QuantumNLS.RootH1RatioOperator

/-! The actual L∞ nonlinear map for R-D24009D4. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioOperator
namespace QuantumNLS.RootH1RatioNonlinear
variable {L : ℝ} [Fact (0 < L)]

lemma ae_norm_le (r : Linfty L) : ∀ᵐ x, ‖r x‖ ≤ ‖r‖ := by
  simpa only [lpNorm, ← Lp.norm_def] using ae_le_lpNorm_exponent_top (Lp.memLp r)

lemma cubic_mem (u : L2T L) (r : Linfty L) :
    MemLp (fun x => star (u x) * (r x)^2) 2 volume := by
  refine (Lp.memLp u).of_le_mul (c := ‖r‖^2) (f := fun x => star (u x) * (r x)^2)
    ((Lp.aestronglyMeasurable u).star.mul ((Lp.aestronglyMeasurable r).pow 2)) ?_
  filter_upwards [ae_norm_le r] with x hx
  simp only [norm_mul, norm_star, norm_pow]
  calc
    ‖u x‖ * ‖r x‖^2 ≤ ‖u x‖ * ‖r‖^2 := by gcongr
    _ = ‖r‖^2 * ‖u x‖ := by ring

def cubic (u : L2T L) (r : Linfty L) : L2T L :=
  (cubic_mem u r).toLp _

lemma coe_cubic (u : L2T L) (r : Linfty L) :
    cubic u r =ᵐ[volume] (fun x => star (u x) * (r x)^2) := MemLp.coeFn_toLp _

lemma cubic_norm (u : L2T L) (r : Linfty L) : ‖cubic u r‖ ≤ ‖r‖^2 * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coe_cubic u r, ae_norm_le r] with x hx hr
  rw [hx, norm_mul, norm_star, norm_pow]
  calc
    ‖u x‖ * ‖r x‖^2 ≤ ‖u x‖ * ‖r‖^2 := by gcongr
    _ = _ := by ring

lemma cubic_sub_norm (u : L2T L) (r s : Linfty L) :
    ‖cubic u r - cubic u s‖ ≤ (‖r‖ + ‖s‖) * ‖r-s‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coe_cubic u r, coe_cubic u s, Lp.coeFn_sub (cubic u r) (cubic u s),
    Lp.coeFn_sub r s, ae_norm_le r, ae_norm_le s, ae_norm_le (r-s)]
    with x hr hs hsub hrs hnr hns hnd
  rw [hsub, Pi.sub_apply, hr, hs, ← mul_sub]
  have he : (r x)^2 - (s x)^2 = (r x + s x)*(r x-s x) := by ring
  rw [he, norm_mul, norm_star, norm_mul]
  have had : ‖r x + s x‖ ≤ ‖r‖ + ‖s‖ := (norm_add_le _ _).trans (add_le_add hnr hns)
  rw [hrs, Pi.sub_apply] at hnd
  calc
    ‖u x‖ * (‖r x+s x‖*‖r x-s x‖) ≤ ‖u x‖ * ((‖r‖+‖s‖)*‖r-s‖) := by gcongr
    _ = _ := by ring

lemma infinityResolvent_sub {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (f g : L2T L) :
    infinityResolvent hY hlog f - infinityResolvent hY hlog g =
      infinityResolvent hY hlog (f-g) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (infinityResolvent hY hlog f) (infinityResolvent hY hlog g),
    coe_infinityResolvent hY hlog f, coe_infinityResolvent hY hlog g,
    coe_infinityResolvent hY hlog (f-g),
    Lp.coeFn_sub (resolvent Y f) (resolvent Y g)] with x hx hf hg hfg hs
  rw [hx, Pi.sub_apply, hf, hg, hfg]
  have he : resolvent Y (f-g) = resolvent Y f - resolvent Y g := map_sub _ _ _
  rw [he, hs, Pi.sub_apply]

lemma infinityResolvent_sub_norm {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (f g : L2T L) :
    ‖infinityResolvent hY hlog f - infinityResolvent hY hlog g‖ ≤ ‖f-g‖/Real.sqrt Y := by
  rw [infinityResolvent_sub]
  exact infinityResolvent_norm hY hlog _

def forcing (κ : ℝ) (u : L2T L) (r : Linfty L) : L2T L :=
  u - (κ:ℂ) • cubic u r

def ratioMap {Y : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (κ : ℝ) (u : L2T L) (r : Linfty L) : Linfty L :=
  infinityResolvent hY hlog (forcing κ u r)

lemma forcing_norm {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (r : Linfty L) :
    ‖forcing κ u r‖ ≤ (1+κ*‖r‖^2)*‖u‖ := by
  calc
    _ ≤ ‖u‖ + ‖(κ:ℂ) • cubic u r‖ := norm_sub_le _ _
    _ = ‖u‖ + κ*‖cubic u r‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hκ]
    _ ≤ ‖u‖ + κ*(‖r‖^2*‖u‖) := by gcongr; exact cubic_norm u r
    _ = _ := by ring

lemma ratioMap_norm {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (r : Linfty L) :
    ‖ratioMap hY hlog κ u r‖ ≤ (1+κ*‖r‖^2)*‖u‖/Real.sqrt Y :=
  (infinityResolvent_norm hY hlog _).trans
    (div_le_div_of_nonneg_right (forcing_norm hκ u r) (Real.sqrt_nonneg Y))

lemma ratioMap_sub_norm {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (r s : Linfty L) :
    ‖ratioMap hY hlog κ u r - ratioMap hY hlog κ u s‖ ≤
      (κ*(‖r‖+‖s‖)*‖u‖/Real.sqrt Y)*‖r-s‖ := by
  have he : forcing κ u r - forcing κ u s = -(κ:ℂ) • (cubic u r-cubic u s) := by
    unfold forcing
    module
  calc
    _ ≤ ‖forcing κ u r - forcing κ u s‖ / Real.sqrt Y := infinityResolvent_sub_norm hY hlog _ _
    _ = κ*‖cubic u r-cubic u s‖ / Real.sqrt Y := by
      rw [he, norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hκ]
    _ ≤ κ*((‖r‖+‖s‖)*‖r-s‖*‖u‖)/Real.sqrt Y := by
      gcongr
      exact cubic_sub_norm u r s
    _ = _ := by ring

#print axioms ae_norm_le
#print axioms cubic_mem
#print axioms coe_cubic
#print axioms cubic_norm
#print axioms cubic_sub_norm
#print axioms infinityResolvent_sub
#print axioms infinityResolvent_sub_norm
#print axioms forcing_norm
#print axioms ratioMap_norm
#print axioms ratioMap_sub_norm
end QuantumNLS.RootH1RatioNonlinear

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioNonlinear." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioNonlinear." then
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
