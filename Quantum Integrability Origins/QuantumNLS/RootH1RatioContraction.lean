import QuantumNLS.RootH1RatioNonlinear

/-! Exact closed-ball contraction at the printed threshold. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioOperator
  QuantumNLS.RootH1RatioNonlinear
namespace QuantumNLS.RootH1RatioContraction
variable {L : ℝ} [Fact (0 < L)]

def scale (Y : ℝ) (u : L2T L) : ℝ := ‖u‖ / Real.sqrt Y

def radius (Y : ℝ) (u : L2T L) : ℝ := 2 * scale Y u

lemma scale_nonneg (Y : ℝ) (u : L2T L) : 0 ≤ scale Y u := by
  unfold scale
  positivity

lemma scale_sq {Y : ℝ} (hY : 0 < Y) (u : L2T L) :
    scale Y u ^ 2 = ‖u‖^2 / Y := by
  rw [scale, div_pow, Real.sq_sqrt hY.le]

lemma radius_printed {Y : ℝ} (hY : 0 < Y) (u : L2T L) :
    radius Y u = 2 * Real.sqrt (‖u‖^2/Y) := by
  rw [radius, ← scale_sq hY, Real.sqrt_sq (scale_nonneg Y u)]

lemma scale_small {Y κ : ℝ} (hY : 0 < Y) (u : L2T L)
    (hsmall : 16*κ*‖u‖^2 ≤ Y) : κ * scale Y u ^ 2 ≤ 1/16 := by
  rw [scale_sq hY]
  have he : κ * (‖u‖^2/Y) = (κ*‖u‖^2)/Y := by ring
  rw [he, div_le_iff₀ hY]
  linarith

lemma ball_small {Y κ : ℝ} (hY : 0 < Y) (hκ : 0 ≤ κ) (u : L2T L)
    (hsmall : 16*κ*‖u‖^2 ≤ Y) {r : Linfty L} (hr : ‖r‖ ≤ radius Y u) :
    κ*‖r‖^2 ≤ 1/4 := by
  have hb : ‖r‖^2 ≤ (2*scale Y u)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hm := mul_le_mul_of_nonneg_left hb hκ
  have hs := scale_small hY u hsmall
  nlinarith

lemma map_ball_bound {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y)
    {r : Linfty L} (hr : ‖r‖ ≤ radius Y u) :
    ‖ratioMap hY hlog κ u r‖ ≤ (5/4)*scale Y u := by
  have hs := ball_small hY hκ u hsmall hr
  calc
    _ ≤ (1+κ*‖r‖^2)*‖u‖/Real.sqrt Y := ratioMap_norm hY hlog hκ u r
    _ = (1+κ*‖r‖^2)*scale Y u := by unfold scale; ring
    _ ≤ (5/4)*scale Y u := mul_le_mul_of_nonneg_right (by linarith) (scale_nonneg Y u)

lemma map_ball {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y)
    {r : Linfty L} (hr : ‖r‖ ≤ radius Y u) :
    ‖ratioMap hY hlog κ u r‖ ≤ radius Y u := by
  exact (map_ball_bound hY hlog hκ u hsmall hr).trans (by
    unfold radius
    nlinarith [scale_nonneg Y u])

lemma map_contracts {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y)
    {r s : Linfty L} (hr : ‖r‖ ≤ radius Y u) (hs : ‖s‖ ≤ radius Y u) :
    ‖ratioMap hY hlog κ u r - ratioMap hY hlog κ u s‖ ≤ (1/4)*‖r-s‖ := by
  have hsum : ‖r‖+‖s‖ ≤ 4*scale Y u := by
    dsimp [radius] at hr hs
    linarith
  have hm := mul_le_mul_of_nonneg_left hsum (mul_nonneg hκ (scale_nonneg Y u))
  have hsc := scale_small hY u hsmall
  have hc : κ*(‖r‖+‖s‖)*‖u‖/Real.sqrt Y ≤ 1/4 := by
    have he : κ*(‖r‖+‖s‖)*‖u‖/Real.sqrt Y = κ*scale Y u*(‖r‖+‖s‖) := by
      unfold scale
      ring
    rw [he]
    nlinarith
  exact (ratioMap_sub_norm hY hlog hκ u r s).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

/-- Banach's theorem on the actual closed L∞ ball, including uniqueness in that ball. -/
theorem exists_unique_ratio {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) :
    ∃! r : Linfty L, ‖r‖ ≤ radius Y u ∧ ratioMap hY hlog κ u r = r := by
  let B := Metric.closedBall (0:Linfty L) (radius Y u)
  have hB : IsComplete B := Metric.isClosed_closedBall.isComplete
  have hb : ∀ r : Linfty L, r ∈ B ↔ ‖r‖ ≤ radius Y u := by
    intro r
    simp [B, Metric.mem_closedBall, dist_zero_right]
  have hmap : MapsTo (ratioMap hY hlog κ u) B B := by
    intro r hr
    exact (hb _).mpr (map_ball hY hlog hκ u hsmall ((hb _).mp hr))
  let f : B → B := hmap.restrict _ B B
  have hc : ContractingWith (1/4:ℝ≥0) f := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun r s => ?_⟩
    change dist (ratioMap hY hlog κ u r.val) (ratioMap hY hlog κ u s.val) ≤
      ((1/4:ℝ≥0):ℝ)*dist r.val s.val
    simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      map_contracts hY hlog hκ u hsmall ((hb _).mp r.property) ((hb _).mp s.property)
  let : CompleteSpace B := hB.completeSpace_coe
  let : Nonempty B := ⟨⟨0, (hb _).mpr (by simp [radius, scale_nonneg])⟩⟩
  let r := hc.fixedPoint f
  have hfix : ratioMap hY hlog κ u r.val = r.val :=
    congrArg Subtype.val hc.fixedPoint_isFixedPt
  refine ⟨r.val, ⟨(hb _).mp r.property, hfix⟩, ?_⟩
  intro s hs
  have hsfix : Function.IsFixedPt f ⟨s, (hb _).mpr hs.1⟩ := Subtype.ext hs.2
  exact congrArg Subtype.val (hc.fixedPoint_unique hsfix)

#print axioms scale_nonneg
#print axioms scale_sq
#print axioms radius_printed
#print axioms scale_small
#print axioms ball_small
#print axioms map_ball_bound
#print axioms map_ball
#print axioms map_contracts
#print axioms exists_unique_ratio
end QuantumNLS.RootH1RatioContraction

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioContraction." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioContraction." then
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
