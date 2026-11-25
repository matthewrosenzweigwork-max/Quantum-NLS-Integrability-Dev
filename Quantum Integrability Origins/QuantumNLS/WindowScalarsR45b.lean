import QuantumNLS.WindowActualEstimatesR44b
import QuantumNLS.WindowRadialR45b

/-! Actual scalar functions in the accepted chart. Full-charge invariance
is obtained from the accepted vanishing scalar tails and literal contour
invariance, with no additional hierarchy or spectral-contract assumption. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter Topology
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowActualEstimatesR44b QuantumNLS.WindowScalarPullbackR44b
open QuantumNLS.WindowPhaseR44b QuantumNLS.Reg015Setting
open QuantumNLS.Q07GradientRemovalR24 QuantumNLS.Q07TailBindingR24
open QuantumNLS.Q07ChargeBoundsR24 QuantumNLS.Q07SobolevModelR24
open QuantumNLS.PROP017UniformN
namespace QuantumNLS.WindowScalarsR45b
variable {L κ : ℝ} [Fact (0 < L)]

def full (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) (z : h02 L (sequenceOrder d)) : ℝ :=
  realCharge (L := L) (sharp r) κ (r+1)
    (coordinates (regularity_pos r).le (inverseForCharge hκ C d r hr z))

def window (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (h : ℝ) (l : ℕ) (z : h02 L (sequenceOrder d)) : ℝ :=
  Q07IntegratedHessiansR16.windowContour hκ r (cutSeq L l) h
    (C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 z))

theorem full_contDiff (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) : ContDiff ℝ 1 (full hκ C d r hr) := by
  exact ((realCharge_contDiff (L := L) (sharp r) (by dsimp [order]; omega) κ (r+1)
    (by omega)).of_le (by norm_num)).comp
    (((coordinates (L := L) (regularity_pos r).le).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      (inverseForCharge_contDiff hκ C d r hr))

/-- The tail is exactly full minus window on the entire high-order space. -/
theorem tail_identity (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) (h : ℝ) (l : ℕ) (z : h02 L (sequenceOrder d)) :
    T (L := L) hκ r h l (inverseForCharge hκ C d r hr z) =
      full hκ C d r hr z-window hκ C d r h l z := by
  unfold T Q07TailBindingR24.tail full window Q07TailBindingR24.field
  rw [fieldMap_coordinates,inverseForCharge_val]

theorem window_rotation (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (h : ℝ) (l : ℕ) (α : ℤ → ℝ) (z : h02 L (sequenceOrder d)) :
    window hκ C d r h l (rotate α z) = window hκ C d r h l z :=
  WindowActionInvariantR44b.contour_rotation hκ C _ (sequenceOrder d).2 z α r _ _

theorem cutoff_tendsto : Tendsto (cutSeq L) atTop atTop := by
  unfold cutSeq
  exact Tendsto.atTop_div_const (Fact.out : 0 < L)
    (Tendsto.atTop_mul_const Real.pi_pos
      (tendsto_atTop_add_const_right _ 1
        (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop)))

/-- The accepted scalar value tails vanish at every finite Sobolev point. -/
theorem tail_tendsto (hκ : 0 < κ) (r : ℕ) {h : ℝ} (hh : 0 < h)
    (u : H02 L (regularity r)) : Tendsto (fun l => T (L := L) hκ r h l u) atTop (𝓝 0) := by
  let x := coordinates (L := L) (regularity_pos r).le u
  obtain ⟨K,H,hK,hH,l0,hb⟩ := Q07TailBindingR24.tail_data (L := L) hκ r ‖x‖ hh
  have hu : ∀ᶠ l : ℕ in atTop, |T (L := L) hκ r h l u| ≤ K/(cutSeq L l)^(r+2) := by
    filter_upwards [eventually_ge_atTop l0] with l hl
    exact (hb l hl).2.2 x (by linarith)
  have hlim : Tendsto (fun l : ℕ => K/(cutSeq L l)^(r+2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega : r+2 ≠ 0)).comp cutoff_tendsto)
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
    (squeeze_zero' (Eventually.of_forall fun l => abs_nonneg _) hu hlim)

/-- Full charge invariance is a consequence of the actual contour limits. -/
theorem full_rotation (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) (α : ℤ → ℝ) (z : h02 L (sequenceOrder d)) :
    full hκ C d r hr (rotate α z) = full hκ C d r hr z := by
  have ht₁ := tail_tendsto hκ r (h := 1) (by norm_num) (inverseForCharge hκ C d r hr (rotate α z))
  have ht₂ := tail_tendsto hκ r (h := 1) (by norm_num) (inverseForCharge hκ C d r hr z)
  have he : (fun l : ℕ => T (L := L) hκ r 1 l (inverseForCharge hκ C d r hr (rotate α z))-
      T (L := L) hκ r 1 l (inverseForCharge hκ C d r hr z)) =
      fun _ => full hκ C d r hr (rotate α z)-full hκ C d r hr z := by
    funext l
    rw [tail_identity,tail_identity,window_rotation]
    ring
  have ht := ht₁.sub ht₂
  rw [he,sub_self] at ht
  have hz : full hκ C d r hr (rotate α z)-full hκ C d r hr z = 0 :=
    tendsto_nhds_unique tendsto_const_nhds ht
  exact sub_eq_zero.mp hz

/-- Uniform actual differential estimate. Differentiability of the window
and its comparison with the full function are conclusions, not inputs. -/
theorem scalar_data (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) {h : ℝ} (hh : 0 < h)
    {K : Set (h02 L (sequenceOrder d))} (hK : IsCompact K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ z ∈ K,
      DifferentiableAt ℝ (window hκ C d r h l) z ∧
      ‖fderiv ℝ (full hκ C d r hr) z-fderiv ℝ (window hκ C d r h l) z‖ ≤
        A*(cutSeq L l)^(-(1/2 : ℝ)) := by
  obtain ⟨A,hA,l0,hb⟩ := compact_pullback hκ r hh (inverseForCharge hκ C d r hr)
    (inverseForCharge_contDiff hκ C d r hr) hK
  refine ⟨A,hA,l0,?_⟩
  intro l hl z hz
  obtain ⟨ht,hbound⟩ := hb l hl z hz
  have hF := ((full_contDiff hκ C d r hr).differentiable (by norm_num)) z
  have he : window hκ C d r h l = fun x => full hκ C d r hr x-
      T (L := L) hκ r h l (inverseForCharge hκ C d r hr x) := by
    funext x
    rw [tail_identity]
    ring
  have hG : DifferentiableAt ℝ (window hκ C d r h l) z := by
    rw [he]
    exact hF.sub ht
  refine ⟨hG,?_⟩
  have he' : (fun x => T (L := L) hκ r h l (inverseForCharge hκ C d r hr x)) =
      fun x => full hκ C d r hr x-window hκ C d r h l x := funext (tail_identity hκ C d r hr h l)
  rw [he',fderiv_fun_sub hF hG] at hbound
  exact hbound

end QuantumNLS.WindowScalarsR45b
#print axioms QuantumNLS.WindowScalarsR45b.full_rotation
#print axioms QuantumNLS.WindowScalarsR45b.scalar_data

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowScalarsR45b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowScalarsR45b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"R45b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
