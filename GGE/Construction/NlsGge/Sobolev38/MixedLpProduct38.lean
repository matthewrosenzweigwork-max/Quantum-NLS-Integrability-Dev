import NlsGge.Definitions.PilotInterfaces
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Tactic

/-! Batch 38 salvage of the owner's UNCOMPILED candidate `Orders.lean` and
`MixedLpProduct.lean` (NLS_GGE_Sobolev_UNCOMPILED_20261010T013139Z), renamed
with suffix 38 and compiled on current main. Generic Hölder product of finitely
many real-linear slot maps into `L^∞` (flag false) or `L²` (flag true), at most
two `L²` flags, on the actual period-one probability measure. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Function
open scoped ENNReal BigOperators

namespace NlsGge.Sobolev38
open NlsGge.Pilot


/-- Count marked slots by recursion, so the count reduces under a head/tail split. -/
def highCount38 : {q : ℕ} -> (Fin q -> Bool) -> ℕ
  | 0, _ => 0
  | q + 1, b => (if b 0 then 1 else 0) + highCount38 (fun i : Fin q => b i.succ)

theorem highCount_eq_sum38 {q : ℕ} (b : Fin q -> Bool) :
    highCount38 b = ∑ i, if b i then 1 else 0 := by
  induction q with
  | zero => simp [highCount38]
  | succ q ih => simp only [highCount38, Fin.sum_univ_succ, ih]

theorem highCount_tail_le38 {q : ℕ} (b : Fin (q + 1) -> Bool) :
    highCount38 (fun i : Fin q => b i.succ) ≤ highCount38 b := by
  change highCount38 (fun i : Fin q => b i.succ) ≤
    (if b 0 then 1 else 0) + highCount38 (fun i : Fin q => b i.succ)
  omega

/-- A positive top order and the total derivative bound allow at most two top slots. -/
theorem highCount_le_two_of_sum38 {q s : ℕ} (hs : 1 ≤ s)
    (a : Fin q -> ℕ) (htotal : (∑ i, a i) ≤ 2 * s) :
    highCount38 (fun i => decide (a i = s)) ≤ 2 := by
  classical
  have hmul : s * highCount38 (fun i => decide (a i = s)) ≤ ∑ i, a i := by
    rw [highCount_eq_sum38, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : a i = s
    · simp [hi]
    · simp [hi]
  have hprod : s * highCount38 (fun i => decide (a i = s)) ≤ 2 * s :=
    hmul.trans htotal
  nlinarith

/-- The source hypotheses at charge order j imply the analytic hypotheses at order m. -/
theorem source_orders_specialize38 {q j m : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ m) (hm : 2 ≤ m)
    (a : Fin q -> ℕ) (hcap : forall i, a i ≤ j - 1)
    (htotal : (∑ i, a i) ≤ 2 * j - 2) :
    (forall i, a i ≤ m - 1) ∧
      highCount38 (fun i => decide (a i = m - 1)) ≤ 2 := by
  constructor
  · intro i
    have hi := hcap i
    omega
  · apply highCount_le_two_of_sum38 (by omega) a
    omega

/-- The nontruncated homogeneity identity gives the indispensable independent degree cap. -/
theorem degree_cap_of_homogeneity38 {q j m : ℕ} (hjm : j ≤ m)
    (a : Fin q -> ℕ) (hhom : (∑ i, a i) + q = 2 * j + 2) :
    q ≤ 2 * m + 2 := by
  omega


open NlsGge.Pilot

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

def slotExponent38 (b : Bool) : ℝ≥0∞ := if b then 2 else ∞
def productExponent38 (t : ℕ) : ℝ≥0∞ := if t = 0 then ∞ else if t = 1 then 2 else 1
def complementaryExponent38 (t : ℕ) : ℝ≥0∞ := if t = 0 then 1 else if t = 1 then 2 else ∞

instance slotExponent_ge_one38 (b : Bool) : Fact (1 ≤ slotExponent38 b) := by
  constructor
  cases b <;> norm_num [slotExponent38]
instance productExponent_ge_one38 (t : ℕ) : Fact (1 ≤ productExponent38 t) := by
  constructor
  unfold productExponent38
  split_ifs <;> norm_num
instance complementaryExponent_ge_one38 (t : ℕ) : Fact (1 ≤ complementaryExponent38 t) := by
  constructor
  unfold complementaryExponent38
  split_ifs <;> norm_num

theorem product_holder_step38 (b : Bool) (t : ℕ) (h : (if b then 1 else 0) + t ≤ 2) :
    ENNReal.HolderTriple (slotExponent38 b) (productExponent38 t)
      (productExponent38 ((if b then 1 else 0) + t)) := by
  cases b with
  | false =>
    have ht : t ≤ 2 := by simpa using h
    interval_cases t <;> dsimp [slotExponent38, productExponent38] <;> infer_instance
  | true =>
    have ht : t ≤ 1 := by change 1 + t ≤ 2 at h; omega
    interval_cases t <;> dsimp [slotExponent38, productExponent38] <;> infer_instance

theorem product_holder_conjugate38 (t : ℕ) (ht : t ≤ 2) :
    ENNReal.HolderConjugate (productExponent38 t) (complementaryExponent38 t) := by
  interval_cases t <;> dsimp [productExponent38, complementaryExponent38] <;> infer_instance

/-- The constant one belongs to all three spaces, using the actual unit-volume measure. -/
def oneLp38 (p : ℝ≥0∞) [Fact (1 ≤ p)] : Lp ℂ p spatialMeasure :=
  ContinuousMap.toLp p spatialMeasure ℂ (1 : C(PhysicalCircle, ℂ))

theorem oneLp_ae38 (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (oneLp38 p : PhysicalCircle -> ℂ) =ᵐ[spatialMeasure] (fun _ => 1) :=
  ContinuousMap.coeFn_toLp spatialMeasure (1 : C(PhysicalCircle, ℂ))

theorem oneLp_norm_le38 (p : ℝ≥0∞) [Fact (1 ≤ p)] : ‖oneLp38 p‖ ≤ 1 := by
  have hbound : ∀ᵐ x ∂spatialMeasure, ‖oneLp38 p x‖ ≤ (1 : ℝ) := by
    filter_upwards [oneLp_ae38 p] with x hx
    simp [hx]
  have h := Lp.norm_le_of_ae_bound (f := oneLp38 p) (by norm_num : (0 : ℝ) ≤ 1) hbound
  have hmass : measureUnivNNReal spatialMeasure = 1 := by
    simp [measureUnivNNReal]
  simpa [hmass] using h

section MultilinearConstructors
set_option linter.unusedSectionVars false
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The zero-slot constant is multilinear; no nonempty-slot zero rule is misapplied. -/
def constantCML038 (z : F) : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) F where
  toFun _ := z
  map_update_add' := by intro _ u i; exact Fin.elim0 i
  map_update_smul' := by intro _ u i; exact Fin.elim0 i
  cont := continuous_const

def postcomposeCML38 {q : ℕ} (B : F →L[ℝ] G)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G where
  toFun u := B (L u)
  map_update_add' := by
    intro _ u i x y
    rw [L.map_update_add, B.map_add]
  map_update_smul' := by
    intro _ u i r x
    rw [L.map_update_smul, B.map_smul]
  cont := B.continuous.comp L.cont

private theorem tail_update_head38 {q : ℕ} [DecidableEq (Fin (q + 1))] (u : Fin (q + 1) -> E) (x : E) :
    (fun i : Fin q => Function.update u 0 x i.succ) = (fun i : Fin q => u i.succ) := by
  funext i
  simp

private theorem tail_update_succ38 {q : ℕ} [DecidableEq (Fin (q + 1))] [DecidableEq (Fin q)] (u : Fin (q + 1) -> E) (j : Fin q) (x : E) :
    (fun i : Fin q => Function.update u j.succ x i.succ) =
      Function.update (fun i : Fin q => u i.succ) j x := by
  funext i
  by_cases hij : i = j
  · subst i; simp
  · simp [Function.update, hij, Fin.succ_inj]

/-- One linear slot followed by a multilinear tail, combined by a bounded bilinear map. -/
def prependBilinear38 {q : ℕ} (B : F →L[ℝ] G →L[ℝ] H) (A : E →L[ℝ] F)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (q + 1) => E) H where
  toFun u := B (A (u 0)) (T (fun i => u i.succ))
  map_update_add' := by
    intro _ u i x y
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [map_add]
    · simp [tail_update_succ38, map_add,
        Function.update_of_ne (Fin.succ_ne_zero j).symm]
  map_update_smul' := by
    intro _ u i r x
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [map_smul]
    · simp [tail_update_succ38, map_smul,
        Function.update_of_ne (Fin.succ_ne_zero j).symm]
  cont := by fun_prop

end MultilinearConstructors

section Products
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual product of an arbitrary finite family with at most two L2 factors. -/
def mixedProduct38 : {q : ℕ} -> (b : Fin q -> Bool) -> (hc : highCount38 b ≤ 2) ->
    ((i : Fin q) -> E →L[ℝ] Lp ℂ (slotExponent38 (b i)) spatialMeasure) ->
    ContinuousMultilinearMap ℝ (fun _ : Fin q => E)
      (Lp ℂ (productExponent38 (highCount38 b)) spatialMeasure)
  | 0, _, _, _ => constantCML038 (oneLp38 ∞)
  | q + 1, b, hc, A => by
      let t := highCount38 (fun i : Fin q => b i.succ)
      letI : ENNReal.HolderTriple (slotExponent38 (b 0)) (productExponent38 t)
          (productExponent38 (highCount38 b)) := product_holder_step38 (b 0) t hc
      exact prependBilinear38
        ((ContinuousLinearMap.mul ℝ ℂ).holderL spatialMeasure
          (slotExponent38 (b 0)) (productExponent38 t) (productExponent38 (highCount38 b)))
        (A 0) (mixedProduct38 (fun i : Fin q => b i.succ)
          ((highCount_tail_le38 b).trans hc) (fun i => A i.succ))

/-- Quotient representatives are handled only through almost-everywhere identities. -/
theorem mixedProduct_ae38 : forall (q : ℕ) (b : Fin q -> Bool) (hc : highCount38 b ≤ 2)
    (A : (i : Fin q) -> E →L[ℝ] Lp ℂ (slotExponent38 (b i)) spatialMeasure)
    (u : Fin q -> E),
    (mixedProduct38 b hc A u : PhysicalCircle -> ℂ) =ᵐ[spatialMeasure]
      (fun x => ∏ i, A i (u i) x) := by
  intro q
  induction q with
  | zero =>
    intro b hc A u
    exact oneLp_ae38 ∞ |>.trans (by simp)
  | succ q ih =>
    intro b hc A u
    let t := highCount38 (fun i : Fin q => b i.succ)
    letI : ENNReal.HolderTriple (slotExponent38 (b 0)) (productExponent38 t)
        (productExponent38 (highCount38 b)) := product_holder_step38 (b 0) t hc
    have htail := ih (fun i : Fin q => b i.succ) ((highCount_tail_le38 b).trans hc)
      (fun i => A i.succ) (fun i => u i.succ)
    have hmul := (ContinuousLinearMap.mul ℝ ℂ).coeFn_holder
      (r := productExponent38 (highCount38 b)) (A 0 (u 0))
      (mixedProduct38 (fun i : Fin q => b i.succ) ((highCount_tail_le38 b).trans hc)
        (fun i => A i.succ) (fun i => u i.succ))
    filter_upwards [hmul, htail] with x hx ht
    change ((ContinuousLinearMap.mul ℝ ℂ).holder (productExponent38 (highCount38 b))
      (A 0 (u 0)) (mixedProduct38 (fun i : Fin q => b i.succ)
        ((highCount_tail_le38 b).trans hc) (fun i => A i.succ) (fun i => u i.succ))) x = _
    rw [hx, Fin.prod_univ_succ, <- ht]
    rfl

end Products

/-- Every resulting product space embeds into integrable functions on the unit circle. -/
theorem productLp_integrable38 (t : ℕ) (ht : t ≤ 2)
    (f : Lp ℂ (productExponent38 t) spatialMeasure) : Integrable f spatialMeasure := by
  letI := product_holder_conjugate38 t ht
  have hm := (ContinuousLinearMap.mul ℝ ℂ).memLp_of_bilin 1
    (Lp.memLp f) (Lp.memLp (oneLp38 (complementaryExponent38 t)))
  have hi := memLp_one_iff_integrable.1 hm
  apply hi.congr
  filter_upwards [oneLp_ae38 (complementaryExponent38 t)] with x hx
  change f x * oneLp38 (complementaryExponent38 t) x = f x
  rw [hx, mul_one]

/-- Integration is constructed using the conjugate exponent and the constant one. -/
def integrateProductLp38 (t : ℕ) (ht : t ≤ 2) :
    Lp ℂ (productExponent38 t) spatialMeasure →L[ℝ] ℂ := by
  letI := product_holder_conjugate38 t ht
  exact ((ContinuousLinearMap.mul ℝ ℂ).lpPairing spatialMeasure
    (productExponent38 t) (complementaryExponent38 t)).flip (oneLp38 (complementaryExponent38 t))

theorem integrateProductLp_eq_integral38 (t : ℕ) (ht : t ≤ 2)
    (f : Lp ℂ (productExponent38 t) spatialMeasure) :
    integrateProductLp38 t ht f = ∫ x, f x ∂spatialMeasure := by
  letI := product_holder_conjugate38 t ht
  change (ContinuousLinearMap.mul ℝ ℂ).lpPairing spatialMeasure
    (productExponent38 t) (complementaryExponent38 t) f (oneLp38 (complementaryExponent38 t)) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [oneLp_ae38 (complementaryExponent38 t)] with x hx
  change f x * oneLp38 (complementaryExponent38 t) x = f x
  rw [hx, mul_one]

theorem mixedProduct_integrable38 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} (b : Fin q -> Bool) (hc : highCount38 b ≤ 2)
    (A : (i : Fin q) -> E →L[ℝ] Lp ℂ (slotExponent38 (b i)) spatialMeasure)
    (u : Fin q -> E) : Integrable (fun x => ∏ i, A i (u i) x) spatialMeasure :=
  (productLp_integrable38 (highCount38 b) hc (mixedProduct38 b hc A u)).congr
    (mixedProduct_ae38 q b hc A u)

end NlsGge.Sobolev38
