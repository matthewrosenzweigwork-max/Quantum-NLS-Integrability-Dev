import Mathlib
import QuantumNLS.RB7Reg
import QuantumNLS.RB7Main
import QuantumNLS.RB7HJoint

/-!
# R-7B122087 `thm:hierarchy`: the sequence-level flow of order `r`, independent of the level `a` (RB7Zf)

For the chart data of `RB7Reg` (`F_r = Fd hR C r` on `h^{S_r}`, `S_r = SOf r`):

* `sdata r a`: `SeqData (def002 L a) Unit` (`RB7Scale.scaleData` with the single functional `F_r`), `a ≥ S_r`; `zflow r a τ z = flow (τ·1) z` on `h^a`.
* `zflow_val_eq`: the flows at different levels `a, a'` of the same sequence agree as sequences (their frequencies `freq F_r (z viewed in h^{S_r})` only see the common `h^{S_r}` class).
* `Zf r τ z` (`z ∈ h^0`): the flow at level `S_r` followed by inclusion to `h^0` when `z ∈ h^{S_r}`, `z` otherwise.  `Zf_zero`, `Zf_val`.
* `zflow_contDiff`: for rapidly decreasing `z`, `τ ↦ zflow r a τ z` is `C^∞` into `h^a` (`RB7Scale.scale_flow_contDiff`).
* `zflow_hasDerivAt`: its derivative at level `S_r` has coordinates `-i ∇_j F_r` at the flowed point (`SeqData.flow_hasDerivAt`, `dcurve_one_val`), as an `ℓ²` curve.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped ComplexConjugate Topology NNReal ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.Reg015Setting QuantumNLS.LossSobolev

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

/-- The one-order sequence data at level `a ≥ S_r`. -/
def sdata (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) (a : ℝ)
    (ha : ((SOf r : ℝ≥0) : ℝ) ≤ a) : SeqData (def002 L a) Unit :=
  scaleData L (fun _ : Unit => ((SOf r : ℝ≥0) : ℝ)) a (fun _ => ha) (fun _ => Fd hR C r)
    (fun _ => Fd_contDiff hR C r) (fun _ => Fd_inv hR C r)

/-- The unit time direction. -/
def one1 : Unit → ℝ := fun _ => 1

/-- The order-`r` flow at time `τ` on `h^a`. -/
def zflow (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) (a : ℝ)
    (ha : ((SOf r : ℝ≥0) : ℝ) ≤ a) (τ : ℝ) (z : h02 L a) : h02 L a :=
  flow (sdata hR C r a ha).D (τ • one1) z

theorem zflow_val_eq (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) {a a' : ℝ}
    (ha : ((SOf r : ℝ≥0) : ℝ) ≤ a) (ha' : ((SOf r : ℝ≥0) : ℝ) ≤ a') (τ : ℝ) (z : h02 L a) (z' : h02 L a')
    (h : z.val = z'.val) : (zflow hR C r a ha τ z).val = (zflow hR C r a' ha' τ z').val := by
  have hd : ∀ j, (sdata hR C r a ha).D.Ω () z j = (sdata hR C r a' ha').D.Ω () z' j := by
    intro j
    show freq (Fd hR C r) ((sdata hR C r a ha).down () z) j =
      freq (Fd hR C r) ((sdata hR C r a' ha').down () z') j
    have : (sdata hR C r a ha).down () z = (sdata hR C r a' ha').down () z' := WSeq.ext h
    rw [this]
  funext j
  unfold zflow
  rw [flow_val, flow_val, h]
  simp only [angle, Pi.smul_apply, smul_eq_mul, one1, mul_one, Finset.univ_unique, Finset.sum_singleton, hd j]

theorem zflow_zero (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) (a : ℝ)
    (ha : ((SOf r : ℝ≥0) : ℝ) ≤ a) (z : h02 L a) : zflow hR C r a ha 0 z = z := by
  unfold zflow
  rw [zero_smul]
  exact flow_zero _ z

open Classical in
/-- The order-`r` sequence flow on `h^0` (the flow at level `S_r` when `z ∈ h^{S_r}`, the identity otherwise). -/
def Zf (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) (τ : ℝ)
    (z : h02 L (((0 : ℝ≥0) : ℝ))) : h02 L (((0 : ℝ≥0) : ℝ)) :=
  if hz : MemHs L ((SOf r : ℝ≥0) : ℝ) z.val then
    h02_mono L (show ((0 : ℝ≥0) : ℝ) ≤ ((SOf r : ℝ≥0) : ℝ) from NNReal.coe_nonneg (SOf r))
      (zflow hR C r _ le_rfl τ (h02.ofMem hz))
  else z

theorem Zf_zero (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    (z : h02 L (((0 : ℝ≥0) : ℝ))) : Zf hR C r 0 z = z := by
  unfold Zf
  split_ifs with hz
  · rw [zflow_zero]
    exact WSeq.ext rfl
  · rfl

theorem Zf_val (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) (τ : ℝ)
    (z : h02 L (((0 : ℝ≥0) : ℝ))) {a : ℝ} (ha : ((SOf r : ℝ≥0) : ℝ) ≤ a) (za : h02 L a) (hza : za.val = z.val) :
    (Zf hR C r τ z).val = (zflow hR C r a ha τ za).val := by
  have hz : MemHs L ((SOf r : ℝ≥0) : ℝ) z.val := by
    rw [← hza]
    exact RB7H.memHs_of_le ha _ za.summable
  unfold Zf
  rw [dif_pos hz]
  exact (zflow_val_eq hR C r le_rfl ha τ (h02.ofMem hz) za hza.symm)

/-- Rapidly decreasing data: `C^∞` in time at every level. -/
theorem zflow_contDiff (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) (a : ℝ)
    (ha : ((SOf r : ℝ≥0) : ℝ) ≤ a) (z : h02 L a) (hz : Hinf L z.val) :
    ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => zflow hR C r a ha τ z) :=
  scale_flow_contDiff L (fun _ : Unit => ((SOf r : ℝ≥0) : ℝ)) (fun _ => NNReal.coe_nonneg _) a (fun _ => ha)
    (fun _ => Fd hR C r) (fun _ => Fd_contDiff hR C r) (fun _ => Fd_inv hR C r) one1 z hz

/-- The `ℓ²`-curve of the flow and its derivative (at level `S_r`). -/
theorem zflow_hasDerivAt (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    (z : h02 L ((SOf r : ℝ≥0) : ℝ)) (hz : Hinf L z.val) (τ : ℝ) :
    ∃ d : lp (fun _ : ℤ => ℂ) 2,
      HasDerivAt (fun t : ℝ => toBase (L := L) ((SOf r : ℝ≥0) : ℝ) (SOf r).2 (zflow hR C r _ le_rfl t z)) d τ ∧
      ∀ j : ℤ, (d : ℤ → ℂ) j = -Complex.I *
        grad (fderiv ℝ (Fd hR C r) (zflow hR C r _ le_rfl τ z)) j := by
  set S := sdata hR C r ((SOf r : ℝ≥0) : ℝ) le_rfl with hS
  have hzP := hzP_of_Hinf L (fun _ : Unit => ((SOf r : ℝ≥0) : ℝ)) (fun _ => NNReal.coe_nonneg _)
    ((SOf r : ℝ≥0) : ℝ) z.val hz
  have h1 := S.flow_hasDerivAt one1 z hzP τ
  let T : h02 L ((SOf r : ℝ≥0) : ℝ) →L[ℝ] lp (fun _ : ℤ => ℂ) 2 :=
    ((toBase (L := L) ((SOf r : ℝ≥0) : ℝ) (SOf r).2).restrictScalars ℝ)
  have h2 := T.hasFDerivAt.comp_hasDerivAt τ h1
  refine ⟨T (dcurve (S.hz_of one1 z hzP) 1 τ), h2, fun j => ?_⟩
  show (toBase (L := L) ((SOf r : ℝ≥0) : ℝ) (SOf r).2 (dcurve (S.hz_of one1 z hzP) 1 τ) : ℤ → ℂ) j = _
  refine (toBase_apply (L := L) ((SOf r : ℝ≥0) : ℝ) (SOf r).2 _ j).trans ?_
  rw [S.dcurve_one_val one1 z (S.hz_of one1 z hzP) τ j]
  simp only [one1, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one, one_mul]
  rfl

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.zflow_val_eq
#print axioms QuantumNLS.RB7.Zf_val
#print axioms QuantumNLS.RB7.zflow_contDiff
#print axioms QuantumNLS.RB7.zflow_hasDerivAt
