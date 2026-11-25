import Mathlib
import QuantumNLS.RB7HJoint
import QuantumNLS.RB7Smooth
import QuantumNLS.LossSobolev
import QuantumNLS.Reg015Assembly

/-!
# R-7B122087 `thm:hierarchy`, sub-obligations A7b(c) and A7b(a)-curve (RB7H, haiku_inventory)

* `hinf_of_smooth` (A7b(c)): a smooth periodic `f` has `Φ(f) ∈ h^s` for every real `s ≥ 0`, where `Φ = e` is the exact-moduli chart of the
  REG-015 homeomorphism clause.  Proof: `memHs_of_smooth` (RB7Smooth) gives `smoothL2 f ∈ H^s`, the REG-015 input (`Reg015Assembly.REG015Input`, as a
  hypothesis in its exact form through its three named inputs) gives the homeomorphism `H^s ≃ Target V s` with coordinates `e`.
* `curve_lift` (A7b(a), curve form, printed "`lem:loss` with a sufficiently large input order"): if `z : ℝ → h^0` is the restriction of a `C^∞`
  curve into every `h^S` (`hz`), and the restriction `Ψ|_{h^S} : h^S → H^S` is continuous at every level (`hreg`, REG-015 homeomorphism
  clause) with `Ψ : h^0 → L²` real analytic (`hPsi`), then `τ ↦ Ψ(z τ)` is a `C^∞` curve in every `H^q`, `q > 0`.  Proof: the accepted
  `LossSobolev.loss_h_to_H` at `k = m+1` and level `S_m = (m+2) q + 1`, composed with `zS_m`; the levels agree since `H^q → L²` is injective.

No held contract is imported.  Named inputs: `hPsi`, `hz`, `hreg` (curve_lift) and the three REG-015 inputs (hinf_of_smooth).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology ContDiff NNReal
open MeasureTheory Filter Set

namespace QuantumNLS.RB7H

open QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.PhysicalTensor QuantumNLS.ClassicalCharges
open QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.RB7 QuantumNLS.LossSobolev QuantumNLS.Loss
open QuantumNLS.Reg015Setting

variable {L : ℝ} [Fact (0 < L)]

/-! ## A7b(c): smooth data lie in `h^∞` (REG-015 homeomorphism clause) -/

/-- **A7b(c).** For the exact-moduli chart `e` of REG-015 (named inputs `reg010`, `reg011`, `reg013` of `REG015Input`), every smooth periodic
`f` satisfies `Φ(f) := e (smoothL2 f) ∈ h^s` for every real `s ≥ 0`, with coordinates `(e (smoothL2 f)).val n`. -/
theorem hinf_of_smooth {κ : ℝ} (hκ : 0 < κ)
    (reg010 : Reg010LowOrdersInput (L := L) hκ) (reg011 : Reg011HomeomorphismInput (L := L) hκ)
    (reg013 : Reg013InductionInput (L := L) hκ)
    {V : Set Seq} (e : L2T L ≃ₜ V) (hE : ExactModuli e hκ)
    {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (s : ℝ) (hs0 : 0 ≤ s) :
    MemHs L s (fun n => (e (smoothL2 hf)).val n) := by
  obtain ⟨F, hF⟩ := (QuantumNLS.Reg015Assembly.REG015Input hκ reg010 reg011 reg013 s hs0).2.2 V e hE
  let v : H02 L s := WField.mk (smoothL2 hf) (memHs_of_smooth hf s)
  have hv : v.val = smoothL2 hf := rfl
  have key : (fun n => (e (smoothL2 hf)).val n) = (F v).val.val := by
    funext n
    rw [hF v n, hv]
  rw [key]
  exact h02_mem L s (F v).val

/-! ## A7b(a)-curve: `τ ↦ Ψ(z τ)` is `C^∞` into every `H^q` -/

/-- The `L²`-value of a DEF-002 inclusion `H^S ↪ H^T` (`T ≤ S`) is that of the element. -/
theorem emb_val {S T : ℝ≥0} (hT : T ≤ S) (w : (fieldScale L).Y S) :
    ((fieldScale L).emb S T hT w).val = w.val :=
  fieldIncl_val (def002 L (T : ℝ)) (def002 L (S : ℝ)) zero_le_one
    (def002_le_of_le L (by exact_mod_cast hT : ((T : ℝ≥0) : ℝ) ≤ (S : ℝ))) w

/-- One level of `lem:loss` (accepted `LossSobolev.loss_h_to_H`) composed with a `C^∞` sequence curve. -/
theorem level_smooth (Psi : (seqScale L).Y 0 → (fieldScale L).Y 0) (hPsi : AnalyticOnNhd ℝ Psi univ)
    {k : ℕ} (hk : 1 ≤ k) {q S : ℝ≥0} (hq : 0 < q) (hS : ((k : ℝ) + 1) * (q : ℝ) < (S : ℝ))
    (hqS : q ≤ S)
    (g : (seqScale L).Y S → (fieldScale L).Y S) (hg : Continuous g)
    (hres : ∀ x, (fieldScale L).emb S 0 (nn_zero_le S) (g x) = Psi ((seqScale L).emb S 0 (nn_zero_le S) x))
    (zS : ℝ → (seqScale L).Y S) (hzS : ContDiff ℝ ∞ zS) :
    ContDiff ℝ ((k : ℕ) : ℕ∞ω) (fun τ => (fieldScale L).emb S q hqS (g (zS τ))) := by
  have hloss := (loss_h_to_H L hk hq hS hqS Psi hPsi g hg hres).1
  exact hloss.comp (hzS.of_le (by exact_mod_cast le_top))

/-- **A7b(a), curve form.** `Ψ : h^0 → L²` analytic, `z` the restriction of `C^∞` curves `zS` in every `h^S` (`hz`), and `Ψ|_{h^S} : h^S → H^S`
continuous with the chart identity (`hreg`). Then for every `q > 0` there is a `C^∞` curve `V : ℝ → H^q` with `V τ = Ψ(z τ)` as `L²` classes. -/
theorem curve_lift (Psi : (seqScale L).Y 0 → (fieldScale L).Y 0) (hPsi : AnalyticOnNhd ℝ Psi univ)
    (z : ℝ → (seqScale L).Y 0)
    (hz : ∀ S : ℝ≥0, ∃ zS : ℝ → (seqScale L).Y S, ContDiff ℝ ∞ zS ∧
      ∀ τ, (seqScale L).emb S 0 (nn_zero_le S) (zS τ) = z τ)
    (hreg : ∀ S : ℝ≥0, ∃ g : (seqScale L).Y S → (fieldScale L).Y S, Continuous g ∧
      ∀ x, (fieldScale L).emb S 0 (nn_zero_le S) (g x) = Psi ((seqScale L).emb S 0 (nn_zero_le S) x))
    (q : ℝ) (hq : 0 < q) :
    ∃ V : ℝ → H02 L q, ContDiff ℝ ∞ V ∧ ∀ τ, (V τ).val = (Psi (z τ)).val := by
  choose g hg using hreg
  choose zS hzS using hz
  have hqpos : (0 : ℝ) < q := hq
  -- the DEF-002 level `S_m = (m+2) q + 1` for `C^{m+1}`
  have hSm : ∀ m : ℕ, ∃ S : ℝ≥0, (S : ℝ) = ((m : ℝ) + 2) * q + 1 := fun m =>
    ⟨⟨((m : ℝ) + 2) * q + 1, by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]⟩, rfl⟩
  choose SN hSN using hSm
  let qN : ℝ≥0 := ⟨q, hq.le⟩
  have hqN : (qN : ℝ) = q := rfl
  have hqNpos : 0 < qN := by
    rw [← NNReal.coe_pos, hqN]; exact hq
  have hS : ∀ m : ℕ, (((m + 1 : ℕ) : ℝ) + 1) * (qN : ℝ) < (SN m : ℝ) := by
    intro m
    rw [hSN m, hqN]
    push_cast
    nlinarith
  have hqS : ∀ m : ℕ, qN ≤ SN m := by
    intro m
    rw [← NNReal.coe_le_coe, hSN m, hqN]
    have : 0 ≤ (m : ℝ) * q := mul_nonneg (Nat.cast_nonneg m) hq.le
    nlinarith
  -- the `m`-th level curve
  let Wm : ℕ → ℝ → (fieldScale L).Y qN := fun m τ =>
    (fieldScale L).emb (SN m) qN (hqS m) (g (SN m) (zS (SN m) τ))
  have hval : ∀ (m : ℕ) (τ : ℝ), (Wm m τ).val = (Psi (z τ)).val := by
    intro m τ
    have h3 := congrArg (fun w : (fieldScale L).Y 0 => w.val)
      ((hg (SN m)).2 (zS (SN m) τ))
    rw [emb_val] at h3
    rw [emb_val]
    rw [h3, (hzS (SN m)).2 τ]
  have hWV : ∀ (m : ℕ) (τ : ℝ), Wm m τ = Wm 0 τ := fun m τ =>
    WField.ext ((hval m τ).trans (hval 0 τ).symm)
  have hsm : ∀ m : ℕ, ContDiff ℝ ((m + 1 : ℕ) : ℕ∞ω) (Wm m) :=
    fun m => level_smooth Psi hPsi (k := m + 1) (by omega) hqNpos (hS m) (hqS m) (g (SN m)) (hg (SN m)).1
      (hg (SN m)).2 (zS (SN m)) (hzS (SN m)).1
  refine ⟨Wm 0, ?_, fun τ => hval 0 τ⟩
  refine contDiff_infty.2 (fun n => ?_)
  have hfun : Wm 0 = Wm n := funext fun τ => (hWV n τ).symm
  rw [hfun]
  exact (hsm n).of_le (by exact_mod_cast Nat.le_succ n)

end QuantumNLS.RB7H

#print axioms QuantumNLS.RB7H.hinf_of_smooth
#print axioms QuantumNLS.RB7H.curve_lift
