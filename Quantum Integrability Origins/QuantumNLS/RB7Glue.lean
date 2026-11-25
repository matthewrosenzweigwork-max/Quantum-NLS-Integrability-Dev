import Mathlib
import QuantumNLS.RB7Charge
import QuantumNLS.RB7Plumb
import QuantumNLS.RB7Invar

/-!
# R-7B122087 `thm:hierarchy`: `F_r = I_{r+1} ∘ Ψ` is `C²` and rotation invariant on `h^S` (assembly of A2, A4, `lem:loss`, with the accepted chart)

Printed: "The differential-polynomial recursion makes `I_{r+1}` a smooth real functional on `H^q`.  Lemma `lem:loss` shows that `(Z^new)^{-1} : h^s → H^q` is `C²`.  Thus `F_r = I_{r+1} ∘ (Z^new)^{-1}`
is `C²` on `h^s`. ... `F_r` is invariant under all coordinatewise rotations."

* `toH0 : L² →L[ℝ] H^0`: the `ℝ`-linear isometric identification `L² = H^0` (`u ↦ ⟨u, _⟩`).
* `Fr_contDiff`: with the accepted chart `ChartFacts` (`Ψ : ℓ² → L²` real analytic), `q > 0`, `3q < S`, `q ≤ S`, `g : h^S → H^S` continuous with `(g z).val = Ψ(z)` (the REG-015 Sobolev-homeomorphism
  restriction, EXPLICIT hypotheses) and `I : H^q → ℝ` `C²`, the map `x ↦ I(g x)` is `C²` on `h^S`: `lem:loss` (`LossSobolev.loss_analytic`) with `X' = h^S`, `X₀ = ℓ²` (`ι = ` coordinate inclusion), `f = toH0 ∘ Ψ`.
* `Fr_data` (assembled): for `r : ℕ`, `(r : ℝ) + 1 ≤ q`, `3q < S` (printed `q = r + 2`, `S = 3q + 1`), the first REG-015 clause (`Reg015Moments`, the named input) and `g` as above, there is `I : H^q → ℝ` which is `C²`,
  equals `Re I_{r+1}` (`ClassicalCharges.charge L κ f (r+1)`) on smooth periodic profiles in `H^q` (`RB7Charge`), such that `F = I ∘ emb ∘ g` is `C²` on `h^S` and invariant under every
  coordinatewise rotation of every `z ∈ h^S` (`RB7Invar.F_invariant`).  This is exactly the `SeqData`-input `RB7Scale.scaleData` needs (`F r`, `hF r`, `hinv r`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped ComplexConjugate NNReal Topology ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.LossSobolev
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.Fourier (MemHsLp)

variable {L κ : ℝ} [Fact (0 < L)]

theorem w0_eq_one (n : ℤ) : (def002 L ((0 : ℝ≥0) : ℝ)).w n = 1 := by
  simp [def002, QuantumNLS.Fourier.sobolevWeight]

/-- `L² = H⁰`: `v ↦ v` as an element of `H⁰` (the weight is `≡ 1`). -/
def toH0ₗ : L2T L →ₗ[ℂ] H02 L ((0 : ℝ≥0) : ℝ) where
  toFun v := WField.mk (W := def002 L ((0 : ℝ≥0) : ℝ)) v (by
    exact (summable_sq_of_lp (QuantumNLS.Fourier.fourierL2 L v)).congr (fun n => by rw [w0_eq_one, one_mul]))
  map_add' u v := WField.ext rfl
  map_smul' c v := WField.ext rfl

theorem toH0ₗ_val (v : L2T L) : (toH0ₗ v : H02 L ((0 : ℝ≥0) : ℝ)).val = v := rfl

/-- The continuous `ℝ`-linear identification `L² → H⁰`. -/
def toH0 : L2T L →L[ℝ] (fieldScale L).Y 0 :=
  (((toH0ₗ (L := L)).restrictScalars ℝ).mkContinuous 1 (fun v => by
    rw [one_mul]
    have h := WField.norm_val_eq (L := L) (W := def002 L ((0 : ℝ≥0) : ℝ)) w0_eq_one (toH0ₗ v)
    rw [toH0ₗ_val] at h
    exact h.symm.le) : L2T L →L[ℝ] H02 L ((0 : ℝ≥0) : ℝ))

theorem toH0_val (v : L2T L) : (toH0 v : H02 L ((0 : ℝ≥0) : ℝ)).val = v := rfl

/-- **`F = I ∘ g` is `C²` on `h^S`** (`lem:loss` through the accepted analytic chart). -/
theorem Fr_contDiff {hκ : 0 < κ} (C : ChartFacts (L := L) hκ) {q S : ℝ≥0} (hq : 0 < q)
    (hS : (2 + 1) * (q : ℝ) < S) (hqS : q ≤ S) (g : h02 L (S : ℝ) → H02 L (S : ℝ)) (hg : Continuous g)
    (hgC : ∀ z : h02 L (S : ℝ), (g z).val = C.Ψ (QuantumNLS.Reg015Setting.toBase (L := L) (S : ℝ) S.2 z))
    (I : (fieldScale L).Y q → ℝ) (hI : ContDiff ℝ 2 I) :
    ContDiff ℝ 2 (fun x : h02 L (S : ℝ) => I ((fieldScale L).emb S q hqS (g x))) := by
  have hf : AnalyticOnNhd ℝ (fun z : lp (fun _ : ℤ => ℂ) 2 => toH0 (C.Ψ z)) Set.univ :=
    fun z _ => ((toH0 (L := L)).analyticAt (C.Ψ z)).comp (C.ana_Ψ z)
  have h := (loss_analytic (fieldScale L)
    (((QuantumNLS.Reg015Setting.toBase (L := L) (S : ℝ) S.2).restrictScalars ℝ :
      h02 L (S : ℝ) →L[ℝ] lp (fun _ : ℤ => ℂ) 2)) (k := 2) (by norm_num) hq (by exact_mod_cast hS) hqS
    (fun z => toH0 (C.Ψ z)) hf g hg (fun x => WField.ext (by
      show (g x).val = _
      rw [hgC x]; rfl))).1
  exact hI.comp h

/-- **`F_r` data**: `I_{r+1}` as a `C²` functional on `H^q`, `F_r = I ∘ g` `C²` and coordinatewise rotation invariant on `h^S`. -/
theorem Fr_data (hκ : 0 < κ) (hreg : Reg015Moments (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {q S : ℝ≥0} (hq : (r : ℝ) + 1 ≤ q) (hS : (2 + 1) * (q : ℝ) < S) (hqS : q ≤ S)
    (g : h02 L (S : ℝ) → H02 L (S : ℝ)) (hg : Continuous g)
    (hgC : ∀ z : h02 L (S : ℝ), (g z).val = C.Ψ (QuantumNLS.Reg015Setting.toBase (L := L) (S : ℝ) S.2 z)) :
    ∃ I : (fieldScale L).Y q → ℝ, ContDiff ℝ 2 I ∧
      (∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (hm : MemHsLp L (q : ℝ) (smoothL2 hf)),
        I ⟨smoothL2 hf, hm⟩ = (charge L κ f (r + 1)).re) ∧
      ContDiff ℝ 2 (fun x : h02 L (S : ℝ) => I ((fieldScale L).emb S q hqS (g x))) ∧
      ∀ (u : ℤ → Circle) (z : h02 L (S : ℝ)),
        I ((fieldScale L).emb S q hqS (g (rot u z))) = I ((fieldScale L).emb S q hqS (g z)) := by
  have hq0 : 0 < q := by
    have : (0 : ℝ) < q := by linarith [Nat.cast_nonneg (α := ℝ) r]
    exact_mod_cast this
  obtain ⟨I, hI2, hIchar⟩ := chargeFun_scale (L := L) κ r hq
  refine ⟨I, hI2, hIchar, Fr_contDiff C hq0 hS hqS g hg hgC I hI2, ?_⟩
  intro u z
  exact F_invariant hκ C.toChartData hreg r hqS g hg hgC I (hI2.continuous) hIchar u z

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.toH0
#print axioms QuantumNLS.RB7.Fr_contDiff
#print axioms QuantumNLS.RB7.Fr_data
