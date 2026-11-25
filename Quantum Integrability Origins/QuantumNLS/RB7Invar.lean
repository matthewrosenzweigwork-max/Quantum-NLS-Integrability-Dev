import Mathlib
import QuantumNLS.RB7Moment
import QuantumNLS.RB7Scale
import QuantumNLS.Reg015Setting

/-!
# R-7B122087 `thm:hierarchy`: rotation invariance of `F_r = I_{r+1} ∘ Ψ` on all of `h^S` (own TODO A4, assembled)

Printed: "For rapidly decreasing coordinates, the scalar moment and uniqueness identities show that `F_r` is invariant under all coordinatewise rotations.  Density and
continuity extend invariance to `h^s`."

`F_invariant`: with the chart data (`RB7Moment.ChartData`), the REG-015 moment clause (NAMED INPUT `Reg015Moments`, supplied by `RB7Bridge.reg015Moments_of_REG015Input`),
`g : h^S → H^S` the continuous restriction of `Ψ`, and `I : H^q → ℝ` continuous with `I(f) = Re I_{r+1}(f)` on smooth periodic `f`, the functional `I ∘ emb ∘ g` is invariant under
every coordinatewise rotation of every `z ∈ h^S`.  This discharges the hypothesis `hfin` of `RB7Scale.inv_of_chart` (finite support ⊆ rapidly decreasing); the only analytic content
beyond REG-015 is `RB7Smooth.smooth_of_memHs`, accepted `R_275B7656` and accepted `root_scalar_uniqueness`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate NNReal
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.LossSobolev
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.Fourier (MemHsLp)

variable {L κ : ℝ} [Fact (0 < L)]

theorem F_invariant (hκ : 0 < κ) (C : ChartData (L := L) hκ) (hreg : Reg015Moments (L := L) hκ) (j : ℕ)
    {q S : ℝ≥0} (hqS : q ≤ S) (g : h02 L (S : ℝ) → H02 L (S : ℝ)) (hg : Continuous g)
    (hgC : ∀ z : h02 L (S : ℝ), (g z).val = C.Ψ (QuantumNLS.Reg015Setting.toBase (L := L) (S : ℝ) S.2 z))
    (I : (fieldScale L).Y q → ℝ) (hI : Continuous I)
    (hIchar : ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (hm : MemHsLp L (q : ℝ) (smoothL2 hf)),
      I ⟨smoothL2 hf, hm⟩ = (charge L κ f (j + 1)).re)
    (u : ℤ → Circle) (z : h02 L (S : ℝ)) :
    I ((fieldScale L).emb S q hqS (g (rot u z))) = I ((fieldScale L).emb S q hqS (g z)) := by
  classical
  -- `I` as a function on `L²`
  let I' : L2T L → ℝ := fun x => if h : MemHsLp L (q : ℝ) x then I ⟨x, h⟩ else 0
  have hI' : ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f), I' (smoothL2 hf) = (charge L κ f (j + 1)).re := by
    intro f hf
    have hm := memHs_of_smooth hf (q : ℝ)
    simp only [I', dif_pos hm]
    exact hIchar f hf hm
  have hemb : ∀ w : H02 L (S : ℝ), I ((fieldScale L).emb S q hqS w) = I' w.val := by
    intro w
    have hm : MemHsLp L (q : ℝ) w.val := by
      have := ((fieldScale L).emb S q hqS w).property
      exact (QuantumNLS.Sobolev.mem_fieldSub_def002 (L := L) (s := (q : ℝ)) _).1 this
    simp only [I', dif_pos hm]
    congr 1
  refine inv_of_chart (L := L) hqS g hg I hI ?_ u z
  intro u' T z'
  rw [hemb, hemb, hgC, hgC]
  refine I_eq_of_moduli hκ C hreg j I' hI' _ _ ?_ ?_
  · intro s hs
    refine summable_of_ne_finset_zero (s := T) (fun n hn => ?_)
    have h1 := QuantumNLS.Reg015Setting.toBase_apply (L := L) (S : ℝ) S.2 (rot u' (trunc T z')) n
    have h2 : (rot u' (trunc T z')).val n = 0 := by simp [rot, hn]
    rw [h2] at h1
    rw [h1]; simp
  · intro n
    have h1 := QuantumNLS.Reg015Setting.toBase_apply (L := L) (S : ℝ) S.2 (rot u' (trunc T z')) n
    have h2 := QuantumNLS.Reg015Setting.toBase_apply (L := L) (S : ℝ) S.2 (trunc T z') n
    rw [h1, h2]
    by_cases hn : n ∈ T <;> simp [rot, hn]

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.F_invariant
