import QuantumNLS.Def044ChartR26m
import QuantumNLS.HierarchyInputR25m

/-! The actual DEF-021 chart realizes the normalized R25m chart antecedent.
Its normalization follows from LOCAL-023 agreement and global compatibility.
The same Sobolev homeomorphisms witness both interfaces, including the inverse
restriction on the actual chart. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.Def044ChartR28m

open PhysicalTensor (L2T)
open REF88Chart (K chartInv chartInv_right)
open REF88PrintedChart (PrintedChart)
open GlobalCompatR47a (Extension)
open Reg015Setting (toBase toBase_apply)

variable {L κ : ℝ} [Fact (0 < L)]

private theorem extension (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) :
    Extension κ hκ (Def021ChartR41b.localChart L).d
      ((Def021ChartR41b.localChart L).Φ κ) ((Def021ChartR41b.localChart L).Ψ κ) C.Φ C.Ψ := by
  refine ⟨C.analytic, C.inverse_analytic, C.left_inverse, C.right_inverse, ?_,
    C.actions, C.local_agreement⟩
  refine ⟨⟨C.Ψ, C.left_inverse, C.right_inverse, fun z => (C.inverse_analytic z).differentiableAt⟩,
    fun u => (C.analytic u).differentiableAt, ?_, C.symplectic⟩
  intro u
  obtain ⟨e, h, _⟩ := C.differential u
  exact ⟨e, congrArg (fun A : L2T L →L[ℝ] K => (A : L2T L → K)) h.fderiv.symm⟩

/-- Every actual DEF-021 chart meets the full R25m chart normalization. -/
theorem printed_chart (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) :
    PrintedChart hκ C.Φ := by
  let lc := Def021ChartR41b.localChart L
  have h := extension hκ C
  refine ⟨h.strong, C.analytic, C.actions, ?_, h.real_normalization lc.positive lc.spec⟩
  intro v
  rw [h.fourier_derivative lc.positive lc.spec]
  rfl

/-- Normalization identifies any R25m printed chart and its inverse with
the same DEF-021 maps. -/
theorem printed_chart_maps (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (w : L2T L → K) (hw : PrintedChart hκ w) :
    w = C.Φ ∧ chartInv hw.symp = C.Ψ := by
  let lc := Def021ChartR41b.localChart L
  have he := (extension hκ C).unique lc.positive lc.spec
    w hw.symp hw.analytic hw.moduli hw.fourier hw.conj
  refine ⟨he, ?_⟩
  funext z
  have hz : C.Φ (chartInv hw.symp z) = z := he ▸ chartInv_right hw.symp z
  exact (C.left_inverse _).symm.trans (congrArg C.Ψ hz)

/-- The witnesses in the R26m restriction and R25m Sobolev antecedent
are interchangeable on the same chart. Pointwise equality identifies the
forward restriction, and the inverse identity then follows by bijectivity. -/
theorem sobolev_iff (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) :
    Def044ChartR51a.SobolevRestrictions hκ C ↔ HierarchyInputR25m.SobolevHomeomorphisms C.Φ := by
  constructor
  · intro h s hs
    obtain ⟨F, hF, _⟩ := h s hs
    refine ⟨F, fun u n => ?_⟩
    have hn := congrArg (fun z : K => z n) (hF u)
    simpa only [toBase_apply] using hn
  · intro h s hs
    obtain ⟨F, hF⟩ := h s hs
    have hmap (u : Sobolev.H02 L s) : toBase s hs (F u) = C.Φ u.val := by
      apply lp.ext
      funext n
      rw [toBase_apply]
      exact hF u n
    refine ⟨F, hmap, fun z => ?_⟩
    have hz := hmap (F.symm z)
    rw [F.apply_symm_apply] at hz
    exact (C.left_inverse _).symm.trans (congrArg C.Ψ hz.symm)

end QuantumNLS.Def044ChartR28m

#print axioms QuantumNLS.Def044ChartR28m.printed_chart
#print axioms QuantumNLS.Def044ChartR28m.printed_chart_maps
#print axioms QuantumNLS.Def044ChartR28m.sobolev_iff
