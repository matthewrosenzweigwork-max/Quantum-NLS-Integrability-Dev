import Mathlib
import QuantumNLS.Ext025A4ProductDischarge
import QuantumNLS.RB01Main
import QuantumNLS.RootIndexedMassesFull
import QuantumNLS.RootMassPropernessR27
import QuantumNLS.RootMassInvolutionBatchR9
import QuantumNLS.GlobalIndividualPeriodsR31b

/-!
# R-F5355ABD `thm:global-actual-chart` (`actual_chart.tex:15`), stage 1: the actual quantum objects meet the product-torus hypotheses

Source: `source-text/chapters/global/actual_chart.tex`, proof (lines 76-173), paragraph "These inputs meet all hypotheses of Theorem `thm:global-product-torus`".

For fixed `L, κ > 0` the actual indexed masses `I^{(κ)} = (I_n^{(κ)})_n = Actions hκ : L²(𝕋_L) → ℓ¹(ℤ;ℝ)` (R-950BFB30, `RootIndexedMasses.masses`) are fed to the *accepted* product-torus theorem
`Ext025A4ProductDischarge.thm_global_product_torus_ext` (R-4C2E4AC7).  Its five printed hypotheses are discharged from accepted nodes, none is assumed:
* real analyticity into `ℓ¹` at every field: R-EC25334D `RB01Main.analyticAt_actions` (`hI`);
* `I_n ≥ 0` and `Σ I_n = ‖u‖²`: R-950BFB30 `RootIndexedMassesFull.root_indexed_masses` (`hpos`, `hmass`);
* properness (compact preimages of compact subsets of `ℓ¹_+`): R-0191D778 `RootMassPropernessR27.root_mass_properness` (`hprop`; `ℓ¹_+` carries the subspace topology of `ℓ¹`);
* involution `{I_n, I_j} = dI_n[X_{I_j}] = 0` with `X_{I_j} = W⁻¹ dI_j`: R-507DD869 `RootMassInvolutionR9.root_mass_involution` (`hinv`; `W⁻¹ ℓ = -(i/2)·Riesz(ℓ)` of the product-torus stage equals DEF-015's `hamField`, `Winv_fderiv`);
* the complete flow of each `I_n` has `2π` return: R-C95830E3 `GlobalIndividualPeriodsR31b.global_individual_periods` (`hper`; the flow of the product-torus stage is the unique solution of `u' = X_{I_n}(u)` and the accepted physical flow solves it with `X_{I_n} = -i ∇ I_n`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Filter Topology Metric

namespace QuantumNLS.RF535Bridge
open QuantumNLS.PhysicalTensor (L2T)
open _root_.HilbertL1Compact (L1)

variable {L κ : ℝ} [Fact (0 < L)]

abbrev Iact (hκ : 0 < κ) : L2T L → L1 ℝ := TerraMultiRound30HessianBridge.Actions hκ

theorem hI (hκ : 0 < κ) : AnalyticOnNhd ℝ (Iact (L := L) hκ) univ :=
  fun u _ => RB01Main.analyticAt_actions hκ u

theorem hpos (hκ : 0 < κ) : QuantumNLS.ProductTorusContinuity.Nonneg (Iact (L := L) hκ) :=
  fun u n => (RootIndexedMasses.masses hκ u).2 n

theorem hmass (hκ : 0 < κ) (u : L2T L) :
    ∑' n, ((Iact (L := L) hκ u : L1 ℝ) : ℤ → ℝ) n = ‖u‖ ^ 2 :=
  (RootIndexedMassesFull.root_indexed_masses hκ u).2.2.2.1

theorem hprop (hκ : 0 < κ) : QuantumNLS.ProductTorusContinuity.Proper (Iact (L := L) hκ) := by
  intro K hK hKnn
  have hP := (RootMassPropernessR27.root_mass_properness (L := L) hκ).2.2.1
  have hind : Topology.IsInducing (Subtype.val : ActionTorus.PosL1 → L1 ℝ) :=
    Topology.IsInducing.subtypeVal
  have hK' : IsCompact ((Subtype.val : ActionTorus.PosL1 → L1 ℝ) ⁻¹' K) := by
    rw [hind.isCompact_iff, Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hKnn x hx⟩, rfl⟩)]
    exact hK
  exact hP _ hK'

theorem continuous_toCircle : Continuous (Real.Angle.toCircle) := by
  have : (Real.Angle.toCircle) = (AddCircle.toCircle : AddCircle (2 * Real.pi) → Circle) := by
    funext θ
    induction θ using Real.Angle.induction_on with
    | h x =>
      rw [Real.Angle.toCircle_coe]
      show Circle.exp x = AddCircle.toCircle (x : AddCircle (2 * Real.pi))
      rw [AddCircle.toCircle_apply_mk]
      congr 1
      field_simp
  rw [this]
  exact AddCircle.continuous_toCircle

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem Winv_fderiv (F : E → ℝ) (u : E) :
    QuantumNLS.ProductTorusGenerator.Winv (fderiv ℝ F u) = SymplecticBracket.hamField F u := by
  unfold QuantumNLS.ProductTorusGenerator.Winv SymplecticBracket.hamField SymplecticBracket.gradient
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  ring

theorem coord_comp_fderiv_gen {I : E → L1 ℝ} (hI : Differentiable ℝ I) (u : E) (n : ℤ) :
    (QuantumNLS.ProductTorusGenerator.coord n).comp (fderiv ℝ I u) =
      fderiv ℝ (fun v => (I v : ℤ → ℝ) n) u :=
  (((QuantumNLS.ProductTorusGenerator.coord n).hasFDerivAt.comp u (hI u).hasFDerivAt).fderiv).symm

theorem Xn_eq_gen {I : E → L1 ℝ} (hI : Differentiable ℝ I) (n : ℤ) (u : E) :
    QuantumNLS.ProductTorusGenerator.Xn (fderiv ℝ I) n u =
      SymplecticBracket.hamField (fun v => (I v : ℤ → ℝ) n) u := by
  unfold QuantumNLS.ProductTorusGenerator.Xn
  rw [coord_comp_fderiv_gen hI]
  exact Winv_fderiv _ _

theorem hinv_gen {I : E → L1 ℝ} (hI : Differentiable ℝ I)
    (h : ∀ n j u, SymplecticBracket.pbR (fun v => (I v : ℤ → ℝ) n) (fun v => (I v : ℤ → ℝ) j) u = 0) :
    QuantumNLS.ProductTorusGenerator.Involutive (fderiv ℝ I) := by
  intro u n j
  rw [Xn_eq_gen hI]
  have h1 := congrFun (congrArg DFunLike.coe (coord_comp_fderiv_gen hI u n))
    (SymplecticBracket.hamField (fun v => (I v : ℤ → ℝ) j) u)
  exact h1.trans (h n j u)

end Generic

theorem hinv (hκ : 0 < κ) : QuantumNLS.ProductTorusGenerator.Involutive (fderiv ℝ (Iact (L := L) hκ)) :=
  hinv_gen (fun u => (hI hκ u (mem_univ u)).differentiableAt)
    (fun n j u => (RootMassInvolutionR9.root_mass_involution (L := L) hκ).2 n j u)

theorem flowHyp (hκ : 0 < κ) :
    QuantumNLS.ProductTorusFlow.Hyp (Iact (L := L) hκ) (fderiv ℝ (Iact (L := L) hκ)) where
  hasFDerivAt := fun u => ((hI hκ u (mem_univ u)).differentiableAt).hasFDerivAt
  contDiff := (hI hκ).fderiv.contDiff
  involutive := hinv hκ
  fibre_compact := QuantumNLS.ProductTorusFlow.fibre_compact_of_source (hpos hκ) (hprop hκ)

theorem hper (hκ : 0 < κ) :
    QuantumNLS.ProductTorusContinuity.Periodic (fderiv ℝ (Iact (L := L) hκ)) := by
  intro n u
  obtain ⟨hP, hflow, -, -, -, -⟩ := GlobalIndividualPeriodsR31b.global_individual_periods (L := L) hκ n
  obtain ⟨h0, hd⟩ := hflow u
  have hX : ∀ v : L2T L, QuantumNLS.ProductTorusGenerator.X (fderiv ℝ (Iact (L := L) hκ))
      (QuantumNLS.ProductTorusCommute.e n) v =
      (-Complex.I) • SymplecticBracket.gradient (RootMassInvolutionR8.mass (L := L) hκ n) v := by
    intro v
    rw [QuantumNLS.ProductTorusCommute.X_e]
    exact Xn_eq_gen (fun u => (hI hκ u (mem_univ u)).differentiableAt) n v
  have key := QuantumNLS.ProductTorusFlow.flow_eq_of_sol (flowHyp hκ)
    (QuantumNLS.ProductTorusCommute.e n) (u := u)
    (α := fun s => CompleteFlowPhysicalR107.phi (L := L) hκ n s u) h0
    (fun t => (hd t).congr_deriv (hX _).symm) (2 * Real.pi)
  exact key.trans (hP u)

/-- The product-torus hypotheses for the actual indexed masses. -/
theorem phyp (hκ : 0 < κ) :
    QuantumNLS.ProductTorusPrimitive.PHyp (Iact (L := L) hκ) (fderiv ℝ (Iact (L := L) hκ)) :=
  QuantumNLS.ProductTorusMain.phyp_of_source (hI hκ) (hpos hκ) (hinv hκ) (hprop hκ) (hper hκ)

end QuantumNLS.RF535Bridge

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RF535Bridge.hI
#print axioms QuantumNLS.RF535Bridge.hpos
#print axioms QuantumNLS.RF535Bridge.hmass
#print axioms QuantumNLS.RF535Bridge.hprop
#print axioms QuantumNLS.RF535Bridge.hinv
#print axioms QuantumNLS.RF535Bridge.hper
#print axioms QuantumNLS.RF535Bridge.phyp
