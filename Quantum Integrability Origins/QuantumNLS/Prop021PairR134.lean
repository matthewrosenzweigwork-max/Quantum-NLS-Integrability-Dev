import QuantumNLS.Prop021AssemblyR133
import QuantumNLS.Prop022CMain

/-! Specialize the intrinsic PROP-022 propagator and Weyl implementer to
the exact reference-carrier input consumed by the coherent estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 180000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021PairR134
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GClassical Prop022GLinear Prop022GHilbert Prop022AFock
open Prop022BClass1 Prop022BExist Prop022PositiveDataR126 Prop022ActualProfileR117
open Prop022ClassicalFlowR126 Prop022FactorialCoefficientsR115 Prop022FockPropagatorR122
open Prop022CWeyl Prop022CQuad Prop022CQuadTorus Prop022CIntrinsic Prop022OVacuum
open Prop021UnitaryR132

variable {L : ℝ} [Fact (0 < L)]

/-- The torus input uses the intrinsic theorem for its generator and
implementer, with the frozen coordinate corollary for the classical
and physical-coordinate clauses. -/
theorem pair_family : Prop021AssemblyR131.Prop022PairFamily (L := L) := by
  intro A M hA hM K hK hs u₀ T P hP
  let _ : TopologicalSpace.SeparableSpace (L2T L) := Prop022BExist.sep
  let U := UI L
  let B := positiveExtension K
  let hB := positiveExtension_bound K M A hK
  let hsa := positiveExtension_selfAdjoint K hs
  let u := profile B M A hA.le hB hsa u₀
  let S := fun t s : ℝ => fderiv ℝ (classicalFlow B M A hA.le hB hsa (t-s)) (u s)
  let V := fun t s => propagator B M A (zero_le_one.trans hM) hA.le hB hsa u₀ s t
  let ah := aSym U K M A hA.le hK hs u₀.val u₀.property
  let bh := bSym U K M A hA.le hK hs u₀.val u₀.property
  let vh := VH U K M A hA.le hK hs u₀.val u₀.property (zero_le_one.trans hM)
  have hKu : KBound (kernelsL U K) M A :=
    fun i => (norm_conjSym_le U (i+1) (K i)).trans (hK i)
  have hsu : KSelfAdj (kernelsL U K) := fun i => conjSym_adjoint U (i+1) (K i) (hs i)
  have hIntrinsic := ((Prop022CMain.PROP022_general_intrinsic L K M A hM hA hK hs u₀.val
    u₀.property T P hP (TraceClass.refBasis (L2T L))).2.1 (L2T_not_finiteDimensional L) U).1
  have hp (K' : Kernels (L2T L)) (hK' : KBound K' M A) (hs' : KSelfAdj K')
      (h : K' = K) :
      profile (positiveExtension K') M A hA.le (positiveExtension_bound K' M A hK')
        (positiveExtension_selfAdjoint K' hs') u₀ = u := by
    subst K'
    rfl
  have hu : profile (BL U K) M A hA.le (BL_bound U K M A hK)
      (BL_selfAdj U K hs) (sphL U u₀.val u₀.property) = u :=
    hp _ hKu hsu (kernelsL_refl K)
  have hflow (K' : Kernels (L2T L)) (hK' : KBound K' M A) (hs' : KSelfAdj K')
      (h : K' = K) (t : ℝ) :
      classicalFlow (positiveExtension K') M A hA.le (positiveExtension_bound K' M A hK')
        (positiveExtension_selfAdjoint K' hs') t = classicalFlow B M A hA.le hB hsa t := by
    subst K'
    rfl
  have hSH (t s : ℝ) : SH U K M A hA.le hK hs u₀.val u₀.property t s = S t s := by
    have hφ : flowH U K M A hA.le hK hs (t-s) = classicalFlow B M A hA.le hB hsa (t-s) :=
      hflow _ hKu hsu (kernelsL_refl K) _
    have hProfile : profH U K M A hA.le hK hs u₀.val u₀.property = u := hu
    unfold SH S
    rw [hφ, hProfile]
  have hBL : BL U K = B := congrArg positiveExtension (kernelsL_refl K)
  have hsym (n : ℕ) (x : HN L n) : (symMap U n).symm x = x := by
    apply (symMap U n).injective
    rw [LinearIsometryEquiv.apply_symm_apply, symMap_refl]
  have ha (t : ℝ) : ah t = numberCoefficient B (u t) := by
    unfold ah aSym
    rw [hu, hBL]
    apply ContinuousLinearMap.ext
    intro x
    change (symMap U 1).symm (numberCoefficient B (u t) (symMap U 1 x)) = _
    rw [symMap_refl, hsym]
  have hb (t : ℝ) : bh t = pairCoefficient B (u t) := by
    unfold bh bSym
    rw [hu, hBL, hsym]
  have hV (t s : ℝ) : vh t s = V t s :=
    LinearIsometryEquiv.ext fun x => Prop022BPairInput.VH_refl_eq K M A hM hA hK hs u₀ t s x
  have hW (v : L2T L) : IsWeylOp v (printedWeyl v) := by
    have hsymm (x : Fock L) : (gam U).symm x = x := by
      apply (gam U).injective
      rw [LinearIsometryEquiv.apply_symm_apply, gam_refl]
    have he : WH U v = printedWeyl v := by
      apply LinearIsometryEquiv.ext
      intro x
      change (gam U).symm (printedWeyl v (gam U x)) = _
      rw [gam_refl, hsymm]
    exact he ▸ (WH_isWeylOp U v)
  obtain ⟨hc,hS,hl,hblocks,hβ,h0,hcomp,hcont,_,_,hv⟩ :=
    (Prop022BPairInput.Prop022PairInput_of_general K M A hM hA hK hs u₀ T P hP).1
  refine ⟨hc,hS,hl,hblocks,hβ,h0,hcomp,hcont,?_,?_,hv⟩
  · intro s t x hx
    have hxH (j : ℕ) : x ∈ momentDomainH j :=
      (gam_mem_momentDomain U j x).1 (by rw [gam_refl]; exact hx j)
    have hd : HasDerivAt (fun r => vh r s x)
        ((-Complex.I) • QPrint (ah t) (bh t) (vh t s x)) t :=
      (hIntrinsic.schrodinger s t x hxH).2
    have hm : V t s x ∈ Ext005Moments.momentDomain (L := L) 2 := by
      have ht := hIntrinsic.domain s t x hxH 2
      change vh t s x ∈ momentDomainH 2 at ht
      have hw := (gam_mem_momentDomain U 2 (vh t s x)).2 ht
      rw [gam_refl, hV] at hw
      exact hw
    have hd' : HasDerivAt (fun r => V r s x)
        ((-Complex.I) • QPrint (numberCoefficient B (u t)) (pairCoefficient B (u t)) (V t s x)) t := by
      simpa only [hV, ha, hb] using hd
    rw [QPrint_eq (QRel_torus _ _ _ hm)] at hd'
    exact hd'
  · intro s t v x
    have hW' : IsWeylOp (SH U K M A hA.le hK hs u₀.val u₀.property t s v)
        (printedWeyl (S t s v)) := by rw [hSH]; exact hW _
    have hi := hIntrinsic.implement s t v _ _ (hW v) hW' x
    change vh t s (printedWeyl v ((vh t s).symm x)) = printedWeyl (S t s v) x at hi
    rw [hV] at hi
    exact hi

end QuantumNLS.Prop021PairR134

#print axioms QuantumNLS.Prop021PairR134.pair_family
