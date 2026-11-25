import QuantumNLS.Ext025A3Compact

/-! Transfer of compact lower-exponent embeddings through the accepted
normalized periodic Fourier isometry. No trace theorem is substituted. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
namespace QuantumNLS.Ext025A3
variable {L : ℝ} [Fact (0 < L)]

/-- Compactness is transferred through the exact weighted Fourier maps. -/
theorem field_incl_compact {W V : PosWeight} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, W.w n ≤ C * V.w n) (hW : ∀ n, 1 ≤ W.w n)
    (hV : ∀ n, 1 ≤ V.w n) (hc : IsCompactOperator (incl W V hC h)) :
    IsCompactOperator (fieldIncl (L := L) W V hC h) := by
  let eW := fourierHs (L := L) hW
  let eV := fourierHs (L := L) hV
  let T := eW.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((incl W V hC h).comp eV.toContinuousLinearEquiv.toContinuousLinearMap)
  have he : fieldIncl (L := L) W V hC h = T := by
    apply ContinuousLinearMap.ext
    intro u
    apply eW.injective
    change eW (fieldIncl W V hC h u) = eW (eW.symm (incl W V hC h (eV u)))
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact WSeq.ext rfl
  rw [he]
  exact (hc.comp_clm eV.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    eW.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Physical DEF-002 H^s embeds compactly in H^t for every 0 ≤ t < s. -/
theorem root01_def002_field_compact {s t : ℝ} (ht : 0 ≤ t) (hst : t < s) :
    IsCompactOperator (H02.mono (L := L) hst.le) :=
  field_incl_compact zero_le_one (def002_le_of_le L hst.le)
    (one_le_def002 L ht) (one_le_def002 L (ht.trans hst.le))
    (root01_def002_compact (Fact.out : 0 < L) hst)

/-- The F04 norm has its own compact lower-exponent embedding. -/
theorem root01_f04_field_compact {s t : ℝ} (ht : 0 ≤ t) (hst : t < s) :
    IsCompactOperator (H04sp.mono (L := L) hst.le) :=
  field_incl_compact zero_le_one (f04W_le_of_le L hst.le)
    (one_le_f04W L ht) (one_le_f04W L (ht.trans hst.le))
    (root01_f04_compact (Fact.out : 0 < L) hst)

/-- A bounded source family has compact closure in the physical lower norm. -/
theorem root01_def002_precompact {s t : ℝ} (ht : 0 ≤ t) (hst : t < s)
    {S : Set (H02 L s)} (hS : Bornology.IsBounded S) :
    IsCompact (closure (H02.mono (L := L) hst.le '' S)) :=
  (root01_def002_field_compact ht hst).isCompact_closure_image_of_bounded hS

/-- The exact symmetric source cutoff transported to periodic fields. -/
def fieldHead {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) (K : ℕ) :
    WField L W →L[ℂ] WField L W :=
  (fourierHs (L := L) hW).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((head W (symmetricCut K)).comp
      (fourierHs (L := L) hW).toContinuousLinearEquiv.toContinuousLinearMap)

theorem fieldHead_fourier {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) (K : ℕ)
    (u : WField L W) (n : ℤ) :
    QuantumNLS.Fourier.fourierL2 L (fieldHead hW K u).val n =
      if -(K : ℤ) ≤ n ∧ n ≤ K then QuantumNLS.Fourier.fourierL2 L u.val n else 0 := by
  have h := congrArg (fun x : WSeq W => x.val n)
    ((fourierHs (L := L) hW).apply_symm_apply
      (head W (symmetricCut K) (fourierHs hW u)))
  change QuantumNLS.Fourier.fourierL2 L (fieldHead hW K u).val n = _ at h
  rw [symmetric_cutoff_val] at h
  exact h
end QuantumNLS.Ext025A3
#print axioms QuantumNLS.Ext025A3.field_incl_compact
#print axioms QuantumNLS.Ext025A3.root01_def002_field_compact
#print axioms QuantumNLS.Ext025A3.root01_f04_field_compact
#print axioms QuantumNLS.Ext025A3.root01_def002_precompact
#print axioms QuantumNLS.Ext025A3.fieldHead_fourier
