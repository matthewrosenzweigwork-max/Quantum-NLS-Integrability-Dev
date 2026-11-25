import Mathlib
import NlsGge.Atomic.LIB.LIB018

-- LIB-019 variant 04A (general NontriviallyNormedField 𝕜), proved from the accepted LIB-018
-- analytic local inverse chart applied to Φ(p,x) = (p, G(p,x)) on P × E.
-- Statement is the approved COMMAND04A proposition (proof development), verbatim up to binder layout.

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace NlsGge.Atomic.LIB

theorem LIB019_04A : ∀ {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (G : P × E → F) (p0 : P) (x0 : E),
    AnalyticAt 𝕜 G (p0, x0) →
    G (p0, x0) = 0 →
    (∃ e : E ≃L[𝕜] F, fderiv 𝕜 (fun x => G (p0, x)) x0 = (e : E →L[𝕜] F)) →
    ∃ x : P → E,
      AnalyticAt 𝕜 x p0 ∧
      x p0 = x0 ∧
      (∀ᶠ p in nhds p0, G (p, x p) = 0) ∧
      (∃ U ∈ nhds x0, ∀ᶠ p in nhds p0, ∀ y ∈ U, G (p, y) = 0 → y = x p) := by
  intro 𝕜 P E F _ _ _ _ _ _ _ _ _ _ G p0 x0 hG h0 he
  obtain ⟨e, he⟩ := he
  set D : P × E →L[𝕜] F := fderiv 𝕜 G (p0, x0) with hDdef
  have hGd : HasFDerivAt G D (p0, x0) := hG.differentiableAt.hasFDerivAt
  -- the slice derivative is `D` restricted to the second factor
  have hslice : ∀ x : E, (e : E →L[𝕜] F) x = D (0, x) := by
    intro x
    have h1 : HasFDerivAt (fun x : E => ((p0, x) : P × E)) (ContinuousLinearMap.inr 𝕜 P E) x0 :=
      hasFDerivAt_prodMk_right p0 x0
    have h2 : fderiv 𝕜 (fun x => G (p0, x)) x0 = D.comp (ContinuousLinearMap.inr 𝕜 P E) :=
      (hGd.comp x0 h1).fderiv
    rw [← he, h2]
    rfl
  have key : ∀ v : P × E, D v = D (v.1, 0) + (e : E →L[𝕜] F) v.2 := by
    intro v
    have hv : D v = D (v.1, 0) + D (0, v.2) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    rw [hv, hslice]
  -- the derivative of Φ(p,x) = (p, G(p,x)) as an explicit linear equivalence
  let Ψ : P × E →L[𝕜] P × F := (ContinuousLinearMap.fst 𝕜 P E).prod D
  let Ψinv : P × F →L[𝕜] P × E :=
    (ContinuousLinearMap.fst 𝕜 P F).prod
      ((e.symm : F →L[𝕜] E).comp ((ContinuousLinearMap.snd 𝕜 P F) -
        (D.comp (ContinuousLinearMap.inl 𝕜 P E)).comp (ContinuousLinearMap.fst 𝕜 P F)))
  have hΨ_apply : ∀ v : P × E, Ψ v = (v.1, D v) := fun v => rfl
  have hΨinv_apply : ∀ w : P × F, Ψinv w = (w.1, e.symm (w.2 - D (w.1, 0))) := fun w => rfl
  have hleft : ∀ v : P × E, Ψinv (Ψ v) = v := by
    intro v
    rw [hΨ_apply, hΨinv_apply]
    refine Prod.ext rfl ?_
    show e.symm (D v - D (v.1, 0)) = v.2
    have h1 : D v - D (v.1, 0) = (e : E →L[𝕜] F) v.2 := by
      rw [key v, add_sub_cancel_left]
    rw [h1, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  have hright : ∀ w : P × F, Ψ (Ψinv w) = w := by
    intro w
    rw [hΨinv_apply, hΨ_apply]
    refine Prod.ext rfl ?_
    show D (w.1, e.symm (w.2 - D (w.1, 0))) = w.2
    rw [key (w.1, e.symm (w.2 - D (w.1, 0)))]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    abel
  let Φlin : (P × E) ≃L[𝕜] (P × F) := ContinuousLinearEquiv.equivOfInverse Ψ Ψinv hleft hright
  -- Φ(p,x) = (p, G(p,x)) is analytic at (p0,x0) with derivative Φlin
  set Φ : P × E → P × F := fun z => (z.1, G z) with hΦdef
  have hΦa : AnalyticAt 𝕜 Φ (p0, x0) := analyticAt_fst.prod hG
  have hΦd : HasFDerivAt Φ Ψ (p0, x0) := (hasFDerivAt_fst).prodMk hGd
  have hL : fderiv 𝕜 Φ (p0, x0) = (Φlin : (P × E) →L[𝕜] (P × F)) := by
    rw [hΦd.fderiv]
    rfl
  have hΦ0 : Φ (p0, x0) = (p0, 0) := Prod.ext rfl h0
  -- the analytic local inverse chart of Φ (accepted LIB-018)
  let C := NlsGge.Atomic.LIB018.analyticLocalInverseChart hΦa hL
  have hsrc : (p0, x0) ∈ C.source := NlsGge.Atomic.LIB017.mem_localInverseChart_source _
  have hσa : AnalyticAt 𝕜 C.symm (p0, 0) := by
    have hσ := NlsGge.Atomic.LIB018.localInverseChart_analyticAt hΦa hL
    rw [hΦ0] at hσ
    exact hσ
  have hfix : C.symm (p0, 0) = (p0, x0) := by
    rw [← hΦ0]
    exact C.left_inv hsrc
  have hright_inv : ∀ p : P, (p, (0 : F)) ∈ C.target →
      (C.symm (p, 0)).1 = p ∧ G (C.symm (p, 0)) = 0 := by
    intro p hp
    have h := C.right_inv hp
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hq : AnalyticAt 𝕜 (fun p : P => ((p, (0 : F)) : P × F)) p0 :=
    analyticAt_id.prod analyticAt_const
  have hx_an : AnalyticAt 𝕜 (fun p : P => (C.symm (p, 0)).2) p0 :=
    analyticAt_snd.comp (hσa.comp_of_eq hq rfl)
  have hmem : (p0, (0 : F)) ∈ C.target := by
    rw [← hΦ0]
    exact C.map_source hsrc
  have hcont : Continuous (fun p : P => ((p, (0 : F)) : P × F)) :=
    continuous_id.prodMk continuous_const
  have hev : ∀ᶠ p in nhds p0, (p, (0 : F)) ∈ C.target :=
    hcont.continuousAt.preimage_mem_nhds (C.open_target.mem_nhds hmem)
  refine ⟨fun p => (C.symm (p, 0)).2, hx_an, ?_, ?_, ?_⟩
  · show (C.symm (p0, 0)).2 = x0
    rw [hfix]
  · filter_upwards [hev] with p hp
    have h := hright_inv p hp
    show G (p, (C.symm (p, 0)).2) = 0
    have hz : (p, (C.symm (p, 0)).2) = C.symm (p, 0) := Prod.ext h.1.symm rfl
    rw [hz]
    exact h.2
  · have hS : C.source ∈ nhds (p0, x0) := C.open_source.mem_nhds hsrc
    obtain ⟨V, hV, U, hU, hVU⟩ := mem_nhds_prod_iff.1 hS
    refine ⟨U, hU, ?_⟩
    filter_upwards [hV, hev] with p hpV hp
    intro y hyU hGy
    have hyS : (p, y) ∈ C.source := hVU (Set.mk_mem_prod hpV hyU)
    have hzS : C.symm (p, 0) ∈ C.source := C.map_target hp
    have hΦeq : C (p, y) = C (C.symm (p, 0)) := by
      rw [C.right_inv hp]
      exact Prod.ext rfl hGy
    have hinj := C.injOn hyS hzS hΦeq
    exact congrArg Prod.snd hinj

end NlsGge.Atomic.LIB
