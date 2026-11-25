import QuantumNLS.Ext025AAnalysis

/-! GP-03 application to LOCAL-018. The report assumes real analyticity
on its full Hilbert ball. No Banach holomorphy-to-series premise is replaced:
this module uses that literal consumer hypothesis and proves the local
analytic inverse, the inverse differential bound, and openness of its image. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Ext025A6
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Neumann inversion with the exact norm bound used by LOCAL-018. -/
theorem neumann_equiv_bound (D : E →L[ℝ] E) {ε : ℝ}
    (hε : ε < 1) (hD : ‖D - 1‖ ≤ ε) :
    ∃ e : E ≃L[ℝ] E, e.toContinuousLinearMap = D ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ (1 - ε)⁻¹ := by
  have hu : IsUnit D := by
    have hsmall : ‖(1 : E →L[ℝ] E) - D‖ < 1 := by
      rw [norm_sub_rev]
      exact hD.trans_lt hε
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hsmall
  obtain ⟨w, hw⟩ := hu
  let e := ContinuousLinearEquiv.ofUnit w
  have he : e.toContinuousLinearMap = D := hw
  refine ⟨e, he, ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_⟩
  intro y
  let x := e.symm y
  have hx : D x = y := by rw [← he]; exact e.apply_symm_apply y
  have hsub : ‖(D - 1) x‖ ≤ ε * ‖x‖ := (D - 1).le_of_opNorm_le hD x
  have htri : ‖x‖ ≤ ‖D x‖ + ‖(D - 1) x‖ := by
    calc
      ‖x‖ = ‖D x - (D - 1) x‖ := by congr 1; simp
      _ ≤ ‖D x‖ + ‖(D - 1) x‖ := norm_sub_le _ _
  rw [hx] at htri
  have hbound : (1 - ε) * ‖x‖ ≤ ‖y‖ := by linarith
  have := (le_div_iff₀ (by linarith : 0 < 1 - ε)).2 (by nlinarith : ‖x‖ * (1 - ε) ≤ ‖y‖)
  simpa only [x, ContinuousLinearEquiv.coe_coe, div_eq_mul_inv, mul_comm] using this

/-- At every point of the report ball the source's own derivative bound
constructs the equivalence. The inverse derivative and analyticity are
conclusions. Both inverse identities hold on neighborhoods. -/
theorem local018_analytic_inverse {f : E → E} {R ε : ℝ} {a : E}
    (ha : a ∈ ball (0 : E) R)
    (hf : ∀ x ∈ ball (0 : E) R, AnalyticAt ℝ f x)
    (hε : ε < 1)
    (hD : ∀ x ∈ ball (0 : E) R, ‖fderiv ℝ f x - 1‖ ≤ ε) :
    ∃ g : E → E, AnalyticAt ℝ g (f a) ∧ g (f a) = a ∧
      HasFDerivAt g (fderiv ℝ f a).inverse (f a) ∧
      ‖(fderiv ℝ f a).inverse‖ ≤ (1 - ε)⁻¹ ∧
      (∀ᶠ x in 𝓝 a, g (f x) = x) ∧
      (∀ᶠ y in 𝓝 (f a), f (g y) = y) := by
  obtain ⟨e, he, hb⟩ := neumann_equiv_bound (fderiv ℝ f a) hε (hD a ha)
  have hd : HasFDerivAt f e.toContinuousLinearMap a :=
    he.symm ▸ (hf a ha).differentiableAt.hasFDerivAt
  obtain ⟨g, hg, hga, hl, hr⟩ :=
    QuantumNLS.Ext025A.gp03_analytic_inverse e (hf a ha) hd
  have hs : HasStrictFDerivAt f e.toContinuousLinearMap a := by
    obtain ⟨p, hp⟩ := hf a ha
    exact hp.hasFDerivAt.unique hd ▸ hp.hasStrictFDerivAt
  have hi : (fderiv ℝ f a).inverse = e.symm.toContinuousLinearMap := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  exact ⟨g, hg, hga, hi.symm ▸ (hs.to_local_left_inverse hl).hasFDerivAt,
    hi.symm ▸ hb, hl, hr⟩

/-- This is the precise GP-03 open-image application in LOCAL-018. It
uses no global surjectivity, norm identity, or assumed inverse. -/
theorem local018_open_image {f : E → E} {R ε : ℝ}
    (hf : ∀ x ∈ ball (0 : E) R, AnalyticAt ℝ f x)
    (hε : ε < 1)
    (hD : ∀ x ∈ ball (0 : E) R, ‖fderiv ℝ f x - 1‖ ≤ ε) :
    IsOpen (f '' ball (0 : E) R) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨e, he, _⟩ := neumann_equiv_bound (fderiv ℝ f a) hε (hD a ha)
  have hd : HasFDerivAt f e.toContinuousLinearMap a :=
    he.symm ▸ (hf a ha).differentiableAt.hasFDerivAt
  have hs : HasStrictFDerivAt f e.toContinuousLinearMap a := by
    obtain ⟨p, hp⟩ := hf a ha
    exact hp.hasFDerivAt.unique hd ▸ hp.hasStrictFDerivAt
  rw [← hs.map_nhds_eq_of_equiv]
  exact Filter.mem_map.mpr (mem_of_superset (isOpen_ball.mem_nhds ha)
    (fun x hx => mem_preimage.mpr ⟨x, hx, rfl⟩))
end QuantumNLS.Ext025A6

#print axioms QuantumNLS.Ext025A6.neumann_equiv_bound
#print axioms QuantumNLS.Ext025A6.local018_analytic_inverse
#print axioms QuantumNLS.Ext025A6.local018_open_image
