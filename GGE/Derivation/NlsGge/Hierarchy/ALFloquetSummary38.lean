import NlsGge.Hierarchy.ALLiouvilleInvariance38
import NlsGge.Hierarchy.ALIsospectral38

/-! Batch 38, E07 wrapper: the `H_d` flow instance of the general flow/Liouville theorems
(paper/v2.tex l.1867-1902, l.1964-1977). `H_d = 2M_d - 2 Re C₁` is `C²` on the open polydisk and
`{M_d, H_d} = 0` (derived from the isospectrality `alMass_const38`). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Set Metric Filter Topology MeasureTheory
open NlsGge.HierarchyRiccati.Core

variable {L : ℕ} [NeZero L]

/-- `H_d` is `C²` on the open polydisk. -/
theorem alHd_contDiffOn38 : ContDiffOn ℝ 2 (alHd (L := L)) (alDisk38 L) := by
  intro α hα
  refine ContDiffAt.contDiffWithinAt ?_
  have hp : ∀ k : ZMod L, ContDiffAt ℝ 2 (fun β : ZMod L → ℂ => β k) α := fun k =>
    (contDiff_apply ℝ ℂ k).contDiffAt
  have hn : ∀ k : ZMod L, ContDiffAt ℝ 2 (fun β : ZMod L → ℂ => 1 - ‖β k‖ ^ 2) α := fun k =>
    contDiffAt_const.sub ((contDiff_norm_sq ℝ (E := ℂ)).contDiffAt.comp α (hp k))
  have hM : ContDiffAt ℝ 2 (alMd (L := L)) α := by
    have : alMd (L := L) = fun β : ZMod L → ℂ => ∑ k : ZMod L, -Real.log (1 - ‖β k‖ ^ 2) := by
      funext β; simp [alMd, alR, Finset.sum_neg_distrib]
    rw [this]
    refine ContDiffAt.sum fun k _ => ?_
    have hpos : 1 - ‖α k‖ ^ 2 ≠ 0 := by
      have := hα k; nlinarith [norm_nonneg (α k)]
    exact ((hn k).log hpos).neg
  have hC : ContDiffAt ℝ 2 (fun β : ZMod L → ℂ => (alC1 β).re) α := by
    have : ContDiffAt ℝ 2 (alC1 (L := L)) α := by
      unfold alC1
      refine ContDiffAt.sum fun k _ => ?_
      exact (hp k).mul (Complex.conjCLE.contDiff.contDiffAt.comp α (hp (k - 1)))
    exact Complex.reCLM.contDiff.contDiffAt.comp α this
  exact (hM.const_smul (2 : ℝ)).sub (hC.const_smul (2 : ℝ)) |>.congr_of_eventuallyEq
    (Eventually.of_forall fun β => by simp [alHd])

/-- `{M_d, H_d} = 0` on the polydisk. -/
theorem alBracket_mass_alHd38 :
    ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) alHd α = 0 := by
  intro α hα
  obtain ⟨ε, hε, γ, h0, hγ⟩ := alFlow_local_exist38 (alHd_contDiffOn38 (L := L)) hα
  have hd0 := (hγ 0 (by simp [hε])).2
  have hder := alBracket_deriv38 (F := alMass38 L) (H := alHd) (γ := γ) (t := 0)
    (by rw [h0]; exact alMass_differentiableAt38 hα) hd0
  rw [h0] at hder
  have hU : IsOpen (Ioo (-ε) ε) := isOpen_Ioo
  have hconst : (fun s => alMass38 L (γ s)) =ᶠ[nhds 0] fun _ => alMass38 L (γ 0) := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0:ℝ)) hε] with s hs
    exact alMass_const38 hU isPreconnected_Ioo hγ hs (by simp [hε])
  exact hder.unique ((hasDerivAt_const (0:ℝ) (alMass38 L (γ 0))).congr_of_eventuallyEq hconst)

/-- The global `H_d` flow exists from every disk point, stays in the mass sublevel and conserves
`M_d`, every `C_k` and every `K_j`. -/
theorem alHdFlow_global38 {α₀ : ZMod L → ℂ} (h₀ : IsALField38 α₀) :
    ∃ γ : ℝ → ZMod L → ℂ, γ 0 = α₀ ∧ ∀ t, IsALField38 (γ t) ∧
      HasDerivAt γ (alX38 alHd (γ t)) t ∧ alMass38 L (γ t) = alMass38 L α₀ ∧
      (∀ j, ‖γ t j‖ ^ 2 ≤ 1 - Real.exp (-alMass38 L α₀)) ∧
      γ t ∈ alMassSublevel38 L (alMass38 L α₀) ∧
      (∀ k : ℕ, alC38 (γ t) k = alC38 α₀ k) ∧ (∀ j : ℕ, alK38 (γ t) j = alK38 α₀ j) := by
  obtain ⟨γ, h0, hγ⟩ := alFlow_global_exist38 (alHd_contDiffOn38 (L := L)) alBracket_mass_alHd38 h₀
  refine ⟨γ, h0, fun t => ⟨(hγ t).1, (hγ t).2.1, (hγ t).2.2.1, (hγ t).2.2.2, ?_, ?_, ?_⟩⟩
  · exact ⟨(hγ t).1, le_of_eq (hγ t).2.2.1⟩
  · intro k
    have := alC_const38 (U := univ) isOpen_univ isPreconnected_univ (γ := γ)
      (fun s _ => ⟨(hγ s).1, (hγ s).2.1⟩) (mem_univ t) (mem_univ 0) k
    rwa [h0] at this
  · intro j
    have := alK_const38 (U := univ) isOpen_univ isPreconnected_univ (γ := γ)
      (fun s _ => ⟨(hγ s).1, (hγ s).2.1⟩) (mem_univ t) (mem_univ 0) j
    rwa [h0] at this

/-- The `H_d` flow map preserves the Liouville measure and each mass-sublevel restriction. -/
theorem alHdFlow_liouville38 (m s : ℝ) :
    (alLiouvilleMeasure38 L).map (alFlow38 alHd s) = alLiouvilleMeasure38 L ∧
    ((alLiouvilleMeasure38 L).restrict (alMassSublevel38 L m)).map (alFlow38 alHd s) =
      (alLiouvilleMeasure38 L).restrict (alMassSublevel38 L m) :=
  ⟨alLiouville_invariant38 (alHd_contDiffOn38 (L := L)) alBracket_mass_alHd38 s,
   alLiouville_massSublevel_invariant38 (alHd_contDiffOn38 (L := L)) alBracket_mass_alHd38 m s⟩

/-- Bundled E07 facts (E07.02-E07.06) for one disk point; each conjunct is the named theorem. -/
theorem E07_summary38 (hL3 : 3 ≤ L) (hodd : Odd L) {α : ZMod L → ℂ} (hα : IsALField38 α) :
    -- E07.02 unit determinant of the monodromy
    (∀ z : ℂ, z ≠ 0 → (alMonodromy38 α z).det = 1) ∧
    -- E07.03 exterior multiplier: eigenvalue, modulus > 1, value at infinity e^{M_d/2}
    (∀ ζ ∈ Metric.ball (0 : ℂ) 1, ζ ≠ 0 →
      (∃ v, v ≠ 0 ∧ (alMonodromy38 α ζ⁻¹).mulVec v = ((ζ ^ L)⁻¹ * alExteriorG38 α ζ) • v) ∧
        1 < ‖(ζ ^ L)⁻¹ * alExteriorG38 α ζ‖) ∧
    alExteriorG38 α 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) ∧
    -- D:eq:pAL with all winding coefficients
    (∀ z : ℂ, 1 < ‖z‖ → alPMinusLog38 α z =
      ((alMass38 L α / (2 * L) : ℝ) : ℂ) + 1 / (L : ℂ) *
        ∑' k : ℕ, alC38 α (k + 1) * z⁻¹ ^ (2 * (k + 1))) ∧
    -- E07.04 kappa: continuity, nonnegativity, bands, pi-periodicity, Fourier identities
    Continuous (alKappa38 α) ∧ (∀ θ, 0 ≤ alKappa38 α θ) ∧
    (∀ θ, alKappa38 α θ = 0 ↔
      ‖(alMonodromy38 α (Complex.exp ((θ : ℂ) * Complex.I))).trace‖ ≤ 2) ∧
    (∀ θ, alKappa38 α (θ + Real.pi) = alKappa38 α θ) ∧
    ∫ θ in (0 : ℝ)..2 * Real.pi, alKappa38 α θ = Real.pi * alMass38 L α / L ∧
    (∀ k : ℕ, 1 ≤ k → ∫ θ in (0 : ℝ)..2 * Real.pi, alKappa38 α θ * Real.cos (2 * k * θ) =
      Real.pi * (alC38 α k).re / L) ∧
    -- E07.06 C1, C2 (D:eq:C12)
    alC38 α 1 = ∑ j, α j * (starRingEnd ℂ) (α (j - 1)) ∧
    alC38 α 2 = ∑ j, α j * (starRingEnd ℂ) (α (j - 2)) * (1 - ((‖α (j - 1)‖ ^ 2 : ℝ) : ℂ)) -
      1 / 2 * ∑ j, (α j * (starRingEnd ℂ) (α (j - 1))) ^ 2 ∧
    -- E07.05/06 H_d flow: C^2, {M_d,H_d}=0, global flow with conservation, Liouville invariance
    ContDiffOn ℝ 2 (alHd (L := L)) (alDisk38 L) ∧
    (∀ β : ZMod L → ℂ, IsALField38 β → alBracket38 (alMass38 L) alHd β = 0) ∧
    (∃ γ : ℝ → ZMod L → ℂ, γ 0 = α ∧ ∀ t, IsALField38 (γ t) ∧
      HasDerivAt γ (alX38 alHd (γ t)) t ∧ alMass38 L (γ t) = alMass38 L α ∧
      (∀ k : ℕ, alC38 (γ t) k = alC38 α k) ∧ (∀ j : ℕ, alK38 (γ t) j = alK38 α j)) ∧
    (∀ s : ℝ, (alLiouvilleMeasure38 L).map (alFlow38 alHd s) = alLiouvilleMeasure38 L) := by
  refine ⟨fun z hz => det_alMonodromy38 hα hz, ?_, alExteriorG38_zero hα, ?_,
    continuous_alKappa38 hα, alKappa38_nonneg α, alKappa38_eq_zero_iff α,
    alKappa38_add_pi_odd hodd α, integral_alKappa38 hα, fun k hk => integral_alKappa38_cos hα hk,
    alC38_one38 hL3 hα, alC38_two38 hL3 hα, alHd_contDiffOn38, alBracket_mass_alHd38, ?_,
    fun s => (alHdFlow_liouville38 0 s).1⟩
  · intro ζ hζ hζ0
    have h := alExteriorG38_multiplier hα hζ hζ0
    exact ⟨h.1, h.2.2⟩
  · intro z hz
    exact (alPMinusLog38_laurent hα hz).2
  · obtain ⟨γ, h0, hγ⟩ := alHdFlow_global38 hα
    exact ⟨γ, h0, fun t => ⟨(hγ t).1, (hγ t).2.1, (hγ t).2.2.1, (hγ t).2.2.2.2.2⟩⟩

#check @E07_summary38
#print axioms E07_summary38
#check @alHd_contDiffOn38
#check @alBracket_mass_alHd38
#check @alHdFlow_global38
#check @alHdFlow_liouville38
#print axioms alHdFlow_global38
#print axioms alHdFlow_liouville38

end NlsGge.AblowitzLadik
