import NlsGge.Birkhoff.F05Identity38d

/-! # F05, file e: `J_T = e^{-D_m}` almost surely and `(T⁻¹)_# γ_m = e^{-D_m} γ_m` (F05.05)

v2: "Lemma `determinants` and `eq:cylindricalcommon` identify `J_T = e^{-D_m}` almost surely."
Ramer's theorem (F05 instance of the generalized theorem, D3) gives `J_N → J_T` in `γ`-measure;
F04 and F01 give `J_N → e^{-D_m}` pointwise on a full-measure set.  Uniqueness of limits.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.Ramer.General NlsGge.Ramer
  NlsGge.Analysis.RegularizedDeterminant Filter Topology
open scoped ENNReal

section Ident

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

/-- Pointwise limit of the finite Ramer densities (F05.05, deterministic part). -/
theorem tendsto_finiteRamerDensity05 (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, (S05 m β hm hβ).coord n ((S05 m β hm hβ).R z) = z n) :
    Tendsto (fun N : ℕ => finiteRamerDensity (fun v : (S05 m β hm hβ).head N =>
        v + (S05 m β hm hβ).truncField (K05 B O hm hβ) N v) ((S05 m β hm hβ).headPt N z))
      atTop (𝓝 (Real.exp (-(D05 hm hβ ((S05 m β hm hβ).R z))))) := by
  have h1 := tendsto_det05 B O hm hβ z hz
  have h2 := tendsto_energy05 B O hm hβ z hz
  have h3 := (Real.continuous_exp.tendsto _).comp h2.neg
  have h4 := h1.mul h3
  rw [one_mul] at h4
  refine h4.congr (fun N => ?_)
  unfold finiteRamerDensity
  simp only [Function.comp]
  congr 2
  ring


include O in
/-- **F05.05.** `(T⁻¹)_# γ_m = e^{-D_m} γ_m` on `E = h^{m-1}`. -/
theorem ramer_density05 :
    (S05 m β hm hβ).γE.map (T05 B hm hβ).symm =
      (S05 m β hm hβ).γE.withDensity (fun x => ENNReal.ofReal (Real.exp (-(D05 hm hβ x)))) := by
  obtain ⟨δK, -, -, hrest⟩ := ramer_F05_instance (m := m) (β := β) hm
    (fun i hi => (hβ i hi).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) (T05 B hm hβ)
    (K05 B O hm hβ) (K05' B O hm hβ) (hT05 B O hm hβ) (hTs05 B O hm hβ)
    ((analytic_K05 B O hm hβ).contDiff) ((analytic_K05' B O hm hβ).contDiff)
  obtain ⟨hmap, -, -, -, hconv⟩ := hrest
  obtain ⟨ns, hns, hae⟩ := hconv.exists_seq_tendsto_ae
  have hlim : ∀ᵐ z ∂(S05 m β hm hβ).γ, ∀ n, (S05 m β hm hβ).coord n ((S05 m β hm hβ).R z) = z n :=
    (S05 m β hm hβ).coord_R_ae
  have hJ : ∀ᵐ z ∂(S05 m β hm hβ).γ, (fun x => |det2 ((S05 m β hm hβ).hsDerivH
        (K05 B O hm hβ) x)| *
        Real.exp (-(δK ((S05 m β hm hβ).coordE x)) - ‖K05 B O hm hβ x‖ ^ 2 / 2))
        ((S05 m β hm hβ).R z) = Real.exp (-(D05 hm hβ ((S05 m β hm hβ).R z))) := by
    filter_upwards [hae, hlim] with z hz1 hz2
    have h2 := tendsto_finiteRamerDensity05 B O hm hβ z hz2
    exact tendsto_nhds_unique hz1 (h2.comp hns.tendsto_atTop)
  have hJ' : ∀ᵐ x ∂(S05 m β hm hβ).γE, (fun x => |det2 ((S05 m β hm hβ).hsDerivH
        (K05 B O hm hβ) x)| *
        Real.exp (-(δK ((S05 m β hm hβ).coordE x)) - ‖K05 B O hm hβ x‖ ^ 2 / 2)) x =
      Real.exp (-(D05 hm hβ x)) := by
    filter_upwards [(S05 m β hm hβ).ae_of_ae_coordE hJ] with x hx
    simpa only [(S05 m β hm hβ).R_coordE] using hx
  refine hmap.trans ?_
  exact withDensity_congr_ae (by filter_upwards [hJ'] with x hx; exact congrArg ENNReal.ofReal hx)

end Ident

end NlsGge.Birkhoff
