import Mathlib
import QuantumNLS.FunctionalLinearizationSource

/-!
# PROP-026 `lem:MP-linearization`: linearization of the combined generator

Source: `source/chapters/propagation/mixed_propagation.tex:354` (`\ReportID{PROP-026}`), with its proof.  The lemma:
for normalized `φ ∈ ran P_N`, uniformly on the boxes,
`‖γ^{(k)}_{e^{-iNC_{0,N}(t,θ)}φ} − γ^{(k)}_{e^{-iNL_N(t,θ)}φ}‖₁ ≤ C_k(W_aΔ_N + ρ^I_N)`; in particular the fixed-contour
error `ρ^I_N` is not multiplied by `W_a`.  Printed proof: a commutator bound `‖[S_N(z),J_N]‖ ≤ Ck‖J‖/N`; apply
`lem:A4-functional-linearization` (PROP-014) in its integral-over-parameter form to the quadratures of `S_N(z)` and the
smooth functions `f_z`; estimate the integral at each parameter before summing (`Δ_N` on `Γ_a` weighted by `|p_t|`,
`ρ^I_N` on the fixed contours weighted by `|θ_n|` and the fixed lengths); trace-norm duality.

## Imported (read-only) and the convention inherited
This module imports the PROP-014 chain (`FunctionalLinearizationSource`, hence `…ParamMeas`, `…Param`) and uses the
**operator-norm Bochner interpretation** of `H_N = N ∫ F_θ(B_θ)dν`, `H^lin = N∫∑∂_jF_θ(b_θ)B_{θ,j}dν`: integrals in the
Banach algebra `B(H)`, with the measurable-family hypotheses `hB` (`θ ↦ B_{θ,j}` strongly measurable in operator norm),
`hFm` (`θ ↦ F_θ|_K` strongly measurable in `C(K,ℂ)`), `hdF` (`θ ↦ ∂_jF_θ(b_θ)` measurable).  PROP-026 therefore inherits
exactly the one qualification of PROP-014 (the owner's ruling on that interpretation is pending); the readings it
does not cover (SOT/WOT-measurability with a Pettis integral) are listed in `FunctionalLinearizationVarying`.

## New here: the weighted integral form of PROP-014
The lemma needs a *parameter-dependent* deviation (`Δ_N` on `Γ_a`, `ρ^I_N` on `Γ_n`) and weight, which the uniform
`functional_linearization_param*` do not give.  Proved, by the same argument:
* `functional_linearization_param_weighted`: bound `(∫ Cb δ dν) · T · C_J` with `Cb, δ : Θ → ℝ`;
* `functional_linearization_param_core_weighted`: with the canonical cutoff `χ F_θ` (`‖D^iF_θ‖ ≤ w(θ) M` on `U`), bound
  `C₀C₁M (∫ w δ dν) T C_J`, no margin hypothesis (`K ⊆ Q`, `b_θ ∈ Q`).

## The lemma
`prop026_linearization` (observable form, `t = 1`) and `prop026_split` (large contour `Θa` versus fixed contours,
`≤ C₀C₁M₀(Δ ∫_{Θa}w + ρ ∫_{Θaᶜ}w)C_J`, so `ρ` multiplies only the fixed weighted length).  `C₀` depends on `d`, `C₁`
on `(Q,U,d)`, nothing on `N`, `J`, `φ` or the contours.

## Objects the source uses and how they are bound
Taken as explicit parameters (not realized in the repository; listed): the transfer operators `S_N(z)` and `D(z)`, the
contours `Γ_a, Γ_n` and weights `p_t, θ_n`, the chart `λ` and the smooth extensions `f_z` (they enter through the real
smooth functions `F_θ` on the parameter space `Θ`, with the real part and the factors `−1/(2πκ)`, `dz` absorbed); the two
commuting quadratures `B_{θ,1}, B_{θ,2}` of `S_N(z)` (the functional calculus `Φ θ` on `C(K,ℂ)`, `K ⊆` the fixed cube
`Q`); the projection `P_N` and `φ_N` (only through the deviation hypothesis `hφδ : ‖(B_{θ,j} − b_{θ,j})φ‖ ≤ δ(θ)`);
the deviations `Δ_N, ρ^I_N` (`eq:MP-fixed-deviation`, `eq:MP-growing-deviation`); the observable `J_N = 𝒰_{N,k}(J)`
(`J`, through `‖[B_{θ,j},J]‖ ≤ C_J/N`, the source's `eq:MP-local-commutator` with `C_J = Ck‖J‖`).
`C0N`, `LN` and `HnlPK_eq_smul_C0N`, `HlinP_eq_smul_LN` record `e^{-iNC_{0,N}} = evol (N·C0N)` and `e^{-iNL_N} = evol (N·LN)`.

## Not formalized (exact remaining statements)
1. From the observable form to the trace-norm statement: the identity `⟨ψ, 𝒰_{N,k}(J)ψ⟩ = Tr(Jγ^{(k)}_ψ)` for general
   symmetric `ψ` (DEF-009 `inner_U_N_r_product` and DEF-030 `reducedDensityN` are realized, the identity for general `ψ` is not)
   plus trace-norm duality (`TraceClass.traceNorm_le_of_forall` is the realized converse direction).
2. The commutator estimate `eq:MP-local-commutator` from the placement structure (DEF-009/041) — an input hypothesis here.
3. The identification of the abstract `F_θ`, `b_θ` with `f_z(S_N(z))`, `s(z)` and of `L_N` with `eq:MP-L` via `∂_wλ = D⁻¹`.
-/

set_option autoImplicit false

open NormedSpace ComplexConjugate MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff FourierTransform

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section Weighted

variable {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- **PROP-014, integral clause with parameter-dependent deviation and constant (weighted form).**
The deviation `δ θ` and the Schwartz constant `Cb θ` may depend on the parameter; the estimate is
`(∫ Cb δ dν) · T · C_J` (the uniform case `δ θ = δ`, `Cb θ = Cb` gives `ν(Θ) Cb T C_J δ`). -/
theorem functional_linearization_param_weighted
    (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiff ℝ ∞ (F θ))
    (hFc : ∀ θ, HasCompactSupport (F θ)) (b : Θ → EuclideanSpace ℝ (Fin d))
    (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
    (hA : Integrable (fun θ => Fop (Φ θ) (F θ) (hF θ).continuous) ν)
    (hL : Integrable (fun θ => LinOp (Φ θ) (F θ) (b θ)) ν)
    (N : ℝ) (hN : 0 < N) (ψ : H) (hψ : ‖ψ‖ = 1) (δ : Θ → ℝ) (hδ : ∀ θ, 0 ≤ δ θ)
    (hψδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖ ≤ δ θ)
    (J : H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
    (hJ : ∀ θ j, ‖Φ θ (coordC j) * J - J * Φ θ (coordC j)‖ ≤ CJ / N)
    (Cb : Θ → ℝ) (hCb0 : ∀ θ, 0 ≤ Cb θ)
    (hCb : ∀ θ, CF (schwartzOfReal (F θ) (hF θ) (hFc θ)) ≤ Cb θ)
    (hW : Integrable (fun θ => Cb θ * δ θ) ν)
    (t T : ℝ) (ht : |t| ≤ T) :
    ‖⟪evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ,
        J (evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ)⟫_ℂ -
      ⟪evol (HlinP ν Φ F b N) t ψ, J (evol (HlinP ν Φ F b N) t ψ)⟫_ℂ‖ ≤
      (∫ θ, Cb θ * δ θ ∂ν) * T * CJ := by
  have : Nontrivial H := ⟨⟨ψ, 0, fun h => by rw [h] at hψ; simp at hψ⟩⟩
  have hcommI : ∀ θ θ' (g g' : C(K, ℂ)), Commute (Φ θ g) (Φ θ' g') :=
    fun θ θ' g g' => commute_images (Φ θ) (Φ θ') (hcomm θ θ') g g'
  set A : Θ → H →L[ℂ] H := fun θ => Fop (Φ θ) (F θ) (hF θ).continuous with hAdef
  set L : Θ → H →L[ℂ] H := fun θ => LinOp (Φ θ) (F θ) (b θ) with hLdef
  have hG : Integrable (fun θ => A θ - L θ) ν := hA.sub hL
  set D : H →L[ℂ] H := (N : ℂ) • ∫ θ, (A θ - L θ) ∂ν with hDdef
  have hHD : HnlP ν Φ F (fun θ => (hF θ).continuous) N - HlinP ν Φ F b N = D := by
    unfold HnlP HlinP
    rw [← smul_sub, ← integral_sub hA hL]
  have hNsa : IsSelfAdjoint (N : ℂ) := by simp [IsSelfAdjoint]
  have hGs : ∀ θ, IsSelfAdjoint (A θ - L θ) := fun θ =>
    (isSelfAdjoint_Fop (Φ θ) (F θ) (hF θ).continuous).sub (isSelfAdjoint_LinOp (Φ θ) (F θ) (b θ))
  have hDsa : IsSelfAdjoint D := hNsa.smul (isSelfAdjoint_integral hG hGs)
  have hLsa : IsSelfAdjoint (HlinP ν Φ F b N) :=
    hNsa.smul (isSelfAdjoint_integral hL (fun θ => isSelfAdjoint_LinOp (Φ θ) (F θ) (b θ)))
  -- commutation
  have hLim : ∀ θ, ∃ g : C(K, ℂ), L θ = Φ θ g := fun θ => ⟨_, LinOp_eq (Φ θ) (F θ) (b θ)⟩
  have hGim : ∀ θ, ∃ g : C(K, ℂ), A θ - L θ = Φ θ g := by
    intro θ
    obtain ⟨g, hg⟩ := hLim θ
    exact ⟨liftC (fun x => ((F θ x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp (hF θ).continuous) - g, by
      rw [map_sub, ← hg]; rfl⟩
  have hGL : ∀ θ θ', Commute (A θ - L θ) (L θ') := by
    intro θ θ'
    obtain ⟨g, hg⟩ := hGim θ
    obtain ⟨g', hg'⟩ := hLim θ'
    rw [hg, hg']; exact hcommI _ _ _ _
  have hGLint : Commute (∫ θ, (A θ - L θ) ∂ν) (∫ θ, L θ ∂ν) :=
    commute_integral_left hG (fun θ => commute_integral_right hL (fun θ' => hGL θ θ'))
  have hcommDH : Commute D (HlinP ν Φ F b N) := (hGLint.smul_left _).smul_right _
  have hXim : ∀ θ j, Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H) =
      Φ θ (coordC j - ((b θ j : ℝ) : ℂ) • (1 : C(K, ℂ))) := fun θ j => by
    rw [map_sub, map_smul, map_one]
  have hXG : ∀ θ j θ', Commute (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (A θ' - L θ') := by
    intro θ j θ'
    obtain ⟨g, hg⟩ := hGim θ'
    rw [hXim, hg]; exact hcommI _ _ _ _
  have hXL : ∀ θ j θ', Commute (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (L θ') := by
    intro θ j θ'
    obtain ⟨g, hg⟩ := hLim θ'
    rw [hXim, hg]; exact hcommI _ _ _ _
  have hXD : ∀ θ j, Commute (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) D :=
    fun θ j => (commute_integral_right hG (fun θ' => hXG θ j θ')).smul_right _
  have hXLin : ∀ θ j, Commute (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H))
      (HlinP ν Φ F b N) :=
    fun θ j => (commute_integral_right hL (fun θ' => hXL θ j θ')).smul_right _
  have hcl : ∀ θ, ∃ R : ℝ, 0 ≤ R ∧ ∀ x : K, ‖(x : EuclideanSpace ℝ (Fin d)) - b θ‖ ≤ R := by
    intro θ
    obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).exists_bound_of_continuousOn
      (f := fun x : K => (x : EuclideanSpace ℝ (Fin d)) - b θ)
      (by fun_prop : Continuous fun x : K => (x : EuclideanSpace ℝ (Fin d)) - b θ).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x (Set.mem_univ x)).trans (le_max_left _ _)⟩
  have hper : ∀ φ : H, ‖φ‖ ≤ 1 →
      (∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) φ‖ ≤ δ θ) → ∀ θ,
      ‖⟪φ, ((A θ - L θ) * J - J * (A θ - L θ)) φ⟫_ℂ‖ ≤ Cb θ * δ θ * (CJ / N) := by
    intro φ hφ hX θ
    obtain ⟨R, hR0, hR⟩ := hcl θ
    have hrem := Phi_remC_bound (Φ θ) (schwartzOfReal (F θ) (hF θ) (hFc θ)) (b θ) hR0 hR J φ hφ
      (hδ θ) (div_nonneg hCJ hN.le) (hX θ) (hJ θ)
    have e : A θ - L θ = Φ θ (remC (K := K) (schwartzOfReal (F θ) (hF θ) (hFc θ)) (b θ)) +
        (((F θ (b θ) : ℝ) : ℂ) - ∑ j : Fin d, ((fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1) : ℝ) : ℂ) *
          ((b θ j : ℝ) : ℂ)) • (1 : H →L[ℂ] H) := Fop_sub_LinOp (Φ θ) (F θ) (hF θ) (hFc θ) (b θ)
    rw [e, comm_add_smul_one]
    refine hrem.trans ?_
    have h0 : 0 ≤ CJ / N := div_nonneg hCJ hN.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCb θ) (hδ θ)) h0
  have hmain : ∀ s : ℝ, ‖⟪evol D s (evol (HlinP ν Φ F b N) t ψ), (D * J - J * D)
      (evol D s (evol (HlinP ν Φ F b N) t ψ))⟫_ℂ‖ ≤ (∫ θ, Cb θ * δ θ ∂ν) * CJ := by
    intro s
    set w := evol (HlinP ν Φ F b N) t ψ with hw
    set φ := evol D s w with hφ
    have n1 : ‖evol D s‖ ≤ 1 := by unfold evol; exact norm_exp_le hDsa (-s)
    have n2 : ‖evol (HlinP ν Φ F b N) t‖ ≤ 1 := by unfold evol; exact norm_exp_le hLsa (-t)
    have hw1 : ‖w‖ ≤ 1 := by
      calc ‖w‖ ≤ ‖evol (HlinP ν Φ F b N) t‖ * ‖ψ‖ := (evol (HlinP ν Φ F b N) t).le_opNorm ψ
        _ ≤ 1 * 1 := by rw [hψ]; gcongr
        _ = 1 := one_mul 1
    have hφ1 : ‖φ‖ ≤ 1 := by
      calc ‖φ‖ ≤ ‖evol D s‖ * ‖w‖ := (evol D s).le_opNorm w
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    have hX : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) φ‖ ≤ δ θ := by
      intro θ j
      have h1 := (commute_evol (hXD θ j) s).eq
      have h2 := (commute_evol (hXLin θ j) t).eq
      have e : (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) φ =
          evol D s (evol (HlinP ν Φ F b N) t
            ((Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ)) := by
        rw [hφ, hw]
        calc _ = ((Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) * evol D s)
              (evol (HlinP ν Φ F b N) t ψ) := rfl
          _ = (evol D s * (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)))
              (evol (HlinP ν Φ F b N) t ψ) := by rw [h1]
          _ = evol D s (((Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) *
              evol (HlinP ν Φ F b N) t) ψ) := rfl
          _ = _ := by rw [h2]; rfl
      rw [e]
      calc _ ≤ ‖evol D s‖ * ‖evol (HlinP ν Φ F b N) t
            ((Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ)‖ := (evol D s).le_opNorm _
        _ ≤ 1 * (1 * ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖) := by
            gcongr
            exact ((evol (HlinP ν Φ F b N) t).le_opNorm _).trans (by gcongr)
        _ ≤ δ θ := by simpa using hψδ θ j
    have hDJ : D * J - J * D = (N : ℂ) • ((∫ θ, (A θ - L θ) ∂ν) * J - J * (∫ θ, (A θ - L θ) ∂ν)) := by
      rw [hDdef, smul_mul_assoc, mul_smul_comm, smul_sub]
    have hint := integral_commEv hG J φ
    rw [hDJ, smul_apply, inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hN, hint]
    have hgint : Integrable (fun θ => Cb θ * δ θ * (CJ / N)) ν := hW.mul_const _
    have hb := norm_integral_le_of_norm_le (μ := ν) hgint
      (f := fun θ => ⟪φ, ((A θ - L θ) * J - J * (A θ - L θ)) φ⟫_ℂ)
      (Filter.Eventually.of_forall (hper φ hφ1 hX))
    rw [integral_mul_const] at hb
    calc N * ‖∫ θ, ⟪φ, ((A θ - L θ) * J - J * (A θ - L θ)) φ⟫_ℂ ∂ν‖ ≤
          N * ((∫ θ, Cb θ * δ θ ∂ν) * (CJ / N)) := by gcongr
      _ = (∫ θ, Cb θ * δ θ ∂ν) * CJ := by field_simp
  have hfin := time_bound hDsa hcommDH ψ J t hmain
  have hH : HnlP ν Φ F (fun θ => (hF θ).continuous) N = D + HlinP ν Φ F b N :=
    sub_eq_iff_eq_add.mp hHD
  rw [hH]
  refine hfin.trans ?_
  have h0 : 0 ≤ (∫ θ, Cb θ * δ θ ∂ν) * CJ :=
    mul_nonneg (integral_nonneg fun θ => mul_nonneg (hCb0 θ) (hδ θ)) hCJ
  calc (∫ θ, Cb θ * δ θ ∂ν) * CJ * |t| ≤ (∫ θ, Cb θ * δ θ ∂ν) * CJ * T := by gcongr
    _ = (∫ θ, Cb θ * δ θ ∂ν) * T * CJ := by ring

end Weighted


section WeightedCore

/-- Weighted integrability of `θ ↦ Φ θ (g θ)`: `‖g θ‖ ≤ C θ` with `C` integrable. -/
theorem integrable_apply_comp_w {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
    (g : Θ → C(K, ℂ)) (hg : AEStronglyMeasurable g ν) (C : Θ → ℝ) (hC : Integrable C ν)
    (hgC : ∀ θ, ‖g θ‖ ≤ C θ) : Integrable (fun θ => Φ θ (g θ)) ν :=
  hC.mono' (aestronglyMeasurable_apply_comp ν Φ hB g hg)
    (ae_of_all _ fun θ => (Phi_norm_le (Φ θ) _).trans (hgC θ))

/-- Weighted integrability of `θ ↦ ∑_j a_j(θ) B_{θ,j}`. -/
theorem integrable_sum_smul_coord_w {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
    (a : Fin d → Θ → ℝ) (ha : ∀ j, AEStronglyMeasurable (a j) ν) (C : Θ → ℝ)
    (hC : Integrable C ν) (hM : ∀ θ j, |a j θ| ≤ C θ) :
    Integrable (fun θ => ∑ j : Fin d, ((a j θ : ℝ) : ℂ) • Φ θ (coordC j)) ν := by
  refine integrable_finsetSum _ (fun j _ => ?_)
  refine (hC.mul_const ‖coordC (K := K) j‖).mono' ?_ (ae_of_all _ fun θ => ?_)
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable (ha j)).smul (hB j)
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hM θ j) (Phi_norm_le (Φ θ) _) (norm_nonneg _) ((abs_nonneg _).trans (hM θ j))

/-- **Weighted core**: `δ` and the derivative bound depend on the parameter through `δ θ` and a weight
`w θ ≥ 0` (`‖D^i F_θ‖ ≤ w θ · M` on `U`); the estimate is `C₀C₁M (∫ w δ dν) T C_J`. -/
theorem functional_linearization_param_core_weighted (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
        {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hKQ : K ⊆ Q) (hbQ : ∀ θ, b θ ∈ Q)
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
        (hFm : AEStronglyMeasurable (fun θ => resKd K (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (N : ℝ) (hN : 0 < N) (ψ : H) (hψ : ‖ψ‖ = 1) (δ : Θ → ℝ) (hδ : ∀ θ, 0 ≤ δ θ)
        (hψδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖ ≤ δ θ)
        (J : H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ θ j, ‖Φ θ (coordC j) * J - J * Φ θ (coordC j)‖ ≤ CJ / N)
        (w : Θ → ℝ) (hw0 : ∀ θ, 0 ≤ w θ) (hw : Integrable w ν)
        (hwδ : Integrable (fun θ => w θ * δ θ) ν)
        {M : ℝ} (hM0 : 0 ≤ M)
        (hFb : ∀ θ, ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ w θ * M)
        (t T : ℝ) (ht : |t| ≤ T),
        ‖⟪evol (HnlPK ν Φ F N) t ψ, J (evol (HnlPK ν Φ F N) t ψ)⟫_ℂ -
          ⟪evol (HlinP ν Φ F b N) t ψ, J (evol (HlinP ν Φ F b N) t ψ)⟫_ℂ‖ ≤
          (C0 * (C1 * M)) * (∫ θ, w θ * δ θ ∂ν) * T * CJ := by
  obtain ⟨s, C0, hC0, hCF⟩ := CF_le_seminorms d
  refine ⟨max (s.sup Prod.snd) 1, C0, le_max_right _ _, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨χ, hχ, hχc, hχU, W, hWo, hQW, hχW⟩ := exists_cutoff hU hQ hQU
  obtain ⟨C1, hC1, hC1b⟩ := sup_seminorm_cutoffExt_le hU χ hχ hχc hχU s
  refine ⟨C1, hC1, fun {Θ} _ ν _ {K} _ {H} _ _ _ Φ F hF b hKQ hbQ hcomm hB hFm hdF N hN ψ hψ δ hδ
    hψδ J {CJ} hCJ hJ w hw0 hw hwδ {M} hM0 hFb t T ht => ?_⟩
  have hKU : K ⊆ U := fun x hx => hQU (hKQ hx)
  have hFK : ∀ θ, ContinuousOn (F θ) K := fun θ => (hF θ).continuousOn.mono hKU
  set F' : Θ → EuclideanSpace ℝ (Fin d) → ℝ := fun θ => cutoffExt χ U (F θ) with hF'def
  have hF' : ∀ θ, ContDiff ℝ ∞ (F' θ) := fun θ => contDiff_cutoffExt hU hχ hχU (hF θ)
  have hF'c : ∀ θ, HasCompactSupport (F' θ) := fun θ => hasCompactSupport_cutoffExt hχc
  have hWU : ∀ x ∈ W, x ∈ U := fun x hx =>
    hχU (subset_tsupport _ (Function.mem_support.mpr (by rw [hχW x hx]; exact one_ne_zero)))
  have hFF' : ∀ θ, ∀ x ∈ W, F' θ x = F θ x := fun θ x hx => by
    simp only [hF'def]; rw [cutoffExt_eq_on (hWU x hx), hχW x hx, one_mul]
  have hFop : ∀ θ, Fop (Φ θ) (F' θ) (hF' θ).continuous = Φ θ (resKd K (F θ)) := by
    intro θ
    unfold Fop
    congr 1
    refine ContinuousMap.ext fun x => ?_
    simp only [liftC, ContinuousMap.coe_mk, resKd_apply (hFK θ)]
    rw [hFF' θ x.1 (hQW (hKQ x.2))]
  have hLin : ∀ θ, LinOp (Φ θ) (F' θ) (b θ) = LinOp (Φ θ) (F θ) (b θ) := by
    intro θ
    unfold LinOp
    have hev : F' θ =ᶠ[nhds (b θ)] F θ := by
      filter_upwards [hWo.mem_nhds (hQW (hbQ θ))] with y hy using hFF' θ y hy
    rw [hev.fderiv_eq]
  have hHn : HnlP ν Φ F' (fun θ => (hF' θ).continuous) N = HnlPK ν Φ F N := by
    unfold HnlP HnlPK; simp only [hFop]
  have hHl : HlinP ν Φ F' b N = HlinP ν Φ F b N := by
    unfold HlinP; simp only [hLin]
  have hnormK : ∀ θ, ‖resKd K (F θ)‖ ≤ w θ * M := fun θ =>
    (ContinuousMap.norm_le _ (mul_nonneg (hw0 θ) hM0)).mpr fun x => by
      rw [resKd_apply (hFK θ), Complex.norm_real]
      have := hFb θ 0 (Nat.zero_le _) x.1 (hKU x.2)
      rwa [norm_iteratedFDeriv_zero] at this
  have hA' : Integrable (fun θ => Fop (Φ θ) (F' θ) (hF' θ).continuous) ν := by
    simp only [hFop]
    exact integrable_apply_comp_w ν Φ hB (fun θ => resKd K (F θ)) hFm (fun θ => w θ * M) (hw.mul_const M) hnormK
  have hdFb : ∀ θ j, |fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)| ≤ w θ * M := by
    intro θ j
    have h1 : ‖fderiv ℝ (F θ) (b θ)‖ ≤ w θ * M := by
      have := hFb θ 1 (le_max_right _ _) (b θ) (hQU (hbQ θ))
      have e : ‖iteratedFDeriv ℝ 0 (fderiv ℝ (F θ)) (b θ)‖ = ‖iteratedFDeriv ℝ (0 + 1) (F θ) (b θ)‖ :=
        norm_iteratedFDeriv_fderiv
      rw [norm_iteratedFDeriv_zero] at e
      rw [e]; simpa using this
    calc |fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)| =
          ‖fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (F θ) (b θ)‖ * ‖(EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ :=
          (fderiv ℝ (F θ) (b θ)).le_opNorm _
      _ ≤ w θ * M * 1 := by
          rw [EuclideanSpace.norm_single]
          simpa using h1
      _ = w θ * M := mul_one _
  have hL' : Integrable (fun θ => LinOp (Φ θ) (F' θ) (b θ)) ν := by
    simp only [hLin]
    exact integrable_sum_smul_coord_w ν Φ hB
      (fun j θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) hdF (fun θ => w θ * M)
      (hw.mul_const M) hdFb
  have hCb : ∀ θ, CF (schwartzOfReal (F' θ) (hF' θ) (hF'c θ)) ≤ C0 * (C1 * (w θ * M)) := fun θ =>
    (hCF _).trans (mul_le_mul_of_nonneg_left
      (hC1b (F θ) (hF θ) (w θ * M) (mul_nonneg (hw0 θ) hM0)
        (fun i hi x hx => hFb θ i (hi.trans (le_max_left _ _)) x hx)) hC0)
  have hW : Integrable (fun θ => (C0 * (C1 * (w θ * M))) * δ θ) ν :=
    (hwδ.const_mul (C0 * (C1 * M))).congr (Filter.Eventually.of_forall fun θ => by
      simp only; ring)
  have := functional_linearization_param_weighted ν Φ F' hF' hF'c b hcomm hA' hL' N hN ψ hψ δ hδ hψδ
    J hCJ hJ (fun θ => C0 * (C1 * (w θ * M)))
    (fun θ => mul_nonneg hC0 (mul_nonneg hC1 (mul_nonneg (hw0 θ) hM0))) hCb hW t T ht
  rw [hHn, hHl] at this
  have hint : ∫ θ, (C0 * (C1 * (w θ * M))) * δ θ ∂ν = (C0 * (C1 * M)) * ∫ θ, w θ * δ θ ∂ν := by
    rw [← integral_const_mul]; congr 1; funext θ; ring
  rw [hint] at this
  exact this

end WeightedCore


section Prop026

/-- `C_{0,N} = ∫ F_θ(B_θ) dν(θ)`, the combined functional of the quadratures (`eq:MP-C0`): a contour integral
over the parameter space `Θ` (contour parameters of `Γ_a` and of the fixed contours `Γ_n`, with the real part,
the factors `−1/(2πκ)`, `p_t(z)`, `θ_n` and `dz` absorbed into the smooth real functions `F_θ`). -/
def C0N {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) : H →L[ℂ] H :=
  ∫ θ, Φ θ (resKd K (F θ)) ∂ν

/-- The linearization `L_N = ∫ ∑_j ∂_jF_θ(b_θ) B_{θ,j} dν(θ)` (`eq:MP-L`; the scalar term of the Taylor
expansion is dropped, it changes no reduced density matrix). -/
def LN {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ)
    (b : Θ → EuclideanSpace ℝ (Fin d)) : H →L[ℂ] H :=
  ∫ θ, LinOp (Φ θ) (F θ) (b θ) ∂ν

theorem HnlPK_eq_smul_C0N {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (N : ℝ) :
    HnlPK ν Φ F N = (N : ℂ) • C0N ν Φ F := rfl

theorem HlinP_eq_smul_LN {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ)
    (b : Θ → EuclideanSpace ℝ (Fin d)) (N : ℝ) :
    HlinP ν Φ F b N = (N : ℂ) • LN ν Φ F b := rfl

/-- **PROP-026 `lem:MP-linearization`, observable (dual) form.**  For a normalized `φ` (in `ran P_N`),
every bounded observable `J_N` (= `𝒰_{N,k}(J)`) with the commutator bound `‖[B_{θ,j}, J_N]‖ ≤ C_J/N`
(`eq:MP-local-commutator`, `C_J = C k ‖J‖`), the two evolutions `e^{-iN C_{0,N}}` and `e^{-iN L_N}` give

`|⟨e^{-iNC_0}φ, J_N e^{-iNC_0}φ⟩ − ⟨e^{-iNL}φ, J_N e^{-iNL}φ⟩| ≤ C₀C₁M₀ (∫ w δ dν) C_J`,

where `δ(θ)` is the deviation `‖(B_{θ,j} − b_{θ,j})φ‖ ≤ δ(θ)` and `w(θ)` the weight (`‖D^iF_θ‖ ≤ w(θ) M₀`
on a fixed neighbourhood `U` of the fixed cube `Q ⊇ spectra ∪ {b_θ}`).  The constants `m, C₀` depend only on `d` and
`C₁` only on `(Q,U,d)`; they are independent of `N`, of the contours, of `J` and `φ`. -/
theorem prop026_linearization (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
        {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hKQ : K ⊆ Q) (hbQ : ∀ θ, b θ ∈ Q)
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
        (hFm : AEStronglyMeasurable (fun θ => resKd K (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (N : ℝ) (hN : 0 < N) (φ : H) (hφ : ‖φ‖ = 1) (δ : Θ → ℝ) (hδ : ∀ θ, 0 ≤ δ θ)
        (hφδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) φ‖ ≤ δ θ)
        (J : H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ θ j, ‖Φ θ (coordC j) * J - J * Φ θ (coordC j)‖ ≤ CJ / N)
        (w : Θ → ℝ) (hw0 : ∀ θ, 0 ≤ w θ) (hw : Integrable w ν)
        (hwδ : Integrable (fun θ => w θ * δ θ) ν)
        {M0 : ℝ} (hM0 : 0 ≤ M0)
        (hFb : ∀ θ, ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ w θ * M0),
        ‖⟪evol ((N : ℂ) • C0N ν Φ F) 1 φ, J (evol ((N : ℂ) • C0N ν Φ F) 1 φ)⟫_ℂ -
          ⟪evol ((N : ℂ) • LN ν Φ F b) 1 φ, J (evol ((N : ℂ) • LN ν Φ F b) 1 φ)⟫_ℂ‖ ≤
          (C0 * (C1 * M0)) * (∫ θ, w θ * δ θ ∂ν) * CJ := by
  obtain ⟨m, C0, hm, hC0, hcore⟩ := functional_linearization_param_core_weighted d
  refine ⟨m, C0, hm, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨C1, hC1, hC1b⟩ := hcore hU hQ hQU
  refine ⟨C1, hC1, fun {Θ} _ ν _ {K} _ {H} _ _ _ Φ F hF b hKQ hbQ hcomm hB hFm hdF N hN φ hφ δ hδ hφδ
    J {CJ} hCJ hJ w hw0 hw hwδ {M0} hM0 hFb => ?_⟩
  have := hC1b ν Φ F hF b hKQ hbQ hcomm hB hFm hdF N hN φ hφ δ hδ hφδ J hCJ hJ w hw0 hw hwδ hM0 hFb
    1 1 (by simp)
  simpa [HnlPK_eq_smul_C0N, HlinP_eq_smul_LN] using this

/-- **The split form of the lemma** (large contour `Γ_a` versus fixed contours `Γ_n`): if the deviation is
`≤ Δ` on the measurable set `Θa` (the large contour) and `≤ ρ` on its complement (fixed contours), then the
bound is `C₀C₁M₀ (Δ W_a' + ρ W_f') C_J`, where `W_a' = ∫_{Θa} w` and `W_f' = ∫_{Θaᶜ} w` are the two weighted
contour lengths.  In particular `ρ` is multiplied only by the *fixed* total `W_f'`, not by the `a`-dependent
`W_a'`. -/
theorem prop026_split (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
        {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hKQ : K ⊆ Q) (hbQ : ∀ θ, b θ ∈ Q)
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
        (hFm : AEStronglyMeasurable (fun θ => resKd K (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (N : ℝ) (hN : 0 < N) (φ : H) (hφ : ‖φ‖ = 1) (δ : Θ → ℝ) (hδ : ∀ θ, 0 ≤ δ θ)
        (hφδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) φ‖ ≤ δ θ)
        (J : H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ θ j, ‖Φ θ (coordC j) * J - J * Φ θ (coordC j)‖ ≤ CJ / N)
        (w : Θ → ℝ) (hw0 : ∀ θ, 0 ≤ w θ) (hw : Integrable w ν) (hδm : AEStronglyMeasurable δ ν)
        (Θa : Set Θ) (hΘa : MeasurableSet Θa) {Δ ρ : ℝ}
        (hΔ : ∀ θ ∈ Θa, δ θ ≤ Δ) (hρ : ∀ θ ∈ Θaᶜ, δ θ ≤ ρ)
        {M0 : ℝ} (hM0 : 0 ≤ M0)
        (hFb : ∀ θ, ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ w θ * M0),
        ‖⟪evol ((N : ℂ) • C0N ν Φ F) 1 φ, J (evol ((N : ℂ) • C0N ν Φ F) 1 φ)⟫_ℂ -
          ⟪evol ((N : ℂ) • LN ν Φ F b) 1 φ, J (evol ((N : ℂ) • LN ν Φ F b) 1 φ)⟫_ℂ‖ ≤
          (C0 * (C1 * M0)) * (Δ * (∫ θ in Θa, w θ ∂ν) + ρ * (∫ θ in Θaᶜ, w θ ∂ν)) * CJ := by
  obtain ⟨m, C0, hm, hC0, hmain⟩ := prop026_linearization d
  refine ⟨m, C0, hm, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨C1, hC1, hC1b⟩ := hmain hU hQ hQU
  refine ⟨C1, hC1, fun {Θ} _ ν _ {K} _ {H} _ _ _ Φ F hF b hKQ hbQ hcomm hB hFm hdF N hN φ hφ δ hδ hφδ
    J {CJ} hCJ hJ w hw0 hw hδm Θa hΘa {Δ ρ} hΔ hρ {M0} hM0 hFb => ?_⟩
  -- δ is bounded, hence `w δ` is integrable
  have hwδ : Integrable (fun θ => w θ * δ θ) ν := by
    have hb : ∀ θ, δ θ ≤ max Δ ρ := fun θ => by
      by_cases h : θ ∈ Θa
      · exact (hΔ θ h).trans (le_max_left _ _)
      · exact (hρ θ h).trans (le_max_right _ _)
    refine (hw.mul_const (max Δ ρ)).mono' ?_ (ae_of_all _ fun θ => ?_)
    · exact hw.aestronglyMeasurable.mul hδm
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 θ) (hδ θ))]
      exact mul_le_mul_of_nonneg_left (hb θ) (hw0 θ)
  have h1 := hC1b ν Φ F hF b hKQ hbQ hcomm hB hFm hdF N hN φ hφ δ hδ hφδ J hCJ hJ w hw0 hw hwδ hM0 hFb
  refine h1.trans ?_
  have hsplit : ∫ θ, w θ * δ θ ∂ν =
      (∫ θ in Θa, w θ * δ θ ∂ν) + ∫ θ in Θaᶜ, w θ * δ θ ∂ν :=
    (integral_add_compl hΘa hwδ).symm
  have hA : ∫ θ in Θa, w θ * δ θ ∂ν ≤ Δ * ∫ θ in Θa, w θ ∂ν := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hwδ.integrableOn) ((hw.integrableOn).const_mul Δ) hΘa fun θ hθ => ?_
    calc w θ * δ θ ≤ w θ * Δ := mul_le_mul_of_nonneg_left (hΔ θ hθ) (hw0 θ)
      _ = Δ * w θ := mul_comm _ _
  have hB' : ∫ θ in Θaᶜ, w θ * δ θ ∂ν ≤ ρ * ∫ θ in Θaᶜ, w θ ∂ν := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hwδ.integrableOn) ((hw.integrableOn).const_mul ρ) hΘa.compl fun θ hθ => ?_
    calc w θ * δ θ ≤ w θ * ρ := mul_le_mul_of_nonneg_left (hρ θ hθ) (hw0 θ)
      _ = ρ * w θ := mul_comm _ _
  have hk : 0 ≤ C0 * (C1 * M0) := mul_nonneg hC0 (mul_nonneg hC1 hM0)
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hA hB') hk) hCJ

end Prop026

end QuantumNLS.FunctionalLinearization

#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param_weighted
#print axioms QuantumNLS.FunctionalLinearization.integrable_apply_comp_w
#print axioms QuantumNLS.FunctionalLinearization.integrable_sum_smul_coord_w
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param_core_weighted
#print axioms QuantumNLS.FunctionalLinearization.prop026_linearization
#print axioms QuantumNLS.FunctionalLinearization.prop026_split
