import QuantumNLS.DiagonalMultiplierFull
/-! integrator-authored trusted spec for R-09DDF6D2 lem:multiplier (DYNAMICS_LEMMAS.tex:271), under VERIFIED SCOPED OWNER
APPROVAL scope (3). DOCUMENTED RESTRICTION: "off a discarded domain whose contribution vanishes or on which T_N = 0" is
formalized ONLY as: vanishing discarded probability (discProb E_N ψ_N → 0) together with a uniform operator bound
(‖T_N φ‖ ≤ Cop‖φ‖), OR annihilation T_N e_m = 0 for m ∈ E_N. U_N(t)e_m = e^{-itΛ_N(m)}e_m; T_N e_m = c_N(m)e_{σm} on the
admissible domain D_N (σ injective, |c| ≤ C), (D_N)ᶜ ⊆ E_N; static residual → 0; gap law on D∖E. Conclusions: sup over
|t| ≤ T of ‖(T_N − e^{itδ}τ)U_N(t)ψ_N‖ → 0; the τ = 0 / T*T-diagonal clause; norm-close preparations. -/
namespace R09DDSpec
open QuantumNLS QuantumNLS.DiagonalMultiplier QuantumNLS.DiagonalMultiplierFull Filter Topology

theorem defs (ι : Type*) [DecidableEq ι] :
    (∀ (Λ : ι → ℝ) (t : ℝ) (m : ι), phase Λ t m = Complex.exp (-(((t * Λ m : ℝ) : ℂ)) * Complex.I)) ∧
    (∀ m : ι, e m = lp.single 2 m (1 : ℂ)) ∧
    (∀ (T : L2 ι →L[ℂ] L2 ι) (τ : ℂ) (δ t : ℝ) (v : L2 ι),
      Fop T τ δ t v = T v - (Complex.exp (((t * δ : ℝ) : ℂ) * Complex.I) * τ) • v) ∧
    (∀ (E : Set ι) (ψ : L2 ι), discProb E ψ = ∑' m, E.indicator (fun m => ‖ψ m‖ ^ 2) m) ∧
    (∀ (Λ : ι → ℝ) (σ : ι → ι) (D E : Set ι) (δ η : ℝ) (ψ : L2 ι), badProb Λ σ D E δ η ψ =
      ∑' m, {m | m ∈ D ∧ m ∉ E ∧ η < |Λ (σ m) - Λ m - δ|}.indicator (fun m => ‖ψ m‖ ^ 2) m) :=
  ⟨fun _ _ _ => rfl, fun _ => rfl, fun T τ δ t v => Fop_apply T τ δ t v, fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

theorem spec (ι : Type*) [DecidableEq ι] :
    (∀ (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (σ : ι → ι) (D : ℕ → Set ι) (hinj : ∀ N, Set.InjOn σ (D N))
    (c : ℕ → ι → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ N, ∀ m ∈ D N, ‖c N m‖ ≤ C)
    (T : ℕ → L2 ι →L[ℂ] L2 ι) (Cop : ℝ) (hCop0 : 0 ≤ Cop)
    (hTb : ∀ N φ, ‖T N φ‖ ≤ Cop * ‖φ‖)
    (hT : ∀ N, ∀ m ∈ D N, T N (e m) = c N m • e (σ m))
    (ψ : ℕ → L2 ι) (hψ : ∀ N, ‖ψ N‖ = 1) (τ : ℂ) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - τ • ψ N‖) atTop (𝓝 0))
    (E : ℕ → Set ι) (hDE : ∀ N, (D N)ᶜ ⊆ E N)
    (hgap : ∀ η > 0, Tendsto (fun N => badProb (Λ N) σ (D N) (E N) δ η (ψ N)) atTop (𝓝 0))
    (hdisc : Tendsto (fun N => discProb (E N) (ψ N)) atTop (𝓝 0) ∨
      ∀ N, ∀ m ∈ E N, T N (e m) = 0)
    (Tmax : ℝ),
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ N))‖)
      atTop (𝓝 0) ) ∧
    (∀ (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (T : ℕ → L2 ι →L[ℂ] L2 ι)
    (hdiag : ∀ N m, ∃ l : ℂ, ContinuousLinearMap.adjoint (T N) (T N (e m)) = l • e m)
    (ψ : ℕ → L2 ι) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - (0 : ℂ) • ψ N‖) atTop (𝓝 0)) (Tmax : ℝ),
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) 0 δ t (U N t (ψ N))‖)
      atTop (𝓝 0) ) ∧
    (∀ (Λ : ℕ → ι → ℝ) (U : ℕ → ℝ → L2 ι →L[ℂ] L2 ι)
    (hU : ∀ N t m, U N t (e m) = phase (Λ N) t m • e m)
    (σ : ι → ι) (D : ℕ → Set ι) (hinj : ∀ N, Set.InjOn σ (D N))
    (c : ℕ → ι → ℂ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ N, ∀ m ∈ D N, ‖c N m‖ ≤ C)
    (T : ℕ → L2 ι →L[ℂ] L2 ι) (Cop : ℝ) (hCop0 : 0 ≤ Cop)
    (hTb : ∀ N φ, ‖T N φ‖ ≤ Cop * ‖φ‖)
    (hT : ∀ N, ∀ m ∈ D N, T N (e m) = c N m • e (σ m))
    (ψ : ℕ → L2 ι) (hψ : ∀ N, ‖ψ N‖ = 1) (τ : ℂ) (δ : ℝ)
    (hstat : Tendsto (fun N => ‖T N (ψ N) - τ • ψ N‖) atTop (𝓝 0))
    (E : ℕ → Set ι) (hDE : ∀ N, (D N)ᶜ ⊆ E N)
    (hgap : ∀ η > 0, Tendsto (fun N => badProb (Λ N) σ (D N) (E N) δ η (ψ N)) atTop (𝓝 0))
    (hdisc : Tendsto (fun N => discProb (E N) (ψ N)) atTop (𝓝 0) ∨
      ∀ N, ∀ m ∈ E N, T N (e m) = 0)
    (Tmax : ℝ) (ψ' : ℕ → L2 ι) (hclose : Tendsto (fun N => ‖ψ' N - ψ N‖) atTop (𝓝 0)),
    Tendsto (fun N => ⨆ t : Set.Icc (-Tmax) Tmax, ‖Fop (T N) τ δ t (U N t (ψ' N))‖)
      atTop (𝓝 0) ) :=
  ⟨fun Λ U => multiplier_full Λ U, fun Λ U => multiplier_zero_diag_full Λ U, fun Λ U => multiplier_full_norm_close Λ U⟩

end R09DDSpec
#print axioms R09DDSpec.defs
#print axioms R09DDSpec.spec
