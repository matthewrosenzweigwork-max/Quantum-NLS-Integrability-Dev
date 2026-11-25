import QuantumNLS.PhysicalWickLimit

/-!
# Strong symbols of Wick operators on general unit `ℓ²` profiles (Fourier occupation realisation)

Source: `chapters/definitions.tex:171` (DEF-028: `A_N` has strong scalar symbol `a(u)` on `ψ_N` if
`‖(A_N − a(u))ψ_N‖ → 0`; uniform versions take a supremum over a profile class),
`chapters/core/wick_calculus.tex` (`thm:full-wick`: "uniform strong symbols", coherent test
`eq:full-coherent-test`, product bound `eq:full-product-bound`).

In the Fourier occupation realisation (no Bethe chart) the preparation is
`Ψ_N = U4(ξ^{⊗N})` for a unit profile `ξ ∈ ℓ²(ℤ)` (physically `ξ = û`, via `U3`), and the symbol of
`W_N(f)` is the classical value `f(ξ) = ∑ f_{αβ} ξ^α conj(ξ)^β`.  The source's Bethe chart `w(u)`
is NOT identified here.  No Bethe U5, no selected gauge; supplied gauges act by exact unitary
conjugation.
-/

namespace QuantumNLS.StrongSymbols

open QuantumNLS.Occupation QuantumNLS.WickSymbols QuantumNLS.WickBounds QuantumNLS.WickSpectralBridge
open QuantumNLS.CoherentLowerBound QuantumNLS.OccupationHilbert Filter

noncomputable section

/-! ### Adjoints of Wick monomials on the finite-support carrier -/

lemma ip_AnnProd (l : List ℤ) (u v : FS) : ip (AnnProd l u) v = ip u (CreProd l.reverse v) := by
  induction l generalizing v with
  | nil => simp [AnnProd, CreProd]
  | cons a l ih =>
    rw [AnnProd, Module.End.mul_apply, ← Cre_adjoint, ih, List.reverse_cons, CreProd_append]
    simp [CreProd]

lemma ip_CreProd_left (l : List ℤ) (u v : FS) : ip (CreProd l u) v = ip u (AnnProd l.reverse v) := by
  calc ip (CreProd l u) v = (starRingEnd ℂ) (ip v (CreProd l u)) := (ip_conj_symm (CreProd l u) v).symm
    _ = (starRingEnd ℂ) (ip (AnnProd l.reverse v) u) := by rw [ip_CreProd]
    _ = ip u (AnnProd l.reverse v) := ip_conj_symm u (AnnProd l.reverse v)

lemma AnnProd_reverse (l : List ℤ) : AnnProd l.reverse = AnnProd l :=
  AnnProd_perm (List.reverse_perm l)

/-- Adjointness of balanced Wick monomials on the finite-support carrier:
`⟨u, W_N(z^α z̄^β) v⟩ = ⟨W_N(z^β z̄^α) u, v⟩`. -/
lemma WMono_adjoint_ip (N : ℕ) {α β : ℤ →₀ ℕ} (hd : α.degree = β.degree) (u v : FS) :
    ip u (WMono N α β v) = ip (WMono N β α u) v := by
  unfold WMono CreMono AnnMono
  simp only [LinearMap.smul_apply, Module.End.mul_apply]
  rw [ip_smul_right, ip_smul_left, ip_CreProd, ip_CreProd_left, AnnProd_reverse, AnnProd_reverse]
  have : (starRingEnd ℂ) (((N : ℂ)⁻¹) ^ β.degree) = ((N : ℂ)⁻¹) ^ α.degree := by
    rw [hd]; simp [map_pow]
  rw [this]

/-- The conjugate symbol `f̄ = ∑ conj(f_{αβ}) z^β z̄^α`. -/
def conjSym (f : Sym) : Sym :=
  ∑ p ∈ f.coeff.support, (starRingEnd ℂ) (f.coeff p) • zm p.2 p.1

lemma balanced_conjSym {f : Sym} (hb : Balanced f) : Balanced (conjSym f) :=
  balanced_of_sum _ (fun p => (starRingEnd ℂ) (f.coeff p)) (fun p => p.2) (fun p => p.1)
    (fun p hp _ => (hb p hp).symm)

lemma WN_conjSym (N : ℕ) (f : Sym) :
    WN N (conjSym f) = ∑ p ∈ f.coeff.support, (starRingEnd ℂ) (f.coeff p) • WMono N p.2 p.1 := by
  unfold conjSym
  rw [map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul, WN_zm]

/-- Adjointness of balanced Wick operators on the finite-support carrier. -/
theorem WN_adjoint_ip (N : ℕ) {f : Sym} (hb : Balanced f) (u v : FS) :
    ip u (WN N f v) = ip (WN N (conjSym f) u) v := by
  have e : WN N f = ∑ p ∈ f.coeff.support, f.coeff p • WMono N p.1 p.2 := symLin_expand _ f
  rw [e, WN_conjSym, LinearMap.sum_apply, LinearMap.sum_apply, ip_sum_right, ip_sum_left]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, ip_smul_right, ip_smul_left, Complex.conj_conj,
    WMono_adjoint_ip N (hb p hp)]

lemma evalMon_swap (ξ : ℤ → ℂ) (p : Mon) :
    evalMon ξ (p.2, p.1) = (starRingEnd ℂ) (evalMon ξ p) := by
  unfold evalMon
  rw [map_mul, conj_prod_eval ξ p.1]
  have h2 := conj_prod_eval (fun a => (starRingEnd ℂ) (ξ a)) p.2
  simp only [Complex.conj_conj] at h2
  rw [h2]; ring

theorem evalSym_conjSym (ξ : ℤ → ℂ) (f : Sym) :
    evalSym ξ (conjSym f) = (starRingEnd ℂ) (evalSym ξ f) := by
  unfold conjSym
  rw [map_sum, evalSym_expand, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul, evalSym_zm, evalMon_swap, smul_eq_mul, map_mul]

/-- **Hilbert adjoint**: `W_N(f̄) = W_N(f)^*` on `ℓ²(𝓜_N)` (`N ≥ 1`, balanced `f`). -/
theorem WHil_adjoint {N : ℕ} (hN : 0 < N) {f : Sym} (hb : Balanced f) (x y : H N) :
    inner ℂ (WHil N (conjSym f) x) y = inner ℂ x (WHil N f y) := by
  have hb' := balanced_conjSym hb
  refine (core_dense N).induction_on₂ (p := fun x y => inner ℂ (WHil N (conjSym f) x) y
    = inner ℂ x (WHil N f y)) ?_ ?_ x y
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro u v
    rw [WHil_core hN hb', WHil_core hN hb, inner_core, inner_core]
    unfold ipS
    rw [emb_WS hb', emb_WS hb]
    exact (WN_adjoint_ip N hb (emb N u) (emb N v)).symm

/-! ### The exact coherent expectation for every unit profile (finite-support approximation) -/

open QuantumNLS.TensorCarrier in
/-- `U4(ξ^{⊗N})`: the occupation image of the actual completed tensor power. -/
def Psi (N : ℕ) (ξ : OccupationUnitary.OneParticle) : H N :=
  OccupationUnitary.U4 N ⟨htpow N ξ, htpow_mem_symSector N ξ⟩

open QuantumNLS.TensorCarrier in
lemma continuous_Psi (N : ℕ) : Continuous (Psi N) := by
  unfold Psi
  refine (OccupationUnitary.U4 N).continuous.comp (Continuous.subtype_mk ?_ _)
  have : Continuous (fun ξ : OccupationUnitary.OneParticle =>
      OccupationUnitary.tensorMultilinear N (fun _ => ξ)) :=
    (OccupationUnitary.tensorMultilinear N).cont.comp (continuous_pi fun _ => continuous_id)
  exact this

lemma continuous_coord (a : ℤ) : Continuous (fun ξ : OccupationUnitary.OneParticle => (ξ : ℤ → ℂ) a) :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 a).continuous

lemma continuous_evalMon (p : Mon) :
    Continuous (fun ξ : OccupationUnitary.OneParticle => evalMon (ξ : ℤ → ℂ) p) := by
  unfold evalMon Finsupp.prod
  refine Continuous.mul (continuous_finsetProd _ (fun a _ => (continuous_coord a).pow _))
    (continuous_finsetProd _ (fun a _ => (Complex.continuous_conj.comp (continuous_coord a)).pow _))

/-- Ratio `(N)_d / N^d`. -/
def ratio (N d : ℕ) : ℝ := (fall N d : ℝ) / (N : ℝ) ^ d

/-- The closed form of the coherent expectation of `W_N(f)`. -/
def Gexp (N : ℕ) (f : Sym) (ξ : ℤ → ℂ) : ℂ :=
  ∑ p ∈ f.coeff.support, f.coeff p * (((ratio N p.1.degree : ℝ) : ℂ) * evalMon ξ p)

lemma continuous_Gexp (N : ℕ) (f : Sym) :
    Continuous (fun ξ : OccupationUnitary.OneParticle => Gexp N f (ξ : ℤ → ℂ)) := by
  unfold Gexp
  exact continuous_finsetSum _ (fun p _ => continuous_const.mul (continuous_const.mul (continuous_evalMon p)))

open QuantumNLS.PhysicalWickLimit in
/-- Exact expectation for finitely supported unit profiles (`coh_expect_poly`). -/
theorem expectation_finite {N : ℕ} (hN : 0 < N) {f : Sym} (hb : Balanced f)
    (η : OccupationUnitary.OneParticle) (hfin : (Function.support (η : ℤ → ℂ)).Finite)
    (h1 : ‖η‖ = 1) :
    inner ℂ (Psi N η) (WHil N f (Psi N η)) = Gexp N f (η : ℤ → ℂ) := by
  have e : Psi N η = core N (cohSector hfin N) := (core_cohSector η hfin N).symm
  rw [e, inner_core_WHil hN hb, emb_cohSector]
  exact coh_expect_poly hfin (coh_ip_self η hfin h1) hb N

/-- Finite truncations of a profile, renormalised. -/
def trunc (ξ : OccupationUnitary.OneParticle) (S : Finset ℤ) : OccupationUnitary.OneParticle :=
  ∑ a ∈ S, lp.single 2 a (ξ a)

lemma trunc_apply (ξ : OccupationUnitary.OneParticle) (S : Finset ℤ) (b : ℤ) :
    (trunc ξ S : ℤ → ℂ) b = if b ∈ S then ξ b else 0 := by
  classical
  unfold trunc
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp [lp.single_apply]

/-- **Exact coherent expectation for every unit profile `ξ ∈ ℓ²(ℤ)`** (finite-support approximation
at fixed `N`, both sides continuous in `ξ`):
`⟨U4(ξ^{⊗N}), W_N(f) U4(ξ^{⊗N})⟩ = ∑_p f_p ((N)_d/N^d) ξ^α conj(ξ)^β`. -/
theorem expectation_unit {N : ℕ} (hN : 0 < N) {f : Sym} (hb : Balanced f)
    (ξ : OccupationUnitary.OneParticle) (h1 : ‖ξ‖ = 1) :
    inner ℂ (Psi N ξ) (WHil N f (Psi N ξ)) = Gexp N f (ξ : ℤ → ℂ) := by
  classical
  have hS : Tendsto (fun S : Finset ℤ => trunc ξ S) atTop (nhds ξ) :=
    lp.hasSum_single (by norm_num) ξ
  have hnorm : Tendsto (fun S : Finset ℤ => ‖trunc ξ S‖) atTop (nhds 1) := by
    simpa [h1] using hS.norm
  have hpos : ∀ᶠ S : Finset ℤ in atTop, 0 < ‖trunc ξ S‖ :=
    hnorm.eventually (lt_mem_nhds (by norm_num))
  set η : Finset ℤ → OccupationUnitary.OneParticle :=
    fun S => (((‖trunc ξ S‖⁻¹ : ℝ)) : ℂ) • trunc ξ S with hη
  have hηlim : Tendsto η atTop (nhds ξ) := by
    have h0 : Tendsto (fun S : Finset ℤ => (((‖trunc ξ S‖⁻¹ : ℝ)) : ℂ)) atTop (nhds 1) := by
      have h2 := hnorm.inv₀ one_ne_zero
      rw [inv_one] at h2
      have := (Complex.continuous_ofReal.tendsto 1).comp h2
      rw [Complex.ofReal_one] at this
      exact this
    simpa [hη, Complex.ofReal_inv] using h0.smul hS
  have hF : Tendsto (fun S => inner ℂ (Psi N (η S)) (WHil N f (Psi N (η S)))) atTop
      (nhds (inner ℂ (Psi N ξ) (WHil N f (Psi N ξ)))) := by
    have hc : Continuous (fun x : OccupationUnitary.OneParticle =>
        inner ℂ (Psi N x) (WHil N f (Psi N x))) :=
      (continuous_Psi N).inner ((WHil N f).continuous.comp (continuous_Psi N))
    exact (hc.tendsto ξ).comp hηlim
  have hG : Tendsto (fun S => Gexp N f ((η S : OccupationUnitary.OneParticle) : ℤ → ℂ)) atTop
      (nhds (Gexp N f (ξ : ℤ → ℂ))) :=
    ((continuous_Gexp N f).tendsto ξ).comp hηlim
  refine tendsto_nhds_unique_of_eventuallyEq hF hG ?_
  filter_upwards [hpos] with S hS0
  have hfin : (Function.support ((η S : OccupationUnitary.OneParticle) : ℤ → ℂ)).Finite := by
    refine (Finset.finite_toSet S).subset ?_
    intro b hb
    by_contra hbS
    have hbS' : b ∉ S := by simpa using hbS
    apply hb
    simp [hη, lp.coeFn_smul, trunc_apply, hbS']
  have hu : ‖η S‖ = 1 := by
    simp only [hη, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hS0.ne'
  exact expectation_finite hN hb (η S) hfin hu

/-! ### Uniform (profile-independent) bounds -/

lemma norm_coord_le (ξ : OccupationUnitary.OneParticle) (h1 : ‖ξ‖ = 1) (a : ℤ) :
    ‖(ξ : ℤ → ℂ) a‖ ≤ 1 := by
  have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) ξ a
  rwa [h1] at this

lemma norm_evalMon_le (ξ : OccupationUnitary.OneParticle) (h1 : ‖ξ‖ = 1) (p : Mon) :
    ‖evalMon (ξ : ℤ → ℂ) p‖ ≤ 1 := by
  unfold evalMon
  rw [norm_mul]
  have hprod : ∀ (g : ℤ → ℂ) (m : ℤ →₀ ℕ), (∀ a, ‖g a‖ ≤ 1) →
      ‖m.prod (fun a k => g a ^ k)‖ ≤ 1 := by
    intro g m hg
    unfold Finsupp.prod
    rw [norm_prod]
    calc ∏ a ∈ m.support, ‖g a ^ m a‖ ≤ ∏ _a ∈ m.support, (1 : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            (fun a _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hg a))
      _ = 1 := by simp
  have h1' := hprod (ξ : ℤ → ℂ) p.1 (norm_coord_le ξ h1)
  have h2' := hprod (fun a => (starRingEnd ℂ) ((ξ : ℤ → ℂ) a)) p.2
    (fun a => by simpa using norm_coord_le ξ h1 a)
  calc ‖∏ a ∈ p.1.support, (ξ : ℤ → ℂ) a ^ p.1 a‖ * ‖∏ a ∈ p.2.support, (starRingEnd ℂ) ((ξ : ℤ → ℂ) a) ^ p.2 a‖
      ≤ 1 * 1 := mul_le_mul h1' h2' (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- `‖f(ξ)‖ ≤ ‖f‖_coeff` for every unit profile. -/
lemma norm_evalSym_le (ξ : OccupationUnitary.OneParticle) (h1 : ‖ξ‖ = 1) (f : Sym) :
    ‖evalSym (ξ : ℤ → ℂ) f‖ ≤ coeffNorm f := by
  rw [evalSym_expand]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
  rw [norm_mul]
  calc ‖f.coeff p‖ * ‖evalMon (ξ : ℤ → ℂ) p‖ ≤ ‖f.coeff p‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_evalMon_le ξ h1 p) (norm_nonneg _)
    _ = ‖f.coeff p‖ := mul_one _

/-- Profile-independent error of the coherent expectation. -/
def delta (N : ℕ) (f : Sym) : ℝ :=
  ∑ p ∈ f.coeff.support, ‖f.coeff p‖ * |ratio N p.1.degree - 1|

lemma delta_nonneg (N : ℕ) (f : Sym) : 0 ≤ delta N f :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (abs_nonneg _))

theorem delta_tendsto (f : Sym) : Tendsto (fun N => delta N f) atTop (nhds 0) := by
  unfold delta
  have : (0 : ℝ) = ∑ p ∈ f.coeff.support, ‖f.coeff p‖ * 0 := by simp
  rw [this]
  refine tendsto_finsetSum _ (fun p _ => ?_)
  refine Tendsto.const_mul _ ?_
  have h := (fall_ratio_tendsto p.1.degree).sub_const 1
  simpa [ratio] using h.abs

/-- **Uniform expectation error**: for every unit profile, `N ≥ 1`, balanced `f`,
`|⟨U4(ξ^{⊗N}), W_N(f) U4(ξ^{⊗N})⟩ − f(ξ)| ≤ δ_N(f)`, with `δ_N(f) → 0` independent of `ξ`. -/
theorem expectation_error {N : ℕ} (hN : 0 < N) {f : Sym} (hb : Balanced f)
    (ξ : OccupationUnitary.OneParticle) (h1 : ‖ξ‖ = 1) :
    ‖inner ℂ (Psi N ξ) (WHil N f (Psi N ξ)) - evalSym (ξ : ℤ → ℂ) f‖ ≤ delta N f := by
  rw [expectation_unit hN hb ξ h1, evalSym_expand]
  unfold Gexp delta
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
  have : f.coeff p * (((ratio N p.1.degree : ℝ) : ℂ) * evalMon (ξ : ℤ → ℂ) p)
      - f.coeff p * evalMon (ξ : ℤ → ℂ) p
      = f.coeff p * ((((ratio N p.1.degree - 1 : ℝ)) : ℂ) * evalMon (ξ : ℤ → ℂ) p) := by
    push_cast; ring
  rw [this, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖f.coeff p‖ * (|ratio N p.1.degree - 1| * ‖evalMon (ξ : ℤ → ℂ) p‖)
      ≤ ‖f.coeff p‖ * (|ratio N p.1.degree - 1| * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_evalMon_le ξ h1 p)
          (abs_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

lemma norm_Psi (N : ℕ) (ξ : OccupationUnitary.OneParticle) : ‖Psi N ξ‖ = ‖ξ‖ ^ N := by
  unfold Psi
  rw [LinearIsometryEquiv.norm_map]
  exact QuantumNLS.TensorCarrier.norm_htpow N ξ

/-! ### True strong norm convergence on every unit profile -/

/-- Exact residual identity: with `W = W_N(f)`, `W̃ = W_N(f̄) = W^*`, `a = ⟨Ψ,WΨ⟩`,
`b = ⟨Ψ, W̃ W Ψ⟩`:  `‖WΨ − cΨ‖² = b̄ − c ā − c̄ a + c̄ c` (unit `Ψ`). -/
lemma residual_identity {N : ℕ} (hN : 0 < N) {f : Sym} (hb : Balanced f) (Ψ : H N) (hΨ : ‖Ψ‖ = 1)
    (c : ℂ) :
    ((‖WHil N f Ψ - c • Ψ‖ : ℝ) : ℂ) ^ 2
      = (starRingEnd ℂ) (inner ℂ Ψ (WHil N (conjSym f) (WHil N f Ψ)))
        - c * (starRingEnd ℂ) (inner ℂ Ψ (WHil N f Ψ))
        - (starRingEnd ℂ) c * inner ℂ Ψ (WHil N f Ψ) + (starRingEnd ℂ) c * c := by
  set X := WHil N f Ψ with hX
  have h0 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (X - c • Ψ)
  have hXX : inner ℂ X X = (starRingEnd ℂ) (inner ℂ Ψ (WHil N (conjSym f) X)) := by
    rw [inner_conj_symm, WHil_adjoint hN hb X Ψ]
  have hXΨ : inner ℂ X Ψ = (starRingEnd ℂ) (inner ℂ Ψ X) := (inner_conj_symm X Ψ).symm
  have hΨΨ : inner ℂ Ψ Ψ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΨ]; simp
  have e : inner ℂ (X - c • Ψ) (X - c • Ψ)
      = inner ℂ X X - c * inner ℂ X Ψ - (starRingEnd ℂ) c * inner ℂ Ψ X
        + (starRingEnd ℂ) c * (c * inner ℂ Ψ Ψ) := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    ring
  have h0' : ((‖X - c • Ψ‖ : ℝ) : ℂ) ^ 2 = inner ℂ (X - c • Ψ) (X - c • Ψ) := h0.symm
  rw [h0', e, hXX, hXΨ, hΨΨ]
  ring

/-- The profile-independent bound for the squared strong residual. -/
def strongBound (N : ℕ) (f : Sym) : ℝ :=
  Cfg (conjSym f) f * ((N : ℝ)⁻¹) ^ 2
    + coeffNorm (S1 (labelsOf (conjSym f)) (conjSym f) f
        + (Complex.I / 2) • pb (labelsOf (conjSym f)) (conjSym f) f) * (N : ℝ)⁻¹
    + delta N (conjSym f * f) + 2 * coeffNorm f * delta N f

/-- **Strong residual bound** (DEF-028, `thm:full-wick`), for EVERY unit profile `ξ ∈ ℓ²(ℤ)`:
`‖W_N(f)Ψ_N − f(ξ)Ψ_N‖² ≤ η_N(f)` with `Ψ_N = U4(ξ^{⊗N})` and `η_N(f)` independent of `ξ`. -/
theorem strong_residual_sq_le {N : ℕ} (hN : 0 < N) {f : Sym} (hb : Balanced f)
    (ξ : OccupationUnitary.OneParticle) (h1 : ‖ξ‖ = 1) :
    ‖WHil N f (Psi N ξ) - (evalSym (ξ : ℤ → ℂ) f) • Psi N ξ‖ ^ 2 ≤ strongBound N f := by
  have hΨ : ‖Psi N ξ‖ = 1 := by rw [norm_Psi, h1, one_pow]
  have hfb := balanced_conjSym hb
  have hg : Balanced (conjSym f * f) := Balanced.mul hfb hb
  set S := labelsOf (conjSym f) with hS
  set q' : Sym := S1 S (conjSym f) f + (Complex.I / 2) • pb S (conjSym f) f with hq'
  have hq'b : Balanced q' := balanced_add (balanced_S1 S hfb hb) (balanced_smul _ (balanced_pb S hfb hb))
  set c := evalSym (ξ : ℤ → ℂ) f with hc
  set Ψ := Psi N ξ with hΨdef
  set a := inner ℂ Ψ (WHil N f Ψ) with ha
  set bb := inner ℂ Ψ (WHil N (conjSym f) (WHil N f Ψ)) with hbb
  set e := inner ℂ Ψ (WHil N (conjSym f * f) Ψ) with he
  have hid := residual_identity hN hb Ψ hΨ c
  have h_a : ‖a - c‖ ≤ delta N f := expectation_error hN hb ξ h1
  have hegc : evalSym (ξ : ℤ → ℂ) (conjSym f * f) = (starRingEnd ℂ) c * c := by
    rw [evalSym_mul, evalSym_conjSym]
  have h_e : ‖e - (starRingEnd ℂ) c * c‖ ≤ delta N (conjSym f * f) := by
    have := expectation_error hN hg ξ h1
    rwa [hegc] at this
  -- b - e
  have h_be : ‖bb - e‖ ≤ Cfg (conjSym f) f * ((N : ℝ)⁻¹) ^ 2 + coeffNorm q' * (N : ℝ)⁻¹ := by
    have hD := hilbert_product_bound hN hfb hb (S := S) le_rfl
    have hsplit : WHil N (conjSym f) * WHil N f - WHil N (conjSym f * f)
        = (WHil N (conjSym f) * WHil N f - WHil N (conjSym f * f) - (N : ℂ)⁻¹ • WHil N q')
          + (N : ℂ)⁻¹ • WHil N q' := by rw [sub_add_cancel]
    have hop : ‖WHil N (conjSym f) * WHil N f - WHil N (conjSym f * f)‖
        ≤ Cfg (conjSym f) f * ((N : ℝ)⁻¹) ^ 2 + coeffNorm q' * (N : ℝ)⁻¹ := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add hD ?_)
      rw [norm_smul]
      have hn : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by simp
      rw [hn, mul_comm]
      exact mul_le_mul_of_nonneg_right (WHil_norm_le hN hq'b) (by positivity)
    have hdiff : bb - e = inner ℂ Ψ ((WHil N (conjSym f) * WHil N f - WHil N (conjSym f * f)) Ψ) := by
      rw [hbb, he, ← inner_sub_right]; rfl
    rw [hdiff]
    calc _ ≤ ‖Ψ‖ * ‖(WHil N (conjSym f) * WHil N f - WHil N (conjSym f * f)) Ψ‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖Ψ‖ * (‖WHil N (conjSym f) * WHil N f - WHil N (conjSym f * f)‖ * ‖Ψ‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖WHil N (conjSym f) * WHil N f - WHil N (conjSym f * f)‖ := by rw [hΨ]; ring
      _ ≤ _ := hop
  have hcn : ‖c‖ ≤ coeffNorm f := norm_evalSym_le ξ h1 f
  -- the right-hand side of the residual identity
  have hrhs : (starRingEnd ℂ) bb - c * (starRingEnd ℂ) a - (starRingEnd ℂ) c * a + (starRingEnd ℂ) c * c
      = (starRingEnd ℂ) (bb - (starRingEnd ℂ) c * c) - c * (starRingEnd ℂ) (a - c)
        - (starRingEnd ℂ) c * (a - c) := by
    simp only [map_sub, map_mul, Complex.conj_conj]; ring
  have hR : ‖WHil N f Ψ - c • Ψ‖ ^ 2 ≤ ‖bb - (starRingEnd ℂ) c * c‖ + 2 * (‖c‖ * ‖a - c‖) := by
    have : ‖WHil N f Ψ - c • Ψ‖ ^ 2 = ‖((‖WHil N f Ψ - c • Ψ‖ : ℝ) : ℂ) ^ 2‖ := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [this, hid, hrhs]
    refine (norm_sub_le _ _).trans ?_
    have h1' : ‖(starRingEnd ℂ) (bb - (starRingEnd ℂ) c * c) - c * (starRingEnd ℂ) (a - c)‖
        ≤ ‖bb - (starRingEnd ℂ) c * c‖ + ‖c‖ * ‖a - c‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [RCLike.norm_conj, norm_mul, RCLike.norm_conj]
    have h2' : ‖(starRingEnd ℂ) c * (a - c)‖ = ‖c‖ * ‖a - c‖ := by
      rw [norm_mul, RCLike.norm_conj]
    linarith
  have hbc : ‖bb - (starRingEnd ℂ) c * c‖ ≤ ‖bb - e‖ + ‖e - (starRingEnd ℂ) c * c‖ := by
    have : bb - (starRingEnd ℂ) c * c = (bb - e) + (e - (starRingEnd ℂ) c * c) := by ring
    rw [this]; exact norm_add_le _ _
  have hca : ‖c‖ * ‖a - c‖ ≤ coeffNorm f * delta N f :=
    mul_le_mul hcn h_a (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  unfold strongBound
  linarith

lemma strongBound_tendsto (f : Sym) : Tendsto (fun N => strongBound N f) atTop (nhds 0) := by
  have h0 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ 2) atTop (nhds 0) := by
    simpa using h0.pow 2
  set K : ℝ := coeffNorm (S1 (labelsOf (conjSym f)) (conjSym f) f
        + (Complex.I / 2) • pb (labelsOf (conjSym f)) (conjSym f) f) with hK
  have := (((h2.const_mul (Cfg (conjSym f) f)).add (h0.const_mul K)).add
    (delta_tendsto (conjSym f * f))).add ((delta_tendsto f).const_mul (2 * coeffNorm f))
  simpa [strongBound, hK] using this

/-- **Strong norm convergence on every unit `ℓ²` profile** (DEF-028 strong scalar symbol; source
`thm:full-wick`): for balanced `f` and unit `ξ ∈ ℓ²(ℤ)`,
`‖W_N(f) U4(ξ^{⊗N}) − f(ξ) U4(ξ^{⊗N})‖ → 0`. -/
theorem strong_symbol_tendsto {f : Sym} (hb : Balanced f) (ξ : OccupationUnitary.OneParticle)
    (h1 : ‖ξ‖ = 1) :
    Tendsto (fun N => ‖WHil N f (Psi N ξ) - (evalSym (ξ : ℤ → ℂ) f) • Psi N ξ‖) atTop (nhds 0) := by
  have hs : Tendsto (fun N => Real.sqrt (strongBound N f)) atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (strongBound_tendsto f)
    rw [Real.sqrt_zero] at this
    exact this
  refine squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) ?_ hs
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  exact Real.le_sqrt_of_sq_le (strong_residual_sq_le hN hb ξ h1)

/-- **Uniform strong symbol over ALL unit profiles**: the residual tends to `0` uniformly in `ξ`
(no regularity class is needed in the Fourier occupation realisation). -/
theorem strong_symbol_uniform {f : Sym} (hb : Balanced f) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ξ : OccupationUnitary.OneParticle, ‖ξ‖ = 1 →
      ‖WHil N f (Psi N ξ) - (evalSym (ξ : ℤ → ℂ) f) • Psi N ξ‖ ≤ ε := by
  have hev : ∀ᶠ N in atTop, strongBound N f < ε ^ 2 :=
    (strongBound_tendsto f).eventually (gt_mem_nhds (by positivity))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hev.and (Filter.eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN ξ h1 => ?_⟩
  obtain ⟨hlt, hge⟩ := hN₀ N hN
  have := strong_residual_sq_le hge hb ξ h1
  exact (sq_le_sq₀ (norm_nonneg _) hε.le).mp (this.trans hlt.le)

/-! ### Supplied gauges and the physical Fourier sector -/

lemma gauge_norm_eq (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (x : H N) :
    ‖gauge N q hq x‖ = ‖x‖ := by
  apply le_antisymm
  · calc ‖gauge N q hq x‖ ≤ ‖gauge N q hq‖ * ‖x‖ := (gauge N q hq).le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (gauge_norm_le N q hq) (norm_nonneg _)
      _ = ‖x‖ := one_mul _
  · have h : gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) (gauge N q hq x) = x := by
      have := congrArg (fun A => A x) (gauge_conj_mul N q hq)
      simpa using this
    calc ‖x‖ = ‖gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) (gauge N q hq x)‖ := by
          rw [h]
      _ ≤ ‖gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq)‖ * ‖gauge N q hq x‖ :=
          (gauge N _ _).le_opNorm _
      _ ≤ 1 * ‖gauge N q hq x‖ :=
          mul_le_mul_of_nonneg_right (gauge_norm_le N _ _) (norm_nonneg _)
      _ = ‖gauge N q hq x‖ := one_mul _

/-- **Supplied-gauge strong residual**: on the inverse-gauge preparation
`Φ = G_{q̄} U4(ξ^{⊗N})`, the gauged Wick operator `W^q_N(f)` has exactly the residual of the
ungauged one (norm preserved). No selected gauge. -/
theorem strong_residual_gauged {N : ℕ} (q : Occ → ℂ) (hq : UnitGauge q) (f : Sym) (c : ℂ)
    (Ψ : H N) :
    ‖WHilq N q hq f (gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) Ψ)
        - c • gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) Ψ‖
      = ‖WHil N f Ψ - c • Ψ‖ := by
  have h : gauge N q hq (gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) Ψ) = Ψ := by
    have := congrArg (fun A => A Ψ) (gauge_mul_conj N q hq)
    simpa using this
  have e : WHilq N q hq f (gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) Ψ)
      - c • gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) Ψ
      = gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) (WHil N f Ψ - c • Ψ) := by
    unfold WHilq
    simp only [mul_apply_eq_comp, h, map_sub, map_smul]
  rw [e, gauge_norm_eq]

open QuantumNLS.PhysicalWickLimit QuantumNLS.PhysicalTensor QuantumNLS.OccupationUnitary
  QuantumNLS.GaugeTransport in
/-- The physical product state `u^{⊗N}` has occupation image `U4(û^{⊗N})`, `û = F u`. -/
theorem physicalOccupation_productState_Psi (L : ℝ) [Fact (0 < L)] (N : ℕ) (u : L2T L) :
    physicalOccupation L N (productState L N u) = Psi N (QuantumNLS.Fourier.fourierL2 L u) := by
  unfold physicalOccupation productState Psi
  rw [LinearIsometryEquiv.trans_apply, TensorFourier.U3_htpow]

open QuantumNLS.PhysicalWickLimit QuantumNLS.PhysicalTensor QuantumNLS.OccupationUnitary
  QuantumNLS.GaugeTransport in
/-- **Strong symbol on the physical Fourier sector** (DEF-028 on `Sym^N L²(𝕋_L)`): for every unit
`u ∈ L²(𝕋_L)` and balanced `f`, `‖J_N^*W_N(f)J_N u^{⊗N} − f(û) u^{⊗N}‖ → 0` where the physical
Wick operator is the transported Hilbert Wick operator (Fourier occupation realisation; no Bethe
`J_N`, no U5). -/
theorem strong_symbol_physical (L : ℝ) [Fact (0 < L)] {f : Sym} (hb : Balanced f) (u : L2T L)
    (hu : ‖u‖ = 1) :
    Tendsto (fun N => ‖physicalWick L N f (productState L N u)
        - (evalSym ((QuantumNLS.Fourier.fourierL2 L u : OccupationUnitary.OneParticle) : ℤ → ℂ) f)
            • productState L N u‖) atTop (nhds 0) := by
  have hξ : ‖QuantumNLS.Fourier.fourierL2 L u‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hu]
  refine (strong_symbol_tendsto hb _ hξ).congr (fun N => ?_)
  rw [← (physicalOccupation L N).norm_map, map_sub, map_smul, physicalOccupation_physicalWick,
    physicalOccupation_productState_Psi]

open QuantumNLS.PhysicalWickLimit QuantumNLS.PhysicalTensor QuantumNLS.OccupationUnitary
  QuantumNLS.GaugeTransport in
/-- Supplied phases on the physical sector: on the preparation `P_q^{-1} u^{⊗N}` the rephased
physical Wick operator has the same residual (exact norm preservation). -/
theorem strong_residual_physicalQ (L : ℝ) [Fact (0 < L)] (N : ℕ) (q : Arr N → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) (f : Sym) (c : ℂ) (Φ : physSector L N) :
    ‖physicalWickQ L N q hq f ((physicalPhase L N q hq).symm Φ) - c • (physicalPhase L N q hq).symm Φ‖
      = ‖physicalWick L N f Φ - c • Φ‖ := by
  have e : physicalWickQ L N q hq f ((physicalPhase L N q hq).symm Φ)
      - c • (physicalPhase L N q hq).symm Φ
      = (physicalPhase L N q hq).symm (physicalWick L N f Φ - c • Φ) := by
    simp [physicalWickQ, map_sub, map_smul]
  rw [e, LinearIsometryEquiv.norm_map]

/-! Axiom audit (printed at compile time). -/
#print axioms norm_evalMon_le
#print axioms delta_tendsto
#print axioms expectation_unit
#print axioms expectation_error
#print axioms residual_identity
#print axioms strong_residual_sq_le
#print axioms strongBound_tendsto
#print axioms strong_symbol_tendsto
#print axioms strong_symbol_uniform
#print axioms strong_residual_gauged
#print axioms physicalOccupation_productState_Psi
#print axioms strong_symbol_physical
#print axioms strong_residual_physicalQ

end

end QuantumNLS.StrongSymbols
