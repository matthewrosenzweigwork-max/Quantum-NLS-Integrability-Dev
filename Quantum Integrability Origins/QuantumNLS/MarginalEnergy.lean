/-
QuantumNLS.MarginalEnergy — DEF-031 spec item 3 (physical-input bridge; an application result, not
part of the definition) on EPD1's carrier (owner: opus_tensor).

Gate spec `implementation/review records/terra_review-def031-trusted-spec.md`, item 3: "Prove the
finite-energy condition and correct normalization for the actual k-body partial trace of each
normalized symmetric H¹ N-body state, 1≤k≤N, and the projector onto u^{⊗k} for unit u∈H¹. Identify
the actual marginal and tensor projector on the same carrier and show their form realizations yield
the stated difference."

Read-only imports: EnergyPreparationDef EPD1 (sha256 4e754a66…, frozen) and through it
PhysicalEnergyTrace (67f87c5d…), SymmetricAkSpectrum (bb798c30…), PhysicalProductPreparation
(1c4d9dc2…), TensorCarrier/TraceClass/PhysicalTensor/PhysicalEnergy/CollisionIdentification.

Objects (none supplied as hypotheses): `γ^{(k)}_ψ = reducedDensityN N k hk ψ` (DEF-030, partial trace of
`|ψ⟩⟨ψ|` over the last `N−k` factors of `(L²(𝕋_L))^{⊗̂N}`), the projector
`rankOne (u^{⊗k}) (u^{⊗k})`, both on EPD1's carrier `Xk L k = (L²(𝕋_L))^{⊗̂k}`; `Tr(A_k ρ)` is EPD1's
`energyTrace ρ = Σ_w (1+Σ_j(2πw_j/L)²)⟨E_w, ρE_w⟩`; `∂_j = gradientCLM j` is the weak periodic partial
(EPD1 `gradientCLM_hasWeakPartial`); `IsFormRealization`, `W`, `additiveEnergyTraceNorm` are EPD1's.

Proved here (standard axioms only):
* §1–2 `mode_eq_ptprod` (`E_w = e_{w_1}⊗⋯⊗e_{w_k}`), `inner_htmul_mode_split`
  (`⟪E_w⊗E_{w'}, Sψ⟫ = ψ̂(w,w')`), `ofReal_re_inner_mode` (`⟨E_w, γE_w⟩ = Σ_{w'}|ψ̂(w,w')|²`),
  `energyTrace_reducedDensityPower` (`Tr(A_kγ) = Σ_v a_k(v_1..v_k)|ψ̂(v)|²`, no regularity assumed).
* §3 **`energyTrace_marginal`**: for every `ψ` with wave function `x ∈ H¹(𝕋_L^N)` and `k ≤ N`,
  `Tr(A_k γ^{(k)}_ψ) = ‖ψ‖² + Σ_{j<k} ‖∂_jψ‖²` (exact identity).
* §4 `mem_sym_of_sector`, `norm_gradient_sym`, `sum_gradient_sym` (`N Σ_{j<k} = k Σ_{j<N}` on `H¹_sym`),
  `sum_gradient_le_hN`; **`marginal_physical_inputs`** (normalized symmetric, `1≤k≤N`: positive,
  `Tr γ = 1`, `‖γ‖₁ = 1`, `Tr(A_kγ) = 1 + Σ_{j<k}‖∂_jψ‖² = 1 + (k/N)Σ_j‖∂_jψ‖² < ∞`,
  `≤ 1 + (k/N)𝔥_N[ψ]` for `κ ≥ 0`); `oneH1_iff_exists_hasWeakDeriv`.
* §5 `marginal_positive_realization`; **`marginal_difference_realization`** (`D = γ − |u^{⊗k}⟩⟨u^{⊗k}|`:
  trace-class `T` with `IsFormRealization D T`, `D = W T W`, `‖A_k^{1/2}DA_k^{1/2}‖₁ = ‖T‖₁ < ∞`, explicit
  bound, `‖D‖₁ ≤` it); **`def031_physical_inputs`** (bundle).
* §6 `energyPreparation_marginals` (application to EPD1 `EnergyPreparation`, `κ ≥ 0`).
-/
import QuantumNLS.EnergyPreparationDef

open scoped InnerProductSpace ENNReal ComplexConjugate
open MeasureTheory Filter Topology

noncomputable section

namespace QuantumNLS.MarginalEnergy

open QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor QuantumNLS.Energy
  QuantumNLS.TensorCarrier QuantumNLS.TraceClass QuantumNLS.PhysicalEnergyTrace
  QuantumNLS.EnergyPreparationDef QuantumNLS.CollisionIdentification

variable {L : ℝ} [Fact (0 < L)]

/-! ## §1 Physical product modes on the tensor carrier -/

/-- The physical product mode `E_w = e_{w_1} ⊗ ⋯ ⊗ e_{w_k}` on `(L²(𝕋_L))^{⊗̂k}`. -/
abbrev mode (k : ℕ) (w : Mom k) : Xk L k := (eK L k).symm (QuantumNLS.EnergyRealization.ev w)

theorem mode_eq_ptprod (k : ℕ) (w : Mom k) :
    mode (L := L) k w = ((ptprod (fun j => QuantumNLS.Fourier.modeLp L (w j)) :
      AlgTensorPower ℂ (L2T L) k) : HilbertTensorPower ℂ (L2T L) k) := by
  refine ext_inner_right ℂ fun v => ?_
  rw [inner_mode, eK_apply, momUnitary_apply_eq_inner, prodMode, ← physUnitary_ptprod,
    LinearIsometryEquiv.inner_map_map]

/-- The Hilbert basis of physical product modes of `(L²(𝕋_L))^{⊗̂m}`. -/
def modeBasis (m : ℕ) : HilbertBasis (Mom m) ℂ (Xk L m) := HilbertBasis.ofRepr (eK L m)

theorem modeBasis_apply (m : ℕ) (w : Mom m) : modeBasis (L := L) m w = mode m w := by
  refine ext_inner_right ℂ fun v => ?_
  rw [← HilbertBasis.repr_apply_apply, inner_mode]
  rfl

theorem append_modes {k m : ℕ} (w : Mom k) (w' : Mom m) :
    Fin.append (fun j => QuantumNLS.Fourier.modeLp L (w j))
        (fun j => QuantumNLS.Fourier.modeLp L (w' j)) =
      fun j => QuantumNLS.Fourier.modeLp L (Fin.append w w' j) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [Fin.append_left, Fin.append_right]

/-- `⟪E_w ⊗ E_{w'}, S ψ⟫ = ψ̂(w, w')`, `S` the split `E^{⊗̂(k+m)} ≃ E^{⊗̂k} ⊗̂ E^{⊗̂m}`. -/
theorem inner_htmul_mode_split {k m : ℕ} (w : Mom k) (w' : Mom m) (Φ : Xk L (k + m)) :
    ⟪(htmul (mode k w) (mode m w') : HilbertTensor ℂ (Xk L k) (Xk L m)),
        splitIsometry k m Φ⟫_ℂ =
      (eK L (k + m) Φ : Mom (k + m) → ℂ) (Fin.append w w') := by
  rw [mode_eq_ptprod, mode_eq_ptprod, ← splitIsometry_ptprod_append,
    LinearIsometryEquiv.inner_map_map, append_modes,
    ← mode_eq_ptprod (L := L) (k + m) (Fin.append w w'), inner_mode]

/-! ## §2 Diagonal of the marginal in product modes -/

/-- **`⟨E_w, γ^{(k)}_Φ E_w⟩ = Σ_{w'} |Φ̂(w, w')|²`** (in `[0, ∞]`). -/
theorem ofReal_re_inner_mode {k m : ℕ} (Φ : Xk L (k + m)) (w : Mom k) :
    ENNReal.ofReal (RCLike.re ⟪mode k w, reducedDensityPower k m Φ (mode k w)⟫_ℂ) =
      ∑' w' : Mom m,
        ENNReal.ofReal (‖(eK L (k + m) Φ : Mom (k + m) → ℂ) (Fin.append w w')‖ ^ 2) := by
  let one : HilbertBasis Unit ℂ ℂ := (OrthonormalBasis.singleton Unit ℂ).toHilbertBasis
  have hone : ∀ u, one u = 1 := by
    intro u; simp [one, OrthonormalBasis.coe_toHilbertBasis, OrthonormalBasis.singleton_apply]
  rw [reducedDensityPower, ← inner_conj_symm, inner_reducedDensity_self, RCLike.conj_ofReal,
    RCLike.ofReal_re]
  rw [← tsum_ofReal_norm_inner_sq (htmulBasis one (modeBasis (L := L) m)), ENNReal.tsum_prod']
  simp only [htmulBasis_apply, hone, inner_htmul_one_contract, modeBasis_apply,
    inner_htmul_mode_split]
  simp

/-- **Energy trace of the marginal over the last `m` factors**:
`Tr(A_k γ^{(k)}_Φ) = Σ_v (1 + Σ_{j<k} (2πv_j/L)²) |Φ̂(v)|²`. -/
theorem energyTrace_reducedDensityPower {k m : ℕ} (Φ : Xk L (k + m)) :
    energyTrace (reducedDensityPower k m Φ) =
      ∑' v : Mom (k + m), ENNReal.ofReal (kinWeight L k (fun j => v (Fin.castAdd m j)) *
        ‖(eK L (k + m) Φ : Mom (k + m) → ℂ) v‖ ^ 2) := by
  unfold energyTrace
  rw [physTrace_eq_modes]
  have hterm : ∀ w : Mom k, ENNReal.ofReal (kinWeight L k w *
      RCLike.re ⟪mode k w, reducedDensityPower k m Φ (mode k w)⟫_ℂ) =
      ∑' w' : Mom m, ENNReal.ofReal (kinWeight L k w *
        ‖(eK L (k + m) Φ : Mom (k + m) → ℂ) (Fin.append w w')‖ ^ 2) := by
    intro w
    have hk : 0 ≤ kinWeight L k w := zero_le_one.trans (one_le_kinWeight L k w)
    rw [ENNReal.ofReal_mul hk, ofReal_re_inner_mode, ← ENNReal.tsum_mul_left]
    congr 1; funext w'
    rw [← ENNReal.ofReal_mul hk]
  refine (tsum_congr fun w => hterm w).trans ?_
  rw [← (Fin.appendEquiv k m).tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun w => tsum_congr fun w' => ?_
  have h1 : (fun j => (Fin.appendEquiv k m) (w, w') (Fin.castAdd m j)) = w := by
    funext j; simp [Fin.appendEquiv_apply, Fin.append_left]
  have h2 : (Fin.appendEquiv k m) (w, w') = Fin.append w w' := by
    funext j; simp [Fin.appendEquiv_apply]
  rw [h1, h2]

/-! ## §3 `H¹` wave functions: the exact energy identity -/

omit [Fact (0 < L)] in
theorem freq_sq_le_kinWeight {n : ℕ} (i : Fin n) (v : Mom n) :
    QuantumNLS.Fourier.freq L (v i) ^ 2 ≤ kinWeight L n v := by
  unfold kinWeight
  have := Finset.single_le_sum (f := fun l => QuantumNLS.Fourier.freq L (v l) ^ 2)
    (fun l _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/-- `Σ_v (2πv_i/L)² |x̂(v)|² = ‖∂_i x‖²` (in `[0, ∞]`), `∂_i` the weak periodic partial. -/
theorem tsum_ofReal_freq_sq {n : ℕ} (x : PhysH1 L n) (i : Fin n) :
    ∑' v : Mom n, ENNReal.ofReal (QuantumNLS.Fourier.freq L (v i) ^ 2 *
      ‖(momUnitary L n x.val : Mom n → ℂ) v‖ ^ 2) = ENNReal.ofReal (‖gradientCLM i x‖ ^ 2) := by
  have hs : Summable fun v : Mom n =>
      kinWeight L n v * ‖(momUnitary L n x.val : Mom n → ℂ) v‖ ^ 2 := by
    have : x.val ∈ Set.range (PhysH1.val : PhysH1 L n → L2TN L n) := ⟨x, rfl⟩
    rw [PhysH1.range_val] at this
    exact this
  have hs' : Summable fun v : Mom n =>
      QuantumNLS.Fourier.freq L (v i) ^ 2 * ‖(momUnitary L n x.val : Mom n → ℂ) v‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun v => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun v => mul_le_mul_of_nonneg_right (freq_sq_le_kinWeight i v) (sq_nonneg _)) hs
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs',
    QuantumNLS.PhysicalProductPreparation.norm_gradientCLM, QuantumNLS.ContactForm.norm_sq_Dj]
  rfl

theorem tsum_ofReal_coeff_sq {n : ℕ} (Φ : Xk L n) :
    ∑' v : Mom n, ENNReal.ofReal (‖(eK L n Φ : Mom n → ℂ) v‖ ^ 2) = ENNReal.ofReal (‖Φ‖ ^ 2) := by
  rw [← tsum_ofReal_norm_inner_sq (modeBasis (L := L) n) Φ]
  refine tsum_congr fun v => ?_
  rw [← HilbertBasis.repr_apply_apply]
  rfl

/-- **Exact energy of the marginal over the last `m` factors of an `H¹` state**:
`Tr(A_k γ^{(k)}_Φ) = ‖Φ‖² + Σ_{j<k} ‖∂_jΦ‖²`. -/
theorem energyTrace_reducedDensityPower_H1 {k m : ℕ} (Φ : Xk L (k + m)) (y : PhysH1 L (k + m))
    (hy : y.val = physUnitary Φ) :
    energyTrace (reducedDensityPower k m Φ) =
      ENNReal.ofReal (‖Φ‖ ^ 2 + ∑ j : Fin k, ‖gradientCLM (Fin.castAdd m j) y‖ ^ 2) := by
  rw [energyTrace_reducedDensityPower]
  have hc : ∀ v, (eK L (k + m) Φ : Mom (k + m) → ℂ) v =
      (momUnitary L (k + m) y.val : Mom (k + m) → ℂ) v := by
    intro v; rw [hy]; rfl
  have hterm : ∀ v : Mom (k + m), ENNReal.ofReal (kinWeight L k (fun j => v (Fin.castAdd m j)) *
      ‖(eK L (k + m) Φ : Mom (k + m) → ℂ) v‖ ^ 2) =
      ENNReal.ofReal (‖(eK L (k + m) Φ : Mom (k + m) → ℂ) v‖ ^ 2) +
        ∑ j : Fin k, ENNReal.ofReal (QuantumNLS.Fourier.freq L (v (Fin.castAdd m j)) ^ 2 *
          ‖(momUnitary L (k + m) y.val : Mom (k + m) → ℂ) v‖ ^ 2) := by
    intro v
    rw [← hc, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      ← ENNReal.ofReal_add (sq_nonneg _)
        (Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    congr 1
    unfold kinWeight
    rw [add_mul, one_mul, Finset.sum_mul]
  rw [tsum_congr hterm, ENNReal.tsum_add, Summable.tsum_finsetSum (fun j _ => ENNReal.summable),
    tsum_ofReal_coeff_sq]
  simp_rw [tsum_ofReal_freq_sq y (Fin.castAdd m _)]
  rw [ENNReal.ofReal_add (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]

/-- Transport of an `H¹` wave function along `castHTP` (the identity after `subst`). -/
theorem exists_cast_H1 {n n' : ℕ} (h : n = n') (ψ : Xk L n) (x : PhysH1 L n)
    (hx : x.val = physUnitary ψ) :
    ∃ y : PhysH1 L n', y.val = physUnitary (castHTP h ψ) ∧
      ∀ i : Fin n, ‖gradientCLM (Fin.cast h i) y‖ = ‖gradientCLM i x‖ := by
  subst h
  exact ⟨x, hx, fun i => rfl⟩

/-- **Exact energy of the actual `k`-particle marginal (DEF-030 `γ^{(k)}_ψ`, partial trace over the
last `N − k` factors) of any `ψ` whose wave function is in `H¹(𝕋_L^N)`**:
`Tr(A_k γ^{(k)}_ψ) = ‖ψ‖² + Σ_{j<k} ‖∂_jψ‖²`, `∂_j` the weak periodic partial. -/
theorem energyTrace_marginal {N k : ℕ} (hk : k ≤ N) (ψ : Xk L N) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) :
    energyTrace (reducedDensityN N k hk ψ) =
      ENNReal.ofReal (‖ψ‖ ^ 2 + ∑ j : Fin k, ‖gradientCLM (Fin.castLE hk j) x‖ ^ 2) := by
  obtain ⟨y, hy, hg⟩ := exists_cast_H1 (Nat.add_sub_cancel' hk).symm ψ x hx
  rw [reducedDensityN, energyTrace_reducedDensityPower_H1 _ y hy, LinearIsometryEquiv.norm_map]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  have : Fin.castAdd (N - k) j = Fin.cast (Nat.add_sub_cancel' hk).symm (Fin.castLE hk j) :=
    Fin.ext rfl
  rw [this, hg]

/-! ## §4 Symmetric states -/

/-- The wave function of a DEF-004 symmetric vector is in `H¹_sym` once it is in `H¹`. -/
theorem mem_sym_of_sector {N : ℕ} {ψ : Xk L N} (hψ : ψ ∈ physSector L N) {x : PhysH1 L N}
    (hx : x.val = physUnitary ψ) : x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) := by
  rw [PhysH1.mem_sym_iff, hx]
  exact (mem_physSector_iff ψ).1 hψ

/-- On `H¹_sym` all partials have the same norm. -/
theorem norm_gradient_sym {N : ℕ} {x : PhysH1 L N}
    (hx : x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) (i i' : Fin N) :
    ‖gradientCLM i x‖ = ‖gradientCLM i' x‖ := by
  have hc := (isSymm_iff_coeff x.val).1 ((PhysH1.mem_sym_iff x).1 hx) (Equiv.swap i i')
  suffices h : ‖gradientCLM i x‖ ^ 2 = ‖gradientCLM i' x‖ ^ 2 from
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  rw [QuantumNLS.PhysicalProductPreparation.norm_gradientCLM,
    QuantumNLS.PhysicalProductPreparation.norm_gradientCLM,
    QuantumNLS.ContactForm.norm_sq_Dj, QuantumNLS.ContactForm.norm_sq_Dj,
    ← (permEquiv (Equiv.swap i i')).tsum_eq]
  refine tsum_congr fun w => ?_
  show QuantumNLS.Fourier.freq L ((w ∘ Equiv.swap i i') i) ^ 2 *
      ‖(momUnitary L N x.val : Mom N → ℂ) (w ∘ Equiv.swap i i')‖ ^ 2 =
    QuantumNLS.Fourier.freq L (w i') ^ 2 * ‖(momUnitary L N x.val : Mom N → ℂ) w‖ ^ 2
  rw [hc w]
  simp [Function.comp, Equiv.swap_apply_left]

/-- `N Σ_{j<k} ‖∂_jψ‖² = k Σ_{j<N} ‖∂_jψ‖²` on `H¹_sym`. -/
theorem sum_gradient_sym {N k : ℕ} (hk : k ≤ N) {x : PhysH1 L N}
    (hx : x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) :
    (N : ℝ) * ∑ j : Fin k, ‖gradientCLM (Fin.castLE hk j) x‖ ^ 2 =
      k * ∑ j : Fin N, ‖gradientCLM j x‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    obtain rfl : k = 0 := by omega
    simp
  · have h : ∀ i, ‖gradientCLM i x‖ ^ 2 = ‖gradientCLM (⟨0, hN⟩ : Fin N) x‖ ^ 2 := fun i => by
      rw [norm_gradient_sym hx i ⟨0, hN⟩]
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- Kinetic part of `𝔥_N` is bounded by `𝔥_N` for `κ ≥ 0`. -/
theorem sum_gradient_le_hN {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (x : PhysH1 L N) :
    ∑ j : Fin N, ‖gradientCLM j x‖ ^ 2 ≤ hN κ N x := by
  rw [(hN_literal κ x).1]
  have : 0 ≤ 2 * (κ / N) * ∑ p : QuantumNLS.ContactForm.Pair N,
      ‖QuantumNLS.CollisionIdentification.productTrace p.1.1 p.1.2 (ne_of_lt p.2) x‖ ^ 2 :=
    mul_nonneg (mul_nonneg zero_le_two (div_nonneg hκ (Nat.cast_nonneg N)))
      (Finset.sum_nonneg fun p _ => sq_nonneg _)
  linarith

/-- **Spec item 3, marginal part.** For a normalized DEF-004 symmetric `ψ ∈ Sym^N L²(𝕋_L)` whose
wave function is `x ∈ H¹(𝕋_L^N)` (hence `x ∈ H¹_sym`), and `1 ≤ k ≤ N`, the actual marginal
`γ = γ^{(k)}_ψ` is positive, has trace one (and trace norm one), and finite energy:
`Tr(A_k γ) = 1 + Σ_{j<k}‖∂_jψ‖² = 1 + (k/N) Σ_{j≤N}‖∂_jψ‖² < ∞`, and `≤ 1 + (k/N) 𝔥_N[ψ]` for
`κ ≥ 0`. -/
theorem marginal_physical_inputs {N k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N) {ψ : Xk L N}
    (hsec : ψ ∈ physSector L N) (hnorm : ‖ψ‖ = 1) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) :
    x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) ∧
    (reducedDensityN N k hk ψ).IsPositive ∧
    posTrace (reducedDensityN N k hk ψ) = 1 ∧
    traceNorm (reducedDensityN N k hk ψ) = 1 ∧
    energyTrace (reducedDensityN N k hk ψ) =
      ENNReal.ofReal (1 + ∑ j : Fin k, ‖gradientCLM (Fin.castLE hk j) x‖ ^ 2) ∧
    energyTrace (reducedDensityN N k hk ψ) =
      ENNReal.ofReal (1 + (k / N : ℝ) * ∑ j : Fin N, ‖gradientCLM j x‖ ^ 2) ∧
    energyTrace (reducedDensityN N k hk ψ) < ⊤ ∧
    ∀ κ : ℝ, 0 ≤ κ →
      energyTrace (reducedDensityN N k hk ψ) ≤ ENNReal.ofReal (1 + (k / N : ℝ) * hN κ N x) := by
  have hsym := mem_sym_of_sector hsec hx
  have hE := energyTrace_marginal hk ψ x hx
  rw [hnorm, one_pow] at hE
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkN : ∑ j : Fin k, ‖gradientCLM (Fin.castLE hk j) x‖ ^ 2 =
      (k / N : ℝ) * ∑ j : Fin N, ‖gradientCLM j x‖ ^ 2 := by
    have := sum_gradient_sym hk hsym
    field_simp
    linarith
  refine ⟨hsym, reducedDensityN_isPositive N k hk ψ, ?_, ?_, hE, by rw [hE, hkN], ?_, ?_⟩
  · exact traceIn_reducedDensityN_eq_one N k hk _ ψ hnorm
  · rw [traceNorm_reducedDensityN, hnorm]; simp
  · rw [hE]; exact ENNReal.ofReal_lt_top
  · intro κ hκ
    rw [hE, hkN]
    refine ENNReal.ofReal_le_ofReal ?_
    have := sum_gradient_le_hN hκ x
    have hkN0 : (0 : ℝ) ≤ k / N := div_nonneg (Nat.cast_nonneg k) hN0.le
    nlinarith

/-- The one-particle hypothesis `OneH1 u` (Fourier `H¹`) is exactly: `u` has a periodic weak derivative
in `L²` (then `K(u) = ‖u'‖²` by EPD1 `kinetic_eq_norm_sq_deriv`). -/
theorem oneH1_iff_exists_hasWeakDeriv (u : L2T L) :
    QuantumNLS.ProductEnergyPreparation.OneH1 u ↔
      ∃ g, QuantumNLS.WeakDerivatives.HasWeakDeriv u g := by
  rw [QuantumNLS.WeakDerivatives.exists_hasWeakDeriv_iff]
  unfold QuantumNLS.ProductEnergyPreparation.OneH1 QuantumNLS.Fourier.Mem04
    QuantumNLS.Fourier.f04Weight
  simp_rw [Real.rpow_one, QuantumNLS.Fourier.fourierL2_apply]
  have h0 := (QuantumNLS.Fourier.hasSum_sq_coeff L (Lp.memLp u)).summable
  constructor
  · intro hs
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun n => ?_) hs
    exact mul_le_mul_of_nonneg_right (by linarith [sq_nonneg (QuantumNLS.Fourier.freq L n)])
      (sq_nonneg _)
  · intro hs
    refine (h0.add hs).congr fun n => ?_
    ring

/-! ## §5 The marginal difference: trace-class form realization (EPD1 characterization) -/

/-- The positive finite-energy realization of the marginal itself. -/
theorem marginal_positive_realization {N k : ℕ} (hk : k ≤ N) (ψ : Xk L N) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) :
    ∃ T, T.IsPositive ∧ IsTraceClass T ∧ IsFormRealization (reducedDensityN N k hk ψ) T ∧
      posTrace T = ENNReal.ofReal (‖ψ‖ ^ 2 + ∑ j : Fin k, ‖gradientCLM (Fin.castLE hk j) x‖ ^ 2) ∧
      additiveEnergyTraceNorm (reducedDensityN N k hk ψ) =
        ENNReal.ofReal (‖ψ‖ ^ 2 + ∑ j : Fin k, ‖gradientCLM (Fin.castLE hk j) x‖ ^ 2) := by
  have hE := energyTrace_marginal hk ψ x hx
  obtain ⟨T, hT, htc, hr, htr, hval⟩ := positive_formRealization
    (reducedDensityN_isPositive N k hk ψ) (by rw [hE]; exact ENNReal.ofReal_ne_top)
  exact ⟨T, hT, htc, hr, htr.trans hE, hval.trans hE⟩

/-- **Spec item 3, difference part.** For `ψ` with `H¹` wave function, `k ≤ N`, and unit `u ∈ H¹`,
the difference `D = γ^{(k)}_ψ − |u^{⊗k}⟩⟨u^{⊗k}|` of the actual marginal and the actual projector (same
carrier `(L²(𝕋_L))^{⊗̂k}`) has a trace-class form realization `T` (`D = W T W`), so its additive
energy trace norm `‖A_k^{1/2} D A_k^{1/2}‖₁ = ‖T‖₁` is finite, with
`‖A_k^{1/2} D A_k^{1/2}‖₁ ≤ (‖ψ‖² + Σ_{j<k}‖∂_jψ‖²) + (1 + k‖u'‖²)` and `‖D‖₁ ≤ ‖A_k^{1/2} D A_k^{1/2}‖₁`. -/
theorem marginal_difference_realization {N k : ℕ} (hk : k ≤ N) (ψ : Xk L N) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) {u : L2T L} (hu : ‖u‖ = 1)
    (hH : QuantumNLS.ProductEnergyPreparation.OneH1 u) :
    ∃ T : Xk L k →L[ℂ] Xk L k, IsTraceClass T ∧
      IsFormRealization (reducedDensityN N k hk ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) T ∧
      reducedDensityN N k hk ψ - InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u) =
        W L k * T * W L k ∧
      additiveEnergyTraceNorm (reducedDensityN N k hk ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) = traceNorm T ∧
      additiveEnergyTraceNorm (reducedDensityN N k hk ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) ≤
        ENNReal.ofReal (‖ψ‖ ^ 2 + ∑ j : Fin k, ‖gradientCLM (Fin.castLE hk j) x‖ ^ 2) +
          ENNReal.ofReal (1 + k * QuantumNLS.ChargeEnergy.kinetic (u : AddCircle L → ℂ)) ∧
      additiveEnergyTraceNorm (reducedDensityN N k hk ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) < ⊤ ∧
      traceNorm (reducedDensityN N k hk ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) ≤
        additiveEnergyTraceNorm (reducedDensityN N k hk ψ -
          InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) := by
  have hE₁ := energyTrace_marginal hk ψ x hx
  have hE₂ := QuantumNLS.PhysicalProductPreparation.physTrace_proj hu hH k
  obtain ⟨T, htc, hs, heq, hb, hc⟩ := phys_difference (reducedDensityN_isPositive N k hk ψ)
    (show energyTrace _ ≠ ⊤ by rw [hE₁]; exact ENNReal.ofReal_ne_top)
    (InnerProductSpace.isPositive_rankOne_self (htpow k u : Xk L k))
    (by rw [hE₂]; exact ENNReal.ofReal_ne_top)
  have hb' : additiveEnergyTraceNorm (reducedDensityN N k hk ψ -
      InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) ≤
      ENNReal.ofReal (‖ψ‖ ^ 2 + ∑ j : Fin k, ‖gradientCLM (Fin.castLE hk j) x‖ ^ 2) +
        ENNReal.ofReal (1 + k * QuantumNLS.ChargeEnergy.kinetic (u : AddCircle L → ℂ)) := by
    have := hb
    unfold energyTrace at hE₁
    rw [hE₁, hE₂] at this
    exact this
  refine ⟨T, htc, (isFormRealization_iff _ T).2 hs, hs, heq, hb', ?_, hc⟩
  exact lt_of_le_of_lt hb' (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

/-- **Bundled spec item 3** for a normalized symmetric `H¹` state and `1 ≤ k ≤ N`: the marginal
data and the trace-class form realization of `γ^{(k)}_ψ − |u^{⊗k}⟩⟨u^{⊗k}|` (unit `u ∈ H¹`), whose
additive energy trace norm is at most `2 + (k/N) Σ_j ‖∂_jψ‖² + k‖u'‖²`. -/
theorem def031_physical_inputs {N k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ N) {ψ : Xk L N}
    (hsec : ψ ∈ physSector L N) (hnorm : ‖ψ‖ = 1) (x : PhysH1 L N)
    (hx : x.val = physUnitary ψ) {u : L2T L} (hu : ‖u‖ = 1)
    (hH : QuantumNLS.ProductEnergyPreparation.OneH1 u) :
    (reducedDensityN N k hk ψ).IsPositive ∧
    posTrace (reducedDensityN N k hk ψ) = 1 ∧
    energyTrace (reducedDensityN N k hk ψ) =
      ENNReal.ofReal (1 + (k / N : ℝ) * ∑ j : Fin N, ‖gradientCLM j x‖ ^ 2) ∧
    energyTrace (InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) =
      ENNReal.ofReal (1 + k * QuantumNLS.ChargeEnergy.kinetic (u : AddCircle L → ℂ)) ∧
    ∃ T : Xk L k →L[ℂ] Xk L k, IsTraceClass T ∧
      IsFormRealization (reducedDensityN N k hk ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) T ∧
      additiveEnergyTraceNorm (reducedDensityN N k hk ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) = traceNorm T ∧
      additiveEnergyTraceNorm (reducedDensityN N k hk ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) ≤
        ENNReal.ofReal (1 + (k / N : ℝ) * ∑ j : Fin N, ‖gradientCLM j x‖ ^ 2) +
          ENNReal.ofReal (1 + k * QuantumNLS.ChargeEnergy.kinetic (u : AddCircle L → ℂ)) := by
  obtain ⟨-, hpos, htr, -, hE, hE', -, -⟩ := marginal_physical_inputs hk1 hk hsec hnorm x hx
  obtain ⟨T, htc, hr, -, heq, hb, -, -⟩ := marginal_difference_realization hk ψ x hx hu hH
  refine ⟨hpos, htr, hE', QuantumNLS.PhysicalProductPreparation.physTrace_proj hu hH k,
    T, htc, hr, heq, ?_⟩
  rw [hnorm, one_pow, ← hE, hE'] at hb
  exact hb

/-! ## §6 Application: marginals of a DEF-031 energy preparation -/

/-- **Application bridge.** If `ψ` is a DEF-031 energy preparation of a unit `u ∈ H¹` (`κ ≥ 0`), then
for every fixed `k` and every `N ≥ k` the actual marginal has finite energy and
`γ_N^{(k)} − |u^{⊗k}⟩⟨u^{⊗k}|` has finite additive energy trace norm (a trace-class form
realization); moreover for every `ε > 0`, eventually `Tr(A_k γ_N^{(k)}) ≤ 1 + k (I₃(u) + ε)`. -/
theorem energyPreparation_marginals {κ : ℝ} (hκ : 0 ≤ κ) {u : L2T L} {ψ : ∀ N, Xk L N}
    (hP : EnergyPreparation κ u ψ) (hu : ‖u‖ = 1)
    (hH : QuantumNLS.ProductEnergyPreparation.OneH1 u) (k : ℕ) :
    (∀ (N : ℕ) (hk : k ≤ N), energyTrace (reducedDensityN N k hk (ψ N)) < ⊤ ∧
      additiveEnergyTraceNorm (reducedDensityN N k hk (ψ N) -
        InnerProductSpace.rankOne ℂ (htpow k u : Xk L k) (htpow k u)) < ⊤) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ hk : k ≤ N,
      energyTrace (reducedDensityN N k hk (ψ N)) ≤ ENNReal.ofReal (1 + k * (I3 κ u + ε)) := by
  obtain ⟨x, hx, hsym, hlim⟩ := hP.energy
  have hnorm : ∀ N, ‖ψ N‖ = 1 := hP.normClose.1
  refine ⟨fun N hk => ⟨?_, ?_⟩, fun ε hε => ?_⟩
  · rw [energyTrace_marginal hk (ψ N) (x N) (hx N)]; exact ENNReal.ofReal_lt_top
  · obtain ⟨T, -, -, -, -, -, hlt, -⟩ := marginal_difference_realization hk (ψ N) (x N) (hx N) hu hH
    exact hlt
  · filter_upwards [(limsup_le_iff (fun N => hN κ N (x N) / N) (I3 κ u)).1 hlim ε hε,
      eventually_ge_atTop 1] with N hNb hN1 hk
    rw [energyTrace_marginal hk (ψ N) (x N) (hx N), hnorm N, one_pow]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := sum_gradient_sym hk (hsym N)
    have h2 := sum_gradient_le_hN hκ (x N)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have h3 : hN κ N (x N) ≤ (I3 κ u + ε) * N := by
      have := hNb
      rwa [div_le_iff₀ hN0] at this
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h4 : (N : ℝ) * ∑ j : Fin k, ‖gradientCLM (Fin.castLE hk j) (x N)‖ ^ 2 ≤
        N * (k * (I3 κ u + ε)) := by
      rw [h1]; nlinarith
    have := le_of_mul_le_mul_left h4 hN0
    linarith

end QuantumNLS.MarginalEnergy

#print axioms QuantumNLS.MarginalEnergy.mode_eq_ptprod
#print axioms QuantumNLS.MarginalEnergy.inner_htmul_mode_split
#print axioms QuantumNLS.MarginalEnergy.ofReal_re_inner_mode
#print axioms QuantumNLS.MarginalEnergy.energyTrace_reducedDensityPower
#print axioms QuantumNLS.MarginalEnergy.tsum_ofReal_freq_sq
#print axioms QuantumNLS.MarginalEnergy.energyTrace_reducedDensityPower_H1
#print axioms QuantumNLS.MarginalEnergy.energyTrace_marginal
#print axioms QuantumNLS.MarginalEnergy.mem_sym_of_sector
#print axioms QuantumNLS.MarginalEnergy.norm_gradient_sym
#print axioms QuantumNLS.MarginalEnergy.sum_gradient_sym
#print axioms QuantumNLS.MarginalEnergy.sum_gradient_le_hN
#print axioms QuantumNLS.MarginalEnergy.marginal_physical_inputs
#print axioms QuantumNLS.MarginalEnergy.oneH1_iff_exists_hasWeakDeriv
#print axioms QuantumNLS.MarginalEnergy.marginal_positive_realization
#print axioms QuantumNLS.MarginalEnergy.marginal_difference_realization
#print axioms QuantumNLS.MarginalEnergy.def031_physical_inputs
#print axioms QuantumNLS.MarginalEnergy.energyPreparation_marginals
