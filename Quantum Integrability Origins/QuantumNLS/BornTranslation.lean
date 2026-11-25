import Mathlib
import QuantumNLS.WaveTranslation
import QuantumNLS.OneParticleBorn

/-!
# Translation invariance of the finite-particle Born laws

Source: `ROOT_spectral_measure.tex` (discussion after `prop:root-free`: "every finite-N Bethe probability is translation invariant") and `ROOT_measure_extensions.tex`
(`prop:root-full-mass`: "Common phase and translation leave every finite-particle probability unchanged").

With `(τ_a u)(x) = u(x + a)` (`trans`), this module proves for the accepted physical Bethe basis (UBB1) at every `N ≥ 1` and coupling `κ/N`:
`bornLaw(Ψ_{N,m}, τ_a u) = bornLaw(Ψ_{N,m}, u)` (`bornLaw_translate`).  The proof: `(τ_a u)^{⊗N} = τ_a^{⊗N} u^{⊗N}` (`prod_trans`), the actual Bethe wave is an eigenvector
of the diagonal translation `τ_a^{⊗N}` with eigenvalue `e^{i a Σ q_j}` of modulus one (`transN_wave`, from `WaveTranslation.torusExtension_translate`), and `τ_a^{⊗N}` is a
linear isometry.  No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal

noncomputable section

namespace QuantumNLS.BornTranslation

open QuantumNLS.PhysicalTensor (L2T L2TN prodLp prodFun memLp_prodFun torusPiMeasure)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.BetheFreeFamily (Label)
open QuantumNLS.BetheConditionalBasis (labelArr normalizedWave)
open QuantumNLS.BetheCoefficientTransform (bornLaw productVec)
open QuantumNLS.WaveTranslation (totalRoot torusExtension_translate)

variable {L : ℝ} [Fact (0 < L)]

/-- The translation `(τ_a u)(x) = u(x + a)` on `L²(𝕋_L)` (a linear isometry). -/
def trans (a : ℝ) : L2T L →ₗᵢ[ℂ] L2T L :=
  Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ (fun x : AddCircle L => x + (a : AddCircle L))
    (measurePreserving_add_right (volume : Measure (AddCircle L)) (a : AddCircle L))

theorem coeFn_trans (a : ℝ) (u : L2T L) :
    (⇑(trans a u) : AddCircle L → ℂ) =ᵐ[volume] fun x => u (x + (a : AddCircle L)) :=
  Lp.coeFn_compMeasurePreserving u _

theorem measurePreserving_shift (N : ℕ) (a : ℝ) :
    MeasurePreserving (fun y : Fin N → AddCircle L => fun j => y j + (a : AddCircle L))
      (torusPiMeasure L N) (torusPiMeasure L N) :=
  measurePreserving_add_right (torusPiMeasure L N) (fun _ : Fin N => (a : AddCircle L))

/-- The diagonal translation `τ_a^{⊗N}` on `L²(𝕋_L^N)`. -/
def transN (N : ℕ) (a : ℝ) : L2TN L N →ₗᵢ[ℂ] L2TN L N :=
  Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ (fun y : Fin N → AddCircle L => fun j => y j + (a : AddCircle L))
    (measurePreserving_shift N a)

theorem coeFn_transN (N : ℕ) (a : ℝ) (g : L2TN L N) :
    (⇑(transN N a g) : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      fun y => g (fun j => y j + (a : AddCircle L)) :=
  Lp.coeFn_compMeasurePreserving g _

/-- `(τ_a u)^{⊗N} = τ_a^{⊗N} u^{⊗N}`. -/
theorem prod_trans (N : ℕ) (a : ℝ) (u : L2T L) :
    prodLp (fun _ : Fin N => trans a u) = transN N a (prodLp (fun _ : Fin N => u)) := by
  apply Lp.ext
  have hA3 := (measurePreserving_shift (L := L) N a).quasiMeasurePreserving.ae
    ((memLp_prodFun (fun _ : Fin N => u)).coeFn_toLp)
  have hA4 : ∀ᵐ y ∂(torusPiMeasure L N), ∀ j : Fin N, (trans a u : AddCircle L → ℂ) (y j) = u (y j + (a : AddCircle L)) :=
    ae_all_iff.2 (fun j => (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure (AddCircle L))) j).ae
      (coeFn_trans a u))
  filter_upwards [(memLp_prodFun (fun _ : Fin N => trans a u)).coeFn_toLp,
    coeFn_transN N a (prodLp (fun _ : Fin N => u)), hA3, hA4] with y h1 h2 h3 h4
  rw [h2]
  change (prodLp (fun _ : Fin N => trans a u) : (Fin N → AddCircle L) → ℂ) y = _
  have h1' : (prodLp (fun _ : Fin N => trans a u) : (Fin N → AddCircle L) → ℂ) y =
      prodFun (fun _ : Fin N => trans a u) y := h1
  have h3' : (prodLp (fun _ : Fin N => u) : (Fin N → AddCircle L) → ℂ) (fun j => y j + (a : AddCircle L)) =
      prodFun (fun _ : Fin N => u) (fun j => y j + (a : AddCircle L)) := h3
  rw [h1', h3']
  unfold prodFun
  exact Finset.prod_congr rfl (fun j _ => h4 j)

/-- The actual one-wave eigenrelation: `τ_a^{⊗N} ψ = e^{i a Σ q_j} ψ`. -/
theorem transN_wave {N : ℕ} {c : ℝ} (hc : 0 < c) {n : Fin (N + 1) → ℤ} (hn : Antitone n) (a : ℝ) :
    transN (N + 1) a (QuantumNLS.BetheH1.wave (L := L) hc hn) =
      Complex.exp (Complex.I * ((a * totalRoot L c n : ℝ) : ℂ)) • QuantumNLS.BetheH1.wave (L := L) hc hn := by
  apply Lp.ext
  have hw := QuantumNLS.BetheH1.coe_wave (L := L) hc hn
  have hw' := (measurePreserving_shift (L := L) (N + 1) a).quasiMeasurePreserving.ae hw
  filter_upwards [coeFn_transN (N + 1) a (QuantumNLS.BetheH1.wave (L := L) hc hn),
    Lp.coeFn_smul (Complex.exp (Complex.I * ((a * totalRoot L c n : ℝ) : ℂ))) (QuantumNLS.BetheH1.wave (L := L) hc hn),
    hw, hw'] with y h1 h2 h3 h4
  rw [h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h4, h3]
  exact torusExtension_translate hc hn y a

/-- `(wave c ℓ : L²(𝕋_L^{N+1}))` is the actual Bethe wave (positive coupling). -/
theorem wave_coe {N : ℕ} {c : ℝ≥0} (hc : 0 < (c : ℝ)) (ℓ : Label (N + 1)) :
    ((QuantumNLS.BetheContinuityInputs.wave (L := L) c ℓ : QuantumNLS.ContactOperator.SymL2 L (N + 1)) : L2TN L (N + 1)) =
      QuantumNLS.BetheH1.wave (L := L) hc ℓ.2 := by
  rw [QuantumNLS.BetheContinuityInputs.wave_pos hc]
  exact QuantumNLS.BetheH1.waveH1_val hc ℓ.2

/-- The modulus of the Bethe coefficient of a product state is translation invariant. -/
theorem norm_coef_translate {N : ℕ} {x : ℝ} (hx : 0 < x) (ℓ : Label (N + 1)) (u : L2T L) (a : ℝ) :
    ‖⟪normalizedWave L (N + 1) ⟨x, hx.le⟩ ℓ,
        QuantumNLS.BethePhysicalTransfer.symmetricPosition L (N + 1) (productVec L (N + 1) (trans a u))⟫_ℂ‖ =
      ‖⟪normalizedWave L (N + 1) ⟨x, hx.le⟩ ℓ,
        QuantumNLS.BethePhysicalTransfer.symmetricPosition L (N + 1) (productVec L (N + 1) u)⟫_ℂ‖ := by
  set c : ℝ≥0 := ⟨x, hx.le⟩ with hcdef
  have hc : 0 < (c : ℝ) := hx
  set W : QuantumNLS.ContactOperator.SymL2 L (N + 1) :=
    QuantumNLS.BetheContinuityInputs.wave (L := L) c ℓ with hWdef
  have hsrc : QuantumNLS.BetheConditionalBasis.sourceWave L (N + 1) c ℓ = W := rfl
  have hV : ∀ v : L2T L, ((QuantumNLS.BethePhysicalTransfer.symmetricPosition L (N + 1) (productVec L (N + 1) v) :
      QuantumNLS.ContactOperator.SymL2 L (N + 1)) : L2TN L (N + 1)) = prodLp (fun _ : Fin (N + 1) => v) :=
    fun v => QuantumNLS.PhysicalTensor.physUnitary_ptprod (fun _ : Fin (N + 1) => v)
  have hWc : (W : L2TN L (N + 1)) = QuantumNLS.BetheH1.wave (L := L) hc ℓ.2 := wave_coe hc ℓ
  have hinner : ∀ v : L2T L, ‖⟪normalizedWave L (N + 1) c ℓ,
      QuantumNLS.BethePhysicalTransfer.symmetricPosition L (N + 1) (productVec L (N + 1) v)⟫_ℂ‖ =
      ‖W‖⁻¹ * ‖⟪(W : L2TN L (N + 1)), prodLp (fun _ : Fin (N + 1) => v)⟫_ℂ‖ := by
    intro v
    set V : QuantumNLS.ContactOperator.SymL2 L (N + 1) :=
      QuantumNLS.BethePhysicalTransfer.symmetricPosition L (N + 1) (productVec L (N + 1) v) with hVdef
    have hI : ⟪W, V⟫_ℂ = ⟪(W : L2TN L (N + 1)), (V : L2TN L (N + 1))⟫_ℂ := rfl
    have hstep : ⟪(((‖W‖ : ℝ) : ℂ))⁻¹ • W, V⟫_ℂ = (starRingEnd ℂ) ((((‖W‖ : ℝ) : ℂ))⁻¹) * ⟪W, V⟫_ℂ :=
      inner_smul_left (𝕜 := ℂ) (E := QuantumNLS.ContactOperator.SymL2 L (N + 1)) W V _
    unfold normalizedWave
    show ‖⟪(((‖W‖ : ℝ) : ℂ))⁻¹ • W, V⟫_ℂ‖ = _
    rw [hstep, norm_mul, hI, hV v]
    congr 1
    rw [Complex.norm_conj, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  rw [hinner, hinner, prod_trans]
  congr 1
  -- `⟪W, τ ψ⟫` has the same modulus as `⟪W, ψ⟫`
  set g0 := prodLp (fun _ : Fin (N + 1) => u) with hg0
  set e : ℂ := Complex.exp (Complex.I * ((a * totalRoot L c ℓ.1 : ℝ) : ℂ)) with he
  have hTW : transN (N + 1) a (W : L2TN L (N + 1)) = e • (W : L2TN L (N + 1)) := by
    rw [hWc]; exact transN_wave hc ℓ.2 a
  have hiso := (transN (L := L) (N + 1) a).inner_map_map (W : L2TN L (N + 1)) g0
  rw [hTW, inner_smul_left] at hiso
  have hen : ‖(starRingEnd ℂ) e‖ = 1 := by
    rw [Complex.norm_conj, he, mul_comm, Complex.norm_exp_ofReal_mul_I]
  have := congrArg norm hiso
  rw [norm_mul, hen, one_mul] at this
  exact this

/-! ### Born law -/

theorem bornLaw_translate {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) (u : L2T L) (a : ℝ) (m : MArr N) :
    bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) (trans a u) m =
      bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) u m := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hc : 0 < κ / ((N' + 1 : ℕ) : ℝ) := div_pos hκ (by positivity)
  have key : ∀ v : L2T L, bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N' + 1) hN hκ) v m =
      ‖⟪normalizedWave L (N' + 1) ⟨κ / ((N' + 1 : ℕ) : ℝ), hc.le⟩ ((labelArr (N' + 1)).symm m),
        QuantumNLS.BethePhysicalTransfer.symmetricPosition L (N' + 1) (productVec L (N' + 1) v)⟫_ℂ‖ ^ 2 := by
    intro v
    have h1 := QuantumNLS.BetheCoefficientTransform.bornLaw_eq_coefficient
      (QuantumNLS.UnconditionalBetheBasis.physicalBasis L (N' + 1) hN (κ / ((N' + 1 : ℕ) : ℝ)) hc) v m
    have h2 := QuantumNLS.UnconditionalBetheBasis.coefficientTransform_apply L (N' + 1) hN
      (κ / ((N' + 1 : ℕ) : ℝ)) hc (productVec L (N' + 1) v) m
    change bornLaw (QuantumNLS.UnconditionalBetheBasis.physicalBasis L (N' + 1) hN (κ / ((N' + 1 : ℕ) : ℝ)) hc) v m = _
    rw [h1]
    change ‖QuantumNLS.UnconditionalBetheBasis.coefficientTransform L (N' + 1) hN (κ / ((N' + 1 : ℕ) : ℝ)) hc
      (productVec L (N' + 1) v) m‖ ^ 2 = _
    rw [h2]
  rw [key, key, norm_coef_translate hc]

end QuantumNLS.BornTranslation

#print axioms QuantumNLS.BornTranslation.prod_trans
#print axioms QuantumNLS.BornTranslation.transN_wave
#print axioms QuantumNLS.BornTranslation.norm_coef_translate
#print axioms QuantumNLS.BornTranslation.bornLaw_translate
