import QuantumNLS.OccupationUnitary
import QuantumNLS.ProductPreparation
import QuantumNLS.BetheLabels

/-!
# DEF-007: Bethe coefficient transform and Born law (parametric realization)
(`definitions.tex:43`, `DEFINITIONS_LEDGER.md:137`)

> Given the normalized complete Bethe basis `Ψ_{N,m}`, the coefficient transform maps `ψ` to
> `(⟨Ψ_{N,m}, ψ⟩)_{m ∈ 𝓜_N}` in the normalized occupation basis of `Sym^N ℓ²(ℤ)`. For a unit profile,
> `p_{N,u}(m) = |⟨Ψ_{N,m}, u^{⊗N}⟩|²` is the full product-state spectral probability law. No conditioning on a
> finite label set is implicit.

**This realization is parametric in the basis.**  The actual complete Bethe basis is the content of the node
R-8E4D05E7 (`basis:thm:basis`, which also realizes DEF-008/DEF-025); it is *not* used here.  Here `Ψ` is any
Hilbert basis of the physical bosonic `N`-particle space indexed by the DEF-006 arrays `𝓜_N`
(`BetheBasis`); the definition, its definitional facts and the Born law are proved for every such `Ψ`.
Instantiating `Ψ` with the Bethe basis (`Ψ_m` = the Bethe eigenfunction with occupation label `m`) is exactly the
step that R-8E4D05E7 supplies; nothing below needs to be redone then.

Pins (all read-only):
* the physical bosonic `N`-particle space `H_N` of DEF-003/DEF-041 is `PhysicalTensor.physSector L N`
  `= Sym^N L²(𝕋_L)` (the carrier of `ProductPreparation.bosonicProduct` / `productState`);
* `u^{⊗N}` is `ProductPreparation.PositiveMassPreparation.bosonicProduct N u = ⟨htpow N u, _⟩`, the realized
  completed tensor power (DEF-041/TensorCarrier), in particular `productState` for the unit profile;
* `𝓜_N` is DEF-006's `BetheLabels.MArr N` (finitely supported `m : ℤ →₀ ℕ`, `Σ m = N`), identified with
  `Occupation.Arr N` by `marrArr`;
* the normalized occupation basis of `Sym^N ℓ²(ℤ)` is `OccupationUnitary.occupationBasis N`, with
  `U4 N : Sym^N ℓ²(ℤ) ≃ₗᵢ ℓ²(𝓜_N)` and `physicalOccupation L N : H_N ≃ₗᵢ ℓ²(𝓜_N)` (U3 then U4).

Proved: the coefficient transform `ψ ↦ (⟨Ψ_m,ψ⟩)_m` is a unitary `H_N ≃ₗᵢ ℓ²(𝓜_N)` (`coefficientTransform`,
`norm_coefficientTransform`, `inner_coefficientTransform`, `coefficientTransform_symm_apply`); with values in the
occupation coordinates of `Sym^N ℓ²(ℤ)` it is the unitary `fockTransform` (`fockTransform_coord`); the Born law
`bornLaw Ψ u m = |⟨Ψ_m, u^{⊗N}⟩|²` is defined on all of `𝓜_N` for every profile `u`, is summable with total mass
exactly `‖u‖^{2N}` (`hasSum_bornLaw`), hence is a probability law, i.e. sums to `1`, for every unit `u`
(`hasSum_bornLaw_unit`, `bornPMF`), with no restriction to finite label sets (`sum_finset_le_one` for the finite
partial sums).  `freeBasis` shows the structure is inhabited (the Fourier occupation basis, whose transform is
`physicalOccupation`); it is *not* the Bethe basis.
-/

set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.BetheCoefficientTransform

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor

/-! ### Reindexing a Hilbert basis -/

section Reindex

variable {ι ι' E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Reindex a Hilbert basis along an equivalence of index types. -/
def reindexBasis (e : ι ≃ ι') (b : HilbertBasis ι ℂ E) : HilbertBasis ι' ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot (v := fun i' => b (e.symm i'))
    (b.orthonormal.comp e.symm e.symm.injective) (by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h0 : ∀ i, ⟪b i, x⟫_ℂ = 0 := fun i => by
        have hmem : b i ∈ Submodule.span ℂ (Set.range fun i' => b (e.symm i')) :=
          Submodule.subset_span ⟨e i, by simp⟩
        exact (Submodule.mem_orthogonal _ x).mp hx (b i) hmem
      have hr : b.repr x = 0 := by
        ext i
        rw [HilbertBasis.repr_apply_apply, h0 i]
        simp
      exact b.repr.map_eq_zero_iff.mp hr)

theorem reindexBasis_apply (e : ι ≃ ι') (b : HilbertBasis ι ℂ E) (i' : ι') :
    reindexBasis e b i' = b (e.symm i') := by
  simp [reindexBasis]

end Reindex

/-! ### Pins: the physical space, the index set, the product state -/

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `H_N`: the physical bosonic `N`-particle space `Sym^N L²(𝕋_L)` (DEF-003 / DEF-041). -/
abbrev HN (L : ℝ) [Fact (0 < L)] (N : ℕ) : Type _ := ↥(physSector L N)

/-- `𝓜_N` (DEF-006) is the set `Occupation.Arr N` of the occupation carrier. -/
def marrArr (N : ℕ) : QuantumNLS.BetheLabels.MArr N ≃ QuantumNLS.Occupation.Arr N :=
  Equiv.subtypeEquivRight (fun m => Iff.rfl)

/-- `u^{⊗N}` in the physical bosonic space (the realized completed tensor power). -/
abbrev productVec (L : ℝ) [Fact (0 < L)] (N : ℕ) (u : L2T L) : HN L N :=
  QuantumNLS.ProductPreparation.PositiveMassPreparation.bosonicProduct (L := L) N u

theorem productVec_coe (u : L2T L) :
    ((productVec L N u : HN L N) : HilbertTensorPower ℂ (L2T L) N) = htpow N u := rfl

theorem norm_productVec (u : L2T L) : ‖productVec L N u‖ = ‖u‖ ^ N :=
  QuantumNLS.ProductPreparation.PositiveMassPreparation.norm_bosonicProduct_eq N u

/-! ### The parametric basis and the coefficient transform -/

/-- A normalized complete basis `Ψ_{N,m}`, `m ∈ 𝓜_N`, of the physical bosonic `N`-particle space (a Hilbert
basis indexed by the DEF-006 occupation arrays).  The Bethe basis of R-8E4D05E7 is an instance. -/
abbrev BetheBasis (L : ℝ) [Fact (0 < L)] (N : ℕ) : Type _ :=
  HilbertBasis (QuantumNLS.BetheLabels.MArr N) ℂ (HN L N)

variable (Ψ : BetheBasis L N)

/-- **The coefficient transform** `ψ ↦ (⟨Ψ_m, ψ⟩)_{m ∈ 𝓜_N}`, a unitary onto `ℓ²(𝓜_N)` (no finite label
truncation: all of `𝓜_N`). -/
def coefficientTransform :
    HN L N ≃ₗᵢ[ℂ] lp (fun _ : QuantumNLS.BetheLabels.MArr N => ℂ) 2 :=
  Ψ.repr

@[simp] theorem coefficientTransform_apply (ψ : HN L N) (m : QuantumNLS.BetheLabels.MArr N) :
    coefficientTransform Ψ ψ m = ⟪Ψ m, ψ⟫_ℂ :=
  HilbertBasis.repr_apply_apply Ψ ψ m

theorem norm_coefficientTransform (ψ : HN L N) : ‖coefficientTransform Ψ ψ‖ = ‖ψ‖ :=
  LinearIsometryEquiv.norm_map _ _

theorem inner_coefficientTransform (ψ φ : HN L N) :
    ⟪coefficientTransform Ψ ψ, coefficientTransform Ψ φ⟫_ℂ = ⟪ψ, φ⟫_ℂ :=
  LinearIsometryEquiv.inner_map_map _ _ _

theorem coefficientTransform_surjective : Function.Surjective (coefficientTransform Ψ) :=
  (coefficientTransform Ψ).surjective

/-- The inverse transform is the (norm-convergent) synthesis `c ↦ Σ_m c_m Ψ_m`. -/
theorem coefficientTransform_symm_apply
    (c : lp (fun _ : QuantumNLS.BetheLabels.MArr N => ℂ) 2) :
    HasSum (fun m => c m • Ψ m) ((coefficientTransform Ψ).symm c) :=
  Ψ.hasSum_repr_symm c

theorem coefficientTransform_expansion (ψ : HN L N) :
    HasSum (fun m => ⟪Ψ m, ψ⟫_ℂ • Ψ m) ψ := by
  have := Ψ.hasSum_repr ψ
  simp only [HilbertBasis.repr_apply_apply] at this
  exact this

/-! ### Coordinates in the normalized occupation basis of `Sym^N ℓ²(ℤ)` -/

/-- The coefficient transform with values in `ℓ²` of all occupation arrays of total `N`
(`OccupationHilbert.H N`), obtained by the bridge `marrArr`. -/
def occupationCoefficient : HN L N ≃ₗᵢ[ℂ] QuantumNLS.OccupationHilbert.H N :=
  (reindexBasis (marrArr N) Ψ).repr

theorem occupationCoefficient_apply (ψ : HN L N) (m : QuantumNLS.BetheLabels.MArr N) :
    occupationCoefficient Ψ ψ (marrArr N m) = ⟪Ψ m, ψ⟫_ℂ := by
  unfold occupationCoefficient
  rw [HilbertBasis.repr_apply_apply, reindexBasis_apply, Equiv.symm_apply_apply]

/-- **The coefficient transform into `Sym^N ℓ²(ℤ)`**: `ψ` is sent to the vector whose coordinates in the
normalized occupation basis `occupationBasis N` are `⟨Ψ_m, ψ⟩`. -/
def fockTransform : HN L N ≃ₗᵢ[ℂ] QuantumNLS.OccupationUnitary.Boson N :=
  (occupationCoefficient Ψ).trans (QuantumNLS.OccupationUnitary.U4 N).symm

/-- The occupation coordinates of `fockTransform Ψ ψ` are the Bethe coefficients `⟨Ψ_m, ψ⟩`. -/
theorem fockTransform_coord (ψ : HN L N) (m : QuantumNLS.BetheLabels.MArr N) :
    QuantumNLS.OccupationUnitary.U4 N (fockTransform Ψ ψ) (marrArr N m) = ⟪Ψ m, ψ⟫_ℂ := by
  unfold fockTransform
  rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    occupationCoefficient_apply]

theorem fockTransform_coord' (ψ : HN L N) (m : QuantumNLS.BetheLabels.MArr N) :
    ⟪QuantumNLS.OccupationUnitary.occupationVector (marrArr N m),
      (fockTransform Ψ ψ : QuantumNLS.OccupationUnitary.Tensor N)⟫_ℂ = ⟪Ψ m, ψ⟫_ℂ := by
  rw [← QuantumNLS.OccupationUnitary.U4_apply]
  exact fockTransform_coord Ψ ψ m

/-! ### The Born law -/

/-- **The Born law** `p_{N,u}(m) = |⟨Ψ_m, u^{⊗N}⟩|²` on all of `𝓜_N`. -/
def bornLaw (u : L2T L) (m : QuantumNLS.BetheLabels.MArr N) : ℝ :=
  ‖⟪Ψ m, productVec L N u⟫_ℂ‖ ^ 2

theorem bornLaw_nonneg (u : L2T L) (m : QuantumNLS.BetheLabels.MArr N) : 0 ≤ bornLaw Ψ u m :=
  sq_nonneg _

theorem bornLaw_eq_coefficient (u : L2T L) (m : QuantumNLS.BetheLabels.MArr N) :
    bornLaw Ψ u m = ‖coefficientTransform Ψ (productVec L N u) m‖ ^ 2 := by
  rw [coefficientTransform_apply]; rfl

theorem bornLaw_eq_fock (u : L2T L) (m : QuantumNLS.BetheLabels.MArr N) :
    bornLaw Ψ u m = ‖⟪QuantumNLS.OccupationUnitary.occupationVector (marrArr N m),
      (fockTransform Ψ (productVec L N u) : QuantumNLS.OccupationUnitary.Tensor N)⟫_ℂ‖ ^ 2 := by
  rw [fockTransform_coord']; rfl

/-- The Born law of the normalized product state of a positive-mass preparation (DEF-003 `productState`). -/
theorem bornLaw_productState (P : QuantumNLS.ProductPreparation.PositiveMassPreparation (L := L))
    (m : QuantumNLS.BetheLabels.MArr N) :
    bornLaw Ψ P.unitProfile m = ‖⟪Ψ m, P.productState N⟫_ℂ‖ ^ 2 := rfl

/-- **Parseval for the Born law**: for every profile `u`, the Born law is summable over ALL of `𝓜_N` with
total mass `‖u‖^{2N}`. -/
theorem hasSum_bornLaw (u : L2T L) : HasSum (bornLaw Ψ u) (‖u‖ ^ (2 * N)) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (coefficientTransform Ψ (productVec L N u))
  have e1 : ((2 : ENNReal).toReal) = 2 := by norm_num
  simp only [e1, Real.rpow_two] at h
  rw [norm_coefficientTransform, norm_productVec] at h
  have e : (‖u‖ ^ N) ^ 2 = ‖u‖ ^ (2 * N) := by rw [← pow_mul, mul_comm]
  rw [e] at h
  have hf : bornLaw Ψ u = fun m => ‖coefficientTransform Ψ (productVec L N u) m‖ ^ 2 :=
    funext (bornLaw_eq_coefficient Ψ u)
  rw [hf]
  exact h

/-- **The Born law of a unit profile is a probability law on all of `𝓜_N`**: it sums to `1`. -/
theorem hasSum_bornLaw_unit (u : L2T L) (hu : ‖u‖ = 1) : HasSum (bornLaw Ψ u) 1 := by
  have := hasSum_bornLaw Ψ u
  rwa [hu, one_pow] at this

theorem tsum_bornLaw_unit (u : L2T L) (hu : ‖u‖ = 1) : ∑' m, bornLaw Ψ u m = 1 :=
  (hasSum_bornLaw_unit Ψ u hu).tsum_eq

theorem summable_bornLaw (u : L2T L) : Summable (bornLaw Ψ u) := (hasSum_bornLaw Ψ u).summable

theorem bornLaw_le_one (u : L2T L) (hu : ‖u‖ = 1) (m : QuantumNLS.BetheLabels.MArr N) :
    bornLaw Ψ u m ≤ 1 := by
  have := (hasSum_bornLaw_unit Ψ u hu)
  have h2 := sum_le_hasSum ({m} : Finset (QuantumNLS.BetheLabels.MArr N))
    (fun i _ => bornLaw_nonneg Ψ u i) this
  simpa using h2

/-- Every finite set of labels carries mass at most `1`; the whole of `𝓜_N` carries exactly `1`
(no finite-label conditioning). -/
theorem sum_finset_le_one (u : L2T L) (hu : ‖u‖ = 1)
    (S : Finset (QuantumNLS.BetheLabels.MArr N)) : ∑ m ∈ S, bornLaw Ψ u m ≤ 1 :=
  sum_le_hasSum S (fun i _ => bornLaw_nonneg Ψ u i) (hasSum_bornLaw_unit Ψ u hu)

/-- The Born law of a unit profile as a probability mass function on `𝓜_N`. -/
def bornPMF (u : L2T L) (hu : ‖u‖ = 1) : PMF (QuantumNLS.BetheLabels.MArr N) :=
  ⟨fun m => ENNReal.ofReal (bornLaw Ψ u m), by
    have h := ENNReal.ofReal_tsum_of_nonneg (bornLaw_nonneg Ψ u) (summable_bornLaw Ψ u)
    rw [tsum_bornLaw_unit Ψ u hu, ENNReal.ofReal_one] at h
    rw [h]
    exact ENNReal.summable.hasSum⟩

theorem bornPMF_apply (u : L2T L) (hu : ‖u‖ = 1) (m : QuantumNLS.BetheLabels.MArr N) :
    bornPMF Ψ u hu m = ENNReal.ofReal (bornLaw Ψ u m) := rfl

/-! ### The structure is inhabited: the Fourier occupation basis (not the Bethe basis) -/

/-- The (free) Fourier occupation basis of `H_N`, `physicalOccupation L N` read as a Hilbert basis indexed by
`𝓜_N`.  It only shows that `BetheBasis` is inhabited and that the coefficient transform specializes to the
realized unitary `physicalOccupation`; the Bethe basis of R-8E4D05E7 is a different (interacting) basis. -/
def freeBasis (L : ℝ) [Fact (0 < L)] (N : ℕ) : BetheBasis L N :=
  reindexBasis (marrArr N).symm
    (HilbertBasis.ofRepr (QuantumNLS.OccupationUnitary.physicalOccupation L N))

theorem occupationCoefficient_free (ψ : HN L N) :
    occupationCoefficient (freeBasis L N) ψ = QuantumNLS.OccupationUnitary.physicalOccupation L N ψ := by
  ext m'
  unfold occupationCoefficient
  rw [HilbertBasis.repr_apply_apply]
  unfold freeBasis
  rw [reindexBasis_apply, reindexBasis_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    ← HilbertBasis.repr_apply_apply]

#print axioms hasSum_bornLaw
#print axioms hasSum_bornLaw_unit
#print axioms coefficientTransform
#print axioms fockTransform_coord
#print axioms bornPMF
#print axioms occupationCoefficient_free

end QuantumNLS.BetheCoefficientTransform
