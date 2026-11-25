import NlsGge.Definitions.PilotInterfaces
import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import NlsGge.GK38.Lib.SymmPair

/-!
# X2: shared definitions for the E01 campaign (plan section 6.0, rev. 4)

Source and conventions (Grébert-Kappeler book, Chapter I, section 1, `(0.1)`, `(1.1)`, `(1.2)`):
the Zakharov-Shabat operator is `L(φ) = R D + Φ` with `R = diag(i, -i)`, `D = d/dt`,
`Φ = [[0, φ₁],[φ₂, 0]]`, acting on `φ = (φ₁, φ₂) ∈ L²_c = L²_ℂ × L²_ℂ`, with period one.
The free fundamental solution is `E_λ(t) = e^{-λRt} = diag(e^{-iλt}, e^{iλt})`; the general one
solves `L(φ)M = λM`, `M(0) = Id`, i.e. `M' = (-λR + RΦ) M` with
`RΦ = [[0, iφ₁],[-iφ₂, 0]]`.  `zsCoeffPair φ₁ φ₂ z x` is exactly `-zR + RΦ(x)`.

Pins checked by theorem in this file:
* `zsCoeffPair_eq_neg_smul_add_mul` : the coefficient is `-zR + RΦ` (book (1.2));
* `zsCoeffPair_mulVec_iff` : `R ψ' + Φ ψ = z ψ ↔ ψ' = A ψ` pointwise (so `ψ' = Aψ` is `L(φ)ψ = zψ`);
* `zsCoeffPair_zero_*` : `φ = 0` gives `E_z(t) = diag(e^{-izt}, e^{izt})`;
* `zsCoeffPair_const_*` : constant potential `(a, b)`: `A² = (ab - z²) I`, closed-form fundamental
  solution `cos(κt) I + (sin(κt)/κ) A` with `κ² = z² - ab`, full trace `2 cos κ`;
* `perCharOf_free` : with `Δ = 2 cos z` (book normalization `Δ = 2Δh`), `Δ² - 4 = -4 sin² z`.

Reuse decisions (recorded for `NlsGge/GK38/STATUS.md`):
* `πn` is an **abbreviation** of `NlsGge.GK38.Lib.piN` (`SymmPair.lean`, L4a), which has the same
  definition; this file imports `SymmPair` and does not duplicate the definition.
* `perChar` is **not defined here**: `discrim` is defined by F4.  `perCharOf` is the generic form
  `fun z => D z ^ 2 - 4`; F4 should set `perChar φ z := perCharOf (discrim φ) z` (or inline).
* `zsCoeffPair_real` is proved against the existing
  `NlsGge.SpectralFoundations.zsCoefficientComplex`.
-/

set_option autoImplicit false

open Filter Topology Matrix

namespace NlsGge.GK38

noncomputable section

open NlsGge.Pilot

/-! ### The potential space and the real slice -/

/-- GKP's `L²_c = L²_ℂ × L²_ℂ` (complex Banach space, sup norm on the product; the book uses the
`ℓ²`-type norm `‖φ‖² = ‖φ₁‖² + ‖φ₂‖²` of `(1.6)`, which is equivalent). -/
abbrev PotPair : Type := PhysicalL2 × PhysicalL2

/-- Pointwise complex conjugation on `PhysicalL2` as a real-linear isometry (Mathlib's `Star`
instance on `Lp`, the same `star` as in `ActualSourcePerturbedDiracSelfAdjointPhysicalSliceV2`). -/
def starLp : PhysicalL2 →ₗᵢ[ℝ] PhysicalL2 where
  toFun f := star f
  map_add' f g := by
    apply MeasureTheory.Lp.ext
    filter_upwards [MeasureTheory.Lp.coeFn_add f g,
      MeasureTheory.Lp.coeFn_star (f + g), MeasureTheory.Lp.coeFn_add (star f) (star g),
      MeasureTheory.Lp.coeFn_star f, MeasureTheory.Lp.coeFn_star g] with x h1 h2 h3 h4 h5
    simp only [h2, h3, h4, h5, Pi.star_apply, Pi.add_apply, h1, star_add]
  map_smul' c f := by
    apply MeasureTheory.Lp.ext
    filter_upwards [MeasureTheory.Lp.coeFn_smul c f,
      MeasureTheory.Lp.coeFn_star (c • f),
      MeasureTheory.Lp.coeFn_smul c (star f),
      MeasureTheory.Lp.coeFn_star f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h2, h3, Pi.star_apply, h1, Pi.smul_apply, h4]
    simp
  norm_map' f := by
    rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
    change (MeasureTheory.eLpNorm (⇑(star f)) 2 _).toReal = _
    rw [MeasureTheory.eLpNorm_congr_ae (MeasureTheory.Lp.coeFn_star f),
      MeasureTheory.eLpNorm_star]

theorem starLp_apply (f : PhysicalL2) : starLp f = star f := rfl

/-- The real slice `u ↦ (u, ū)` of GKP's complex potential space (real-linear, isometric, not
complex-linear). -/
def realSlice : PhysicalL2 →L[ℝ] PotPair :=
  (ContinuousLinearMap.id ℝ PhysicalL2).prod starLp.toContinuousLinearMap

@[simp] theorem realSlice_apply (u : PhysicalL2) : realSlice u = (u, star u) := rfl

theorem realSlice_fst (u : PhysicalL2) : (realSlice u).1 = u := rfl

theorem realSlice_snd (u : PhysicalL2) : (realSlice u).2 = star u := rfl

theorem realSlice_snd_ae (u : PhysicalL2) :
    ⇑(realSlice u).2 =ᵐ[spatialMeasure] fun x => starRingEnd ℂ (u x) :=
  MeasureTheory.Lp.coeFn_star u

theorem realSlice_injective : Function.Injective realSlice := fun u v h => by
  simpa using congrArg Prod.fst h

theorem norm_realSlice (u : PhysicalL2) : ‖realSlice u‖ = ‖u‖ := by
  rw [realSlice_apply, Prod.norm_def]
  have : ‖star u‖ = ‖u‖ := starLp.norm_map u
  rw [this, max_self]

/-! ### The Zakharov-Shabat coefficient matrix -/

/-- `ψ' = [[-iλ, iφ₁],[-iφ₂, iλ]] ψ` is `L(φ)ψ = λψ` for `L(φ) = i diag(1,-1) d/dx + [[0,φ₁],[φ₂,0]]`
(GK book Chapter I (0.1), (1.1), (1.2); GKP §1). -/
def zsCoeffPair (φ₁ φ₂ : ℝ → ℂ) (z : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(Complex.I * z), Complex.I * φ₁ x; -(Complex.I * φ₂ x), Complex.I * z]

/-- On the real slice `φ₂ = ū`, the pair coefficient is the repository's `zsCoefficientComplex`. -/
theorem zsCoeffPair_real (u : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    zsCoeffPair u (fun y => star (u y)) z x =
      NlsGge.SpectralFoundations.zsCoefficientComplex u z x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zsCoeffPair, NlsGge.SpectralFoundations.zsCoefficientComplex]

/-- The book's matrices `R = diag(i,-i)` and `Φ = [[0,φ₁],[φ₂,0]]`. -/
def zsR : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

def zsPhi (φ₁ φ₂ : ℝ → ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, φ₁ x; φ₂ x, 0]

/-- Book (1.2): `M' = (-λR + RΦ̃) M`, i.e. the coefficient is `-zR + RΦ`. -/
theorem zsCoeffPair_eq_neg_smul_add_mul (φ₁ φ₂ : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    zsCoeffPair φ₁ φ₂ z x = -(z • zsR) + zsR * zsPhi φ₁ φ₂ x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zsCoeffPair, zsR, zsPhi] <;> ring

/-- Pointwise: `L(φ)ψ = zψ`, i.e. `R ψ' + Φ ψ = z ψ`, iff `ψ' = A ψ`. -/
theorem zsCoeffPair_mulVec_iff (φ₁ φ₂ : ℝ → ℂ) (z : ℂ) (x : ℝ) (ψ ψ' : Fin 2 → ℂ) :
    zsR *ᵥ ψ' + zsPhi φ₁ φ₂ x *ᵥ ψ = z • ψ ↔ ψ' = zsCoeffPair φ₁ φ₂ z x *ᵥ ψ := by
  have hI := Complex.I_sq
  rw [funext_iff, funext_iff]
  simp only [Fin.forall_fin_two, Pi.add_apply, Pi.smul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, zsR, zsPhi, zsCoeffPair]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨?_, ?_⟩
    · linear_combination (-Complex.I) * h0 + ψ' 0 * hI
    · linear_combination (Complex.I) * h1 + ψ' 1 * hI
  · rintro ⟨h0, h1⟩
    refine ⟨?_, ?_⟩
    · linear_combination Complex.I * h0 + (φ₁ x * ψ 1 - ψ 0 * z) * hI
    · linear_combination (-Complex.I) * h1 + (φ₂ x * ψ 0 - ψ 1 * z) * hI

/-! ### The remaining shared definitions -/

/-- `π_n = nπ` for `n ≠ 0`, `π_0 = 1` (GKP App. 20).  This is an abbreviation of
`NlsGge.GK38.Lib.piN` from `SymmPair.lean` (same definition), not a second definition. -/
abbrev πn (n : ℤ) : ℝ := NlsGge.GK38.Lib.piN n

theorem πn_zero : πn 0 = 1 := NlsGge.GK38.Lib.piN_zero

theorem πn_of_ne {n : ℤ} (h : n ≠ 0) : πn n = n * Real.pi := NlsGge.GK38.Lib.piN_of_ne h

theorem πn_ne_zero (n : ℤ) : πn n ≠ 0 := NlsGge.GK38.Lib.piN_ne_zero n

/-- The periodic characteristic function from a discriminant `D` (full trace of the monodromy,
GKP's `Δ = 2Δh`): `χ_p = D² - 4`.  F4 defines `discrim` and then `perChar φ z := perCharOf (discrim φ) z`. -/
def perCharOf (D : ℂ → ℂ) (z : ℂ) : ℂ := D z ^ 2 - 4

/-- Weak convergence in `PhysicalL2` (inner product conjugate-linear in the first slot, as in
Mathlib: `inner ℂ v u = ∫ conj v · u`). -/
def IsWeakLim (u : ℕ → PhysicalL2) (u₀ : PhysicalL2) : Prop :=
  ∀ v : PhysicalL2, Tendsto (fun k => inner ℂ v (u k)) atTop (𝓝 (inner ℂ v u₀))

/-- Componentwise weak convergence of potential pairs (plan §6.0, used by F6; added after review REVIEW_X2
finding 1). -/
def IsWeakLimComp (φ : ℕ → PotPair) (φ₀ : PotPair) : Prop :=
  IsWeakLim (fun k => (φ k).1) φ₀.1 ∧ IsWeakLim (fun k => (φ k).2) φ₀.2

/-- "`ℓ²(n)` locally uniformly on a neighbourhood of `x₀`": there are a neighbourhood `U` of `x₀`
and a constant `c` with `Σ_n ‖a x n‖² ≤ c` (and summable) for every `x ∈ U`.  A locally bounded
constant only: it gives no uniformly small tails (AUD §2.5). -/
def IsLocUnifL2Seq {X ι : Type*} [TopologicalSpace X] (a : X → ι → ℂ) (x₀ : X) : Prop :=
  ∃ U ∈ 𝓝 x₀, ∃ c : ℝ, ∀ x ∈ U,
    Summable (fun n => ‖a x n‖ ^ 2) ∧ ∑' n, ‖a x n‖ ^ 2 ≤ c


/-! ### Lemmas for the weak limit and the `ℓ²` predicate -/

theorem isWeakLim_const (u₀ : PhysicalL2) : IsWeakLim (fun _ => u₀) u₀ := fun _ =>
  tendsto_const_nhds

theorem IsWeakLim.unique {u : ℕ → PhysicalL2} {u₀ u₁ : PhysicalL2} (h₀ : IsWeakLim u u₀)
    (h₁ : IsWeakLim u u₁) : u₀ = u₁ := by
  refine (ext_inner_left ℂ fun v => ?_).symm
  exact tendsto_nhds_unique (h₀ v) (h₁ v) |>.symm

/-- Norm convergence implies weak convergence. -/
theorem IsWeakLim.of_tendsto {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    (h : Tendsto u atTop (𝓝 u₀)) : IsWeakLim u u₀ := fun v =>
  ((innerSL ℂ v).continuous.tendsto u₀).comp h

theorem isLocUnifL2Seq_const {X ι : Type*} [TopologicalSpace X] (b : ι → ℂ) (x₀ : X)
    (hb : Summable fun n => ‖b n‖ ^ 2) : IsLocUnifL2Seq (fun (_ : X) n => b n) x₀ :=
  ⟨Set.univ, Filter.univ_mem, ∑' n, ‖b n‖ ^ 2, fun _ _ => ⟨hb, le_rfl⟩⟩

theorem IsLocUnifL2Seq.mono {X ι : Type*} [TopologicalSpace X] {a b : X → ι → ℂ} {x₀ : X}
    (ha : IsLocUnifL2Seq a x₀) (hle : ∀ᶠ x in 𝓝 x₀, ∀ n, ‖b x n‖ ≤ ‖a x n‖) :
    IsLocUnifL2Seq b x₀ := by
  obtain ⟨U, hU, c, hc⟩ := ha
  refine ⟨U ∩ {x | ∀ n, ‖b x n‖ ≤ ‖a x n‖}, Filter.inter_mem hU hle, c, fun x hx => ?_⟩
  obtain ⟨hxU, hxb⟩ := hx
  obtain ⟨hs, ht⟩ := hc x hxU
  have hle2 : ∀ n, ‖b x n‖ ^ 2 ≤ ‖a x n‖ ^ 2 := fun n =>
    pow_le_pow_left₀ (norm_nonneg _) (hxb n) 2
  have hsb : Summable fun n => ‖b x n‖ ^ 2 :=
    hs.of_nonneg_of_le (fun n => sq_nonneg _) hle2
  exact ⟨hsb, (hsb.tsum_le_tsum hle2 hs).trans ht⟩

/-! ### Probes: sign conventions (book Chapter I, section 1) -/

/-- `φ = 0`: the coefficient is `-zR = diag(-iz, iz)`, the generator of `E_z(t) = e^{-zRt}`. -/
theorem zsCoeffPair_zero (z : ℂ) (x : ℝ) :
    zsCoeffPair (fun _ => 0) (fun _ => 0) z x = !![-(Complex.I * z), 0; 0, Complex.I * z] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [zsCoeffPair]

/-- `φ = 0`: `E_z(t) = diag(e^{-izt}, e^{izt})` solves `M' = A M`, `M(0) = Id` (book Chapter I
section 1, `E_λ`). -/
theorem zsCoeffPair_zero_fundamental (z : ℂ) :
    NlsGge.SpectralFoundations.freeZsFundamentalComplex z 0 = 1 ∧ ∀ x : ℝ,
      HasDerivAt (NlsGge.SpectralFoundations.freeZsFundamentalComplex z)
        (zsCoeffPair (fun _ => 0) (fun _ => 0) z x *
          NlsGge.SpectralFoundations.freeZsFundamentalComplex z x) x := by
  have h := NlsGge.SpectralFoundations.freeZsFundamentalComplex_is z
  refine ⟨h.1, fun x => ?_⟩
  have e : (fun _ : ℝ => (0 : ℂ)) = fun y => star ((fun _ : ℝ => (0 : ℂ)) y) := by
    funext y; simp
  have := h.2 x
  rwa [← zsCoeffPair_real, ← e] at this

theorem freeZsFundamentalComplex_entries (z : ℂ) (x : ℝ) :
    NlsGge.SpectralFoundations.freeZsFundamentalComplex z x =
      !![Complex.exp (-(Complex.I * z * x)), 0; 0, Complex.exp (Complex.I * z * x)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NlsGge.SpectralFoundations.freeZsFundamentalComplex,
      NlsGge.SpectralFoundations.freeDiagonalCandidate, Matrix.diagonal, mul_comm]

/-- Regression T2 (zero potential), the part provable from this file: the full monodromy trace at
`φ = 0` over period one is `2 cos z`, i.e. `Δh(0, z) = cos z` and `Δ = 2 Δh`. -/
theorem zsFullTrace_zeroPotential (z : ℂ) :
    NlsGge.SpectralFoundations.zsFullTrace
      (NlsGge.SpectralFoundations.freeZsFundamentalComplex z) 1 = 2 * Complex.cos z := by
  rw [NlsGge.SpectralFoundations.freeZsFullTraceComplex, Complex.two_cos]
  simp [mul_comm, add_comm]

/-- Book Lemma 3.1 normalization: `χ_p = Δ² - 4 = -4 sin² z` at `φ = 0`. -/
theorem perCharOf_free (z : ℂ) :
    perCharOf (fun w => 2 * Complex.cos w) z = -4 * Complex.sin z ^ 2 := by
  unfold perCharOf
  linear_combination 4 * Complex.sin_sq_add_cos_sq z

/-- Constant potential `(a, b)`: `A² = (ab - z²) I` (so `A` has eigenvalues `±κ i`, `κ² = z² - ab`). -/
theorem zsCoeffPair_const_sq (a b z : ℂ) (x : ℝ) :
    zsCoeffPair (fun _ => a) (fun _ => b) z x * zsCoeffPair (fun _ => a) (fun _ => b) z x
      = (a * b - z ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hI := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zsCoeffPair, Matrix.mul_apply, Fin.sum_univ_two] <;> first | (linear_combination (z ^ 2 - a * b) * hI) | ring

theorem zsCoeffPair_const_trace (a b z : ℂ) (x : ℝ) :
    Matrix.trace (zsCoeffPair (fun _ => a) (fun _ => b) z x) = 0 := by
  simp [zsCoeffPair, Matrix.trace, Fin.sum_univ_two]

theorem zsCoeffPair_const_det (a b z : ℂ) (x : ℝ) :
    Matrix.det (zsCoeffPair (fun _ => a) (fun _ => b) z x) = z ^ 2 - a * b := by
  have hI := Complex.I_sq
  rw [Matrix.det_fin_two]
  simp [zsCoeffPair]
  linear_combination (a * b - z ^ 2) * hI

/-- Constant real-slice potential `u ≡ a` (`φ = (a, ā)`): closed-form fundamental solution
`cos(κt) I + (sin(κt)/κ) A` with `κ² = z² - |a|²`. -/
theorem hasDerivAt_cos_mul (κ : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.cos (κ * x)) (-(κ * Complex.sin (κ * x))) x := by
  have h : HasDerivAt (fun w : ℂ => κ * w) κ (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul κ
  have := (h.ccos).comp_ofReal
  simpa [mul_comm] using this

theorem hasDerivAt_sin_mul (κ : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.sin (κ * x)) (κ * Complex.cos (κ * x)) x := by
  have h : HasDerivAt (fun w : ℂ => κ * w) κ (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul κ
  have := (h.csin).comp_ofReal
  simpa [mul_comm] using this

def zsConstFund (a z κ : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.cos (κ * x) - Complex.I * z / κ * Complex.sin (κ * x),
      Complex.I * a / κ * Complex.sin (κ * x);
    -(Complex.I * star a) / κ * Complex.sin (κ * x),
      Complex.cos (κ * x) + Complex.I * z / κ * Complex.sin (κ * x)]

theorem zsConstFund_isFundamental (a z κ : ℂ) (hκ : κ ≠ 0) (hκ2 : κ ^ 2 = z ^ 2 - a * star a) :
    NlsGge.SpectralFoundations.IsZsFundamentalSolutionComplex (fun _ => a) z
      (zsConstFund a z κ) := by
  have hI := Complex.I_sq
  have hκ2' : κ ^ 2 = z ^ 2 - a * (starRingEnd ℂ) a := hκ2
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [zsConstFund]
  · intro x
    change HasDerivAt
      (fun t : ℝ => fun i : Fin 2 => fun j : Fin 2 => zsConstFund a z κ t i j)
      (fun i : Fin 2 => fun j : Fin 2 =>
        (NlsGge.SpectralFoundations.zsCoefficientComplex (fun _ => a) z x * zsConstFund a z κ x) i j) x
    have hc := hasDerivAt_cos_mul κ x
    have hs := hasDerivAt_sin_mul κ x
    apply (hasDerivAt_pi (𝕜 := ℝ)).2
    intro i
    apply (hasDerivAt_pi (𝕜 := ℝ)).2
    intro j
    fin_cases i <;> fin_cases j
    · have := hc.sub (hs.const_mul (Complex.I * z / κ))
      refine this.congr_deriv ?_
      simp [NlsGge.SpectralFoundations.zsCoefficientComplex, zsConstFund, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      linear_combination (-Complex.sin (κ * ↑x)) * hκ2' + (-Complex.sin (κ * ↑x) * (z ^ 2 - a * (starRingEnd ℂ) a)) * hI
    · have := hs.const_mul (Complex.I * a / κ)
      refine this.congr_deriv ?_
      simp [NlsGge.SpectralFoundations.zsCoefficientComplex, zsConstFund, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      ring
    · have := hs.const_mul (-(Complex.I * star a) / κ)
      refine this.congr_deriv ?_
      simp [NlsGge.SpectralFoundations.zsCoefficientComplex, zsConstFund, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      ring
    · have := hc.add (hs.const_mul (Complex.I * z / κ))
      refine this.congr_deriv ?_
      simp [NlsGge.SpectralFoundations.zsCoefficientComplex, zsConstFund, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      linear_combination (-Complex.sin (κ * ↑x)) * hκ2' + (-Complex.sin (κ * ↑x) * (z ^ 2 - a * (starRingEnd ℂ) a)) * hI

/-- The full monodromy trace of the constant potential over period one is `2 cos κ`,
`κ² = z² - |a|²`; for real `z` with `|z| < |a|` (`κ` imaginary) `Δh = cosh √(|a|²-z²) > 1`, the gap
`(-|a|, |a|)` around `0`. -/
theorem zsConstFund_trace (a z κ : ℂ) :
    Matrix.trace (zsConstFund a z κ 1) = 2 * Complex.cos κ := by
  simp [zsConstFund, Matrix.trace, Fin.sum_univ_two]
  ring

end

end NlsGge.GK38
