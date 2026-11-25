import QuantumNLS.CoherentLowerBound
import QuantumNLS.GaugeTransport

/-!
# Transfer of the Wick norm limit to the physical Fourier sector

Source: `chapters/core/wick_calculus.tex` (`eq:full-Wick`, `eq:full-norm-limit`: "Use the physical
test vector `J_N^* ξ^{⊗N}`"), `chapters/core/occupation_transfers.tex:2–9`,
`chapters/definitions.tex:151–159` (DEF-025/026: the supplied phase convention `D_q^* E D_q`).
The occupation Hilbert carrier is transported to the actual physical sector `Sym^N L²(𝕋_L)` by the
constructed unitaries `U3` (Fourier) and `U4` (occupation), and the supplied phases by
`GaugeTransport.physicalPhase`.  Norms are preserved exactly (unitary intertwining).

Qualifications: NO Bethe wavefunction, NO U5, NO selected gauge: the phases `q N : Arr N → ℂ` are
arbitrary unit-modulus functions.  This is the Fourier occupation realisation, not an
identification with interacting Bethe coefficients.
-/

namespace QuantumNLS.PhysicalWickLimit

open QuantumNLS.Occupation QuantumNLS.WickSymbols QuantumNLS.WickBounds QuantumNLS.WickSpectralBridge
open QuantumNLS.CoherentLowerBound QuantumNLS.OccupationHilbert QuantumNLS.OccupationConjugacy
open QuantumNLS.GaugeTransport QuantumNLS.PhysicalTensor QuantumNLS.OccupationUnitary Filter

noncomputable section

/-- Exact norm equality for operators intertwined by a unitary. -/
lemma norm_eq_of_intertwine {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E)
    (B : F →L[ℂ] F) (h : ∀ v, e (A v) = B (e v)) : ‖A‖ = ‖B‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    calc ‖A v‖ = ‖e (A v)‖ := (e.norm_map _).symm
      _ = ‖B (e v)‖ := by rw [h]
      _ ≤ ‖B‖ * ‖e v‖ := B.le_opNorm _
      _ = ‖B‖ * ‖v‖ := by rw [e.norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro w
    calc ‖B w‖ = ‖e.symm (B w)‖ := (e.symm.norm_map _).symm
      _ = ‖A (e.symm w)‖ := by
          have := h (e.symm w)
          rw [e.apply_symm_apply] at this
          rw [← this, e.symm_apply_apply]
      _ ≤ ‖A‖ * ‖e.symm w‖ := A.le_opNorm _
      _ = ‖A‖ * ‖w‖ := by rw [e.symm.norm_map]

variable (L : ℝ) [Fact (0 < L)]

/-- The physical Wick operator `J_N^* N^{-d}(b^*)^β b^α J_N` (ungauged, Fourier occupation
realisation): the Hilbert Wick operator transported by the constructed `U3`/`U4`. -/
def physicalWick (N : ℕ) (f : Sym) : physSector L N →L[ℂ] physSector L N :=
  (physicalOccupation L N).symm.conjStarAlgEquiv (WHil N f)

theorem physicalOccupation_physicalWick (N : ℕ) (f : Sym) (v : physSector L N) :
    physicalOccupation L N (physicalWick L N f v) = WHil N f (physicalOccupation L N v) := by
  simp [physicalWick]

/-- The supplied-phase physical Wick operator: the physical operator rephased by the transported
supplied phases (`D_q^* · D_q` convention, as `physicalGaugedCollective`). -/
def physicalWickQ (N : ℕ) (q : Arr N → ℂ) (hq : ∀ m, Complex.normSq (q m) = 1) (f : Sym) :
    physSector L N →L[ℂ] physSector L N :=
  (physicalPhase L N q hq).symm.conjStarAlgEquiv (physicalWick L N f)

/-- The rephased physical operator is the gauged Hilbert Wick operator on the occupation carrier,
with the diagonal extension of the supplied phases. -/
theorem physicalOccupation_physicalWickQ (N : ℕ) (q : Arr N → ℂ) (hq : ∀ m, Complex.normSq (q m) = 1)
    (f : Sym) (v : physSector L N) :
    physicalOccupation L N (physicalWickQ L N q hq f v)
      = WHilq N (extendSectorGauge N q) (extendSectorGauge_unit N q hq) f
          (physicalOccupation L N v) := by
  simp only [physicalWickQ, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, physicalOccupation_phase_symm, physicalOccupation_physicalWick,
    physicalOccupation_phase]
  unfold WHilq
  rw [phaseUnitary_symm_apply, phase_conj_eq_gauge N q hq]
  rfl

/-- **Exact norm preservation** (ungauged). -/
theorem norm_physicalWick (N : ℕ) (f : Sym) : ‖physicalWick L N f‖ = ‖WHil N f‖ :=
  norm_eq_of_intertwine (physicalOccupation L N) _ _ (physicalOccupation_physicalWick L N f)

/-- **Exact norm preservation** with supplied phases. -/
theorem norm_physicalWickQ (N : ℕ) (q : Arr N → ℂ) (hq : ∀ m, Complex.normSq (q m) = 1) (f : Sym) :
    ‖physicalWickQ L N q hq f‖
      = ‖WHilq N (extendSectorGauge N q) (extendSectorGauge_unit N q hq) f‖ :=
  norm_eq_of_intertwine (physicalOccupation L N) _ _ (physicalOccupation_physicalWickQ L N q hq f)

/-! ### The norm limit on the physical sector -/

/-- **Norm limit on the physical Fourier sector with supplied phases.** For a balanced polynomial
symbol `f` with labels in `I` and arbitrary unit-modulus phases `q N : Arr N → ℂ`,
`‖J_N^* W^q_N(f) J_N‖ → sup_{‖z‖≤1} |f(z)|` (the transported Wick operator on
`Sym^N L²(𝕋_L)`; Fourier occupation realisation, no Bethe U5). -/
theorem physical_wick_norm_limit (q : ∀ N, Arr N → ℂ) (hq : ∀ N m, Complex.normSq (q N m) = 1)
    (I : Finset ℤ) {f : Sym} (hb : Balanced f) (hI : LabelsIn I f) :
    Tendsto (fun N => ‖physicalWickQ L N (q N) (hq N) f‖) atTop
      (nhds (SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f))) := by
  simp only [norm_physicalWickQ]
  exact wick_balanced_norm_limit (fun N => extendSectorGauge N (q N))
    (fun N => extendSectorGauge_unit N (q N) (hq N)) I hb hI

lemma gauge_eq_one (N : ℕ) (r : Occ → ℂ) (hr : UnitGauge r) (h1 : ∀ m, r m = 1) :
    gauge N r hr = 1 := by
  ext1 v
  apply lp.ext
  funext m
  simp [gauge_apply, h1]

lemma WHilq_one (N : ℕ) (hq : UnitGauge (fun _ : Occ => (1 : ℂ))) (h : Sym) :
    WHilq N (fun _ => 1) hq h = WHil N h := by
  unfold WHilq
  rw [gauge_eq_one N _ _ (fun m => by simp), gauge_eq_one N _ _ (fun m => rfl), one_mul, mul_one]

/-- The same norm limit for the ungauged physical Wick operator (all phases `1`). -/
theorem physical_wick_norm_limit_ungauged (I : Finset ℤ) {f : Sym} (hb : Balanced f)
    (hI : LabelsIn I f) :
    Tendsto (fun N => ‖physicalWick L N f‖) atTop
      (nhds (SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f))) := by
  have h := wick_balanced_norm_limit (fun _ : ℕ => fun _ : Occ => (1 : ℂ))
    (fun N => show UnitGauge (fun _ : Occ => (1 : ℂ)) from fun m => by simp) I hb hI
  simp only [norm_physicalWick]
  refine h.congr (fun N => ?_)
  rw [WHilq_one]

/-! ### Physical product states `u^{⊗N}` as the lower-bound test vectors -/

open QuantumNLS.TensorCarrier in
/-- The physical bosonic product state `u^{⊗N} ∈ Sym^N L²(𝕋_L)`. -/
def productState (N : ℕ) (u : L2T L) : physSector L N :=
  ⟨htpow N u, htpow_mem_symSector N u⟩

open QuantumNLS.TensorCarrier in
theorem norm_productState (N : ℕ) (u : L2T L) : ‖productState L N u‖ = ‖u‖ ^ N := by
  change ‖(htpow N u : HilbertTensorPower ℂ (L2T L) N)‖ = _
  exact norm_htpow N u

open QuantumNLS.TensorCarrier in
/-- **Physical test vectors.** For a finitely supported unit `ξ ∈ ℓ²(ℤ)` and
`u = F⁻¹ ξ ∈ L²(𝕋_L)` (physical Fourier normalisation), the actual `U3`/`U4` occupation image of
the physical product state `u^{⊗N}` is the coherent occupation vector. -/
theorem physicalOccupation_productState (ξ : OccupationUnitary.OneParticle)
    (hξ : (Function.support (ξ : ℤ → ℂ)).Finite) (N : ℕ) :
    physicalOccupation L N (productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ))
      = core N (cohSector hξ N) := by
  rw [core_cohSector ξ hξ N]
  have h : QuantumNLS.Fourier.fourierL2 L ((QuantumNLS.Fourier.fourierL2 L).symm ξ) = ξ :=
    LinearIsometryEquiv.apply_symm_apply _ _
  have e : (TensorFourier.U3 L N) (productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ))
      = ⟨htpow N ξ, htpow_mem_symSector N ξ⟩ := by
    unfold productState
    rw [TensorFourier.U3_htpow]
    exact Subtype.ext (by rw [h])
  change OccupationUnitary.U4 N ((TensorFourier.U3 L N) _) = _
  rw [e]

lemma inner_core_WHil {N : ℕ} (hN : 0 < N) {f : Sym} (hb : Balanced f) (v : Sector N) :
    inner ℂ (core N v) (WHil N f (core N v)) = ip (emb N v) (WN N f (emb N v)) := by
  rw [WHil_core hN hb, inner_core]
  unfold ipS
  rw [emb_WS hb]

/-- **Physical coherent expectation** (`eq:full-coherent-test`, physical form): for
`u = F⁻¹ξ`, `⟨u^{⊗N}, W_N(f) u^{⊗N}⟩ → f(ξ) = f(û)` for balanced `f`. -/
theorem physical_product_expectation_tendsto (ξ : OccupationUnitary.OneParticle)
    (hξ : (Function.support (ξ : ℤ → ℂ)).Finite) (h1 : ‖ξ‖ = 1) {f : Sym} (hb : Balanced f) :
    Tendsto (fun N : ℕ => inner ℂ (productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ))
        (physicalWick L N f (productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ))))
      atTop (nhds (evalSym (ξ : ℤ → ℂ) f)) := by
  have hT := coh_expect_tendsto hξ (coh_ip_self ξ hξ h1) hb
  refine hT.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN' : 0 < N := hN
  rw [← (physicalOccupation L N).inner_map_map, physicalOccupation_physicalWick,
    physicalOccupation_productState L ξ hξ N, inner_core_WHil hN' hb, emb_cohSector]

/-- Lower bound from the physical product states, for the ungauged physical Wick operator. -/
theorem physical_product_lower_bound (ξ : OccupationUnitary.OneParticle)
    (hξ : (Function.support (ξ : ℤ → ℂ)).Finite) (h1 : ‖ξ‖ = 1) {f : Sym} (hb : Balanced f)
    (hbdd : ∃ M : ℝ, ∀ N : ℕ, ‖physicalWick L N f‖ ≤ M) :
    ‖evalSym (ξ : ℤ → ℂ) f‖ ≤ liminf (fun N => ‖physicalWick L N f‖) atTop := by
  have hT := (physical_product_expectation_tendsto L ξ hξ h1 hb).norm
  have hu : ‖(QuantumNLS.Fourier.fourierL2 L).symm ξ‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, h1]
  have hle : ∀ N : ℕ, ‖inner ℂ (productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ))
        (physicalWick L N f (productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ)))‖
      ≤ ‖physicalWick L N f‖ := by
    intro N
    have hn : ‖productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ)‖ = 1 := by
      rw [norm_productState, hu, one_pow]
    calc _ ≤ ‖productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ)‖ *
          ‖physicalWick L N f (productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ))‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ)‖ *
          (‖physicalWick L N f‖ * ‖productState L N ((QuantumNLS.Fourier.fourierL2 L).symm ξ)‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖physicalWick L N f‖ := by rw [hn]; ring
  obtain ⟨M, hM⟩ := hbdd
  rw [← hT.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
    (Filter.isBoundedUnder_of ⟨0, fun N => norm_nonneg _⟩)
    (Filter.isCoboundedUnder_ge_of_le atTop (x := M) hM)

/-- Lower bound for the physical Wick operators with arbitrary supplied phases. -/
theorem physical_coherent_lower_bound (q : ∀ N, Arr N → ℂ) (hq : ∀ N m, Complex.normSq (q N m) = 1)
    {ξ : OccupationUnitary.OneParticle} (hξ : (Function.support (ξ : ℤ → ℂ)).Finite)
    (h1 : ‖ξ‖ = 1) {f : Sym} (hb : Balanced f) :
    ‖evalSym (ξ : ℤ → ℂ) f‖ ≤ liminf (fun N => ‖physicalWickQ L N (q N) (hq N) f‖) atTop := by
  have := coherent_lower_bound (fun N => extendSectorGauge N (q N))
    (fun N => extendSectorGauge_unit N (q N) (hq N)) hξ h1 hb
  simp only [norm_physicalWickQ]
  exact this

/-! Axiom audit (printed at compile time). -/
#print axioms norm_eq_of_intertwine
#print axioms physicalOccupation_physicalWick
#print axioms physicalOccupation_physicalWickQ
#print axioms norm_physicalWick
#print axioms norm_physicalWickQ
#print axioms physical_wick_norm_limit
#print axioms WHilq_one
#print axioms physical_wick_norm_limit_ungauged
#print axioms norm_productState
#print axioms physicalOccupation_productState
#print axioms inner_core_WHil
#print axioms physical_product_expectation_tendsto
#print axioms physical_product_lower_bound
#print axioms physical_coherent_lower_bound

end

end QuantumNLS.PhysicalWickLimit
