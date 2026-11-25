import QuantumNLS.FidelitySource
import QuantumNLS.ExactDensity

/-! R-93D28FE1, prop:stability, projective_reconstruction.tex:183–226.
Read-only accepted FidelitySource bee0b8bb and ExactDensity 388d49e7.
The full overlap estimate is obtained by trace-norm duality for the difference
of two pure states and its partial trace; then the elementary unit-vector bound.
-/
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate ENNReal
open QuantumNLS.TraceClass QuantumNLS.TensorCarrier
noncomputable section
namespace QuantumNLS.PreparationStability

section Duality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Trace-norm duality for the finite-rank selfadjoint input used in the source.
The eigenbasis and its trace norm are those proved in the accepted fidelity chain. -/
theorem quadratic_pairing_le (v z : E) (Z : E →L[ℂ] E) (hZ : ‖Z‖ ≤ 1) :
    ‖⟪v, Z v⟫_ℂ - ⟪z, Z z⟫_ℂ‖ ≤ ∑ i, |RankTwoTrace.eigval v z i| := by
  classical
  let u := RankTwoTrace.eigvec v z
  have hex : ∀ w ∈ RankTwoTrace.spanVZ v z,
      ∑ i, ⟪w, u i⟫_ℂ * ⟪u i, Z w⟫_ℂ = ⟪w, Z w⟫_ℂ := by
    intro w hw
    calc ∑ i, ⟪w, u i⟫_ℂ * ⟪u i, Z w⟫_ℂ
        = ⟪∑ i, ⟪u i, w⟫_ℂ • u i, Z w⟫_ℂ := by
          rw [sum_inner]
          simp only [inner_smul_left, inner_conj_symm]
      _ = _ := by rw [RankTwoTrace.expand_mem v z hw]
  have he : ∑ i, ⟪u i, Z (RankTwoTrace.rankTwo v z (u i))⟫_ℂ =
      ⟪v, Z v⟫_ℂ - ⟪z, Z z⟫_ℂ := by
    simp only [RankTwoTrace.rankTwo_apply, map_sub, map_smul, inner_sub_right, inner_smul_right]
    rw [Finset.sum_sub_distrib, hex v (RankTwoTrace.v_mem v z), hex z (RankTwoTrace.z_mem v z)]
  rw [← he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [RankTwoTrace.rankTwo_eigvec, map_smul, inner_smul_right, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hu : ‖u i‖ = 1 := (RankTwoTrace.eigvec_orthonormal v z).norm_eq_one i
  have hi : ‖⟪u i, Z (u i)⟫_ℂ‖ ≤ 1 := by
    apply (norm_inner_le_norm _ _).trans
    have hz := Z.le_opNorm (u i)
    rw [hu] at hz ⊢
    nlinarith
  nlinarith [abs_nonneg (RankTwoTrace.eigval v z i)]

end Duality

section PartialTrace
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

theorem reducedDensity_contraction (ψ φ : HilbertTensor ℂ X Y) :
    traceNorm (reducedDensity ψ - reducedDensity φ) ≤
      traceNorm (InnerProductSpace.rankOne ℂ ψ ψ - InnerProductSpace.rankOne ℂ φ φ) := by
  change _ ≤ traceNorm (RankTwoTrace.rankTwo ψ φ)
  rw [RankTwoTrace.rankTwo_eq_diag ψ φ,
    RankTwoTrace.traceNorm_diag _ (RankTwoTrace.eigvec_orthonormal ψ φ)]
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ X
  refine traceNorm_le_of_forall b _ fun Xop hX s => ?_
  set M : X →L[ℂ] X := ∑ i ∈ s, InnerProductSpace.rankOne ℂ (Xop (b i)) (b i) with hM
  have hMnorm : ‖M‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    have e : M x = Xop (∑ i ∈ s, ⟪b i, x⟫_ℂ • b i) := by
      rw [hM, sum_apply, map_sum]
      simp [InnerProductSpace.rankOne_apply, map_smul]
    rw [e, one_mul]
    exact (Xop.le_opNorm _).trans ((mul_le_mul hX (norm_sum_inner_smul_le b s x)
      (norm_nonneg _) zero_le_one).trans (by rw [one_mul]))
  set Z := htmap M (ContinuousLinearMap.id ℂ Y) with hZ
  have hZnorm : ‖Z‖ ≤ 1 :=
    (norm_htmap_le _ _).trans (by
      have := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Y)
      nlinarith [norm_nonneg M, norm_nonneg (ContinuousLinearMap.id ℂ Y)])
  have hsum : ∀ χ : HilbertTensor ℂ X Y,
      ∑ i ∈ s, ⟪Xop (b i), reducedDensity χ (b i)⟫_ℂ = (starRingEnd ℂ) ⟪χ, Z χ⟫_ℂ := by
    intro χ
    have e1 : ∀ i, ⟪Xop (b i), reducedDensity χ (b i)⟫_ℂ = (starRingEnd ℂ)
        ⟪χ, htmap (InnerProductSpace.rankOne ℂ (Xop (b i)) (b i))
          (ContinuousLinearMap.id ℂ Y) χ⟫_ℂ := by
      intro i
      rw [← inner_reducedDensity_left, inner_conj_symm]
    simp_rw [e1]
    rw [← map_sum, ← inner_sum, ← sum_apply, ← htmap_sum_left, ← hM]
  have hdiff : ∑ i ∈ s, ⟪Xop (b i), (reducedDensity ψ - reducedDensity φ) (b i)⟫_ℂ =
      (starRingEnd ℂ) (⟪ψ, Z ψ⟫_ℂ - ⟪φ, Z φ⟫_ℂ) := by
    simp_rw [sub_apply, inner_sub_right]
    rw [Finset.sum_sub_distrib, hsum, hsum, map_sub]
  rw [hdiff]
  refine (RCLike.re_le_norm _).trans ?_
  rw [RCLike.norm_conj]
  exact quadratic_pairing_le ψ φ Z hZnorm

/-- Exact fidelity form of the partial-trace estimate. -/
theorem reducedDensity_overlap (ψ φ : HilbertTensor ℂ X Y)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (reducedDensity ψ - reducedDensity φ) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) := by
  exact (reducedDensity_contraction ψ φ).trans_eq
    (RankTwoTrace.traceNorm_unit_sub_eq ψ φ hψ hφ)

end PartialTrace
section OccupationIsometry
open QuantumNLS.Occupation QuantumNLS.OccupationHilbert
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.ExactDensity
variable {q : ℕ}

/-- Coefficients of the source isometry, indexed by every pair `(a,ν)`. -/
def pairEntry (d : H (1 + q)) (p : ℤ × Arr q) : ℂ := vEntry d p.2 p.1

theorem pairEntry_sum (d : H (1 + q)) :
    ∑' p : ℤ × Arr q, ENNReal.ofReal (‖pairEntry d p‖ ^ 2) = ENNReal.ofReal (‖d‖ ^ 2) := by
  rw [ENNReal.tsum_prod']
  exact tsum_tsum_vEntry d

theorem pairEntry_mem (d : H (1 + q)) : Memℓp (pairEntry d) 2 := by
  have h : ∑' p : ℤ × Arr q, ENNReal.ofReal (‖pairEntry d p‖ ^ 2) ≠ ⊤ := by
    rw [pairEntry_sum]; exact ENNReal.ofReal_ne_top
  have hs := ENNReal.summable_toReal h
  rw [memℓp_gen_iff (by norm_num)]
  simpa [Real.rpow_two, ENNReal.toReal_ofReal (sq_nonneg _)] using hs

/-- The same coefficient vector in `ℓ²(ℤ × 𝓜_{N-1})`. -/
def pairVector (d : H (1 + q)) : lp (fun _ : ℤ × Arr q => ℂ) 2 :=
  ⟨pairEntry d, pairEntry_mem d⟩

theorem pairVector_norm (d : H (1 + q)) : ‖pairVector d‖ = ‖d‖ := by
  have hs := (lp_sq_hasSum (pairVector d)).summable
  have he : ENNReal.ofReal (‖pairVector d‖ ^ 2) = ENNReal.ofReal (‖d‖ ^ 2) := by
    rw [← (lp_sq_hasSum (pairVector d)).tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs]
    exact pairEntry_sum d
  have he' : ‖pairVector d‖ ^ 2 = ‖d‖ ^ 2 := by
    have ht := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ht
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 he'

/-- Linearity of the displayed source isometry. -/
def pairLinear : H (1 + q) →ₗ[ℂ] lp (fun _ : ℤ × Arr q => ℂ) 2 where
  toFun := pairVector
  map_add' d e := by
    apply Subtype.ext; funext p
    change pairEntry (d + e) p = pairEntry d p + pairEntry e p
    simp [pairEntry, vEntry, mul_add]
  map_smul' c d := by
    apply Subtype.ext; funext p
    simp [pairVector, pairEntry, vEntry, mul_left_comm]

/-- The trace-sum computation proves isometry without a unit-norm restriction. -/
def pairIsometry : H (1 + q) →ₗᵢ[ℂ] lp (fun _ : ℤ × Arr q => ℂ) 2 where
  toLinearMap := pairLinear
  norm_map' := pairVector_norm

/-- The canonical environment `ℓ²(𝓜_{N-1})` basis. -/
def environmentBasis (q : ℕ) : HilbertBasis (Arr q) ℂ (H q) := default

/-- The joint one-body/environment tensor basis. -/
def jointBasis (q : ℕ) : HilbertBasis (ℤ × Arr q) ℂ (HilbertTensor ℂ OneParticle (H q)) :=
  htmulBasis oneBasis (environmentBasis q)

/-- The actual source `V_N d = ∑_ν v_ν ⊗ e_ν`, constructed by its square-summable
coefficients in the completed Hilbert tensor product. -/
def V (q : ℕ) : H (1 + q) →ₗᵢ[ℂ] HilbertTensor ℂ OneParticle (H q) :=
  (jointBasis q).repr.symm.toLinearIsometry.comp pairIsometry

theorem V_coeff (d : H (1 + q)) (a : ℤ) (ν : Arr q) :
    ⟪htmul (oneBasis a) (environmentBasis q ν), V q d⟫_ℂ = vEntry d ν a := by
  have hb : jointBasis q (a, ν) = htmul (oneBasis a) (environmentBasis q ν) :=
    htmulBasis_apply oneBasis (environmentBasis q) (a, ν)
  rw [← hb]
  rw [← HilbertBasis.repr_apply_apply]
  change (jointBasis q).repr ((jointBasis q).repr.symm (pairVector d)) (a, ν) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem inner_reducedDensity_contract {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (ψ : HilbertTensor ℂ X Y) (x y : X) :
    ⟪x, reducedDensity ψ y⟫_ℂ =
      ⟪htmap (InnerProductSpace.rankOne ℂ (1 : ℂ) y) (ContinuousLinearMap.id ℂ Y) ψ,
        htmap (InnerProductSpace.rankOne ℂ (1 : ℂ) x) (ContinuousLinearMap.id ℂ Y) ψ⟫_ℂ := by
  rw [← inner_conj_symm, inner_reducedDensity_left]
  rw [← inner_conj_symm (htmap _ _ ψ), ← ContinuousLinearMap.adjoint_inner_right]
  rw [adjoint_htmap, InnerProductSpace.adjoint_rankOne, ContinuousLinearMap.adjoint_id,
    ← ContinuousLinearMap.comp_apply, ← htmap_comp, InnerProductSpace.rankOne_comp_rankOne]
  simp

/-- The source identification `Γ[d] = Tr₂ |V_N d⟩⟨V_N d|`. -/
theorem Gamma_eq_reducedDensity (d : H (1 + q)) : Gamma d = reducedDensity (V q d) := by
  have he : ∀ a c : ℤ, ⟪oneBasis a, Gamma d (oneBasis c)⟫_ℂ =
      ⟪oneBasis a, reducedDensity (V q d) (oneBasis c)⟫_ℂ := by
    intro a c
    let b0 : HilbertBasis Unit ℂ ℂ := (OrthonormalBasis.singleton Unit ℂ).toHilbertBasis
    have hb0 : ∀ u, b0 u = 1 := by
      intro u; simp [b0, OrthonormalBasis.coe_toHilbertBasis, OrthonormalBasis.singleton_apply]
    rw [inner_Gamma, inner_reducedDensity_contract,
      ← (htmulBasis b0 (environmentBasis q)).tsum_inner_mul_inner]
    rw [((htmulBasis b0 (environmentBasis q)).summable_inner_mul_inner _ _).tsum_prod]
    simp only [htmulBasis_apply, hb0, ← inner_conj_symm
      (htmap (InnerProductSpace.rankOne ℂ (1 : ℂ) (oneBasis c))
        (ContinuousLinearMap.id ℂ (H q)) (V q d)), inner_htmul_one_contract, V_coeff]
    simp [mul_comm]
  apply lp.ext_continuousLinearMap (by norm_num)
  intro c
  apply ContinuousLinearMap.ext
  intro z
  change Gamma d (lp.single 2 c z) = reducedDensity (V q d) (lp.single 2 c z)
  have hs : (lp.single 2 c z : OneParticle) = z • oneBasis c := by
    rw [QuantumNLS.OccupationUnitary.oneBasis_apply, ← lp.single_smul]
    simp
  rw [hs, map_smul, map_smul]
  congr 1
  apply oneBasis.repr.injective
  ext a
  simpa only [HilbertBasis.repr_apply_apply] using he a c

end OccupationIsometry
section UnitVectorEstimate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The second inequality of eq:density-stability, with the intermediate source
inequalities `1-|s|² ≤ 2(1-|s|) ≤ 2(1-Re s) = ‖ψ-φ‖²`. -/
theorem overlap_le_distance (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2) ≤ 2 * ‖ψ - φ‖ := by
  have hn : ‖⟪ψ, φ⟫_ℂ‖ ≤ 1 := by simpa [hψ, hφ] using norm_inner_le_norm (𝕜 := ℂ) ψ φ
  have hr : (⟪ψ, φ⟫_ℂ).re ≤ ‖⟪ψ, φ⟫_ℂ‖ := Complex.re_le_norm _
  have he := norm_sub_sq (𝕜 := ℂ) ψ φ
  rw [hψ, hφ] at he
  change ‖ψ - φ‖ ^ 2 = 1 ^ 2 - 2 * (⟪ψ, φ⟫_ℂ).re + 1 ^ 2 at he
  have hnon : 0 ≤ 1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
    nlinarith [norm_nonneg (⟪ψ, φ⟫_ℂ)]
  have hs := Real.sq_sqrt hnon
  have hs0 := Real.sqrt_nonneg (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)
  have hd0 := norm_nonneg (ψ - φ)
  have h1 : 1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2 ≤ 2 * (1 - ‖⟪ψ, φ⟫_ℂ‖) := by
    nlinarith [sq_nonneg (1 - ‖⟪ψ, φ⟫_ℂ‖)]
  have h2 : 2 * (1 - ‖⟪ψ, φ⟫_ℂ‖) ≤ 2 * (1 - (⟪ψ, φ⟫_ℂ).re) := by linarith
  have hsqd : Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2) ^ 2 ≤ ‖ψ - φ‖ ^ 2 := by
    nlinarith
  have hle := (sq_le_sq₀ hs0 hd0).1 hsqd
  linarith

end UnitVectorEstimate

section Physical
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform
  QuantumNLS.BetheOccupationGauge QuantumNLS.CartesianOccupationTransfer
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
variable {L : ℝ} [Fact (0 < L)] {q : ℕ}

/-- The actual positive trace-class auxiliary density of the accepted exact-density
construction. The complete physical basis and gauge are explicit parameters. -/
def density (b : BetheBasis L (1 + q)) (g : Gauge) (ψ : HN L (1 + q)) :
    OneParticle →L[ℂ] OneParticle := ExactDensity.Gamma (coordinates b g ψ)

theorem density_entry (b : BetheBasis L (1 + q)) (g : Gauge) (ψ : HN L (1 + q)) (a c : ℤ) :
    ⟪oneBasis a, density b g ψ (oneBasis c)⟫_ℂ = AuxiliaryDensity.gammaEntry b g ψ a c := by
  rw [density, ExactDensity.inner_Gamma, AuxiliaryDensity.gammaEntry_eq_coefficient]
  exact (ExactDensity.inner_E_eq_tsum (coordinates b g ψ) a c).symm

/-- The isometry `V_N J_N` appearing in the printed proof. -/
def physicalV (b : BetheBasis L (1 + q)) (g : Gauge) :
    HN L (1 + q) →ₗᵢ[ℂ] HilbertTensor ℂ OneParticle (OccupationHilbert.H q) :=
  (V q).comp (coordinates b g).toLinearIsometry

theorem density_partialTrace (b : BetheBasis L (1 + q)) (g : Gauge) (ψ : HN L (1 + q)) :
    density b g ψ = reducedDensity (physicalV b g ψ) :=
  Gamma_eq_reducedDensity (coordinates b g ψ)

/-- R-93D28FE1, literally eq:density-stability for arbitrary two unit physical
preparations, including the exact fidelity overlap bound. -/
theorem stability (b : BetheBasis L (1 + q)) (g : Gauge)
    (ψ φ : HN L (1 + q)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (density b g ψ - density b g φ) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) ∧
    ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) ≤
      ENNReal.ofReal (2 * ‖ψ - φ‖) := by
  constructor
  · rw [density_partialTrace, density_partialTrace]
    have hp : ‖physicalV b g ψ‖ = 1 := by rw [LinearIsometry.norm_map, hψ]
    have hf : ‖physicalV b g φ‖ = 1 := by rw [LinearIsometry.norm_map, hφ]
    simpa only [LinearIsometry.inner_map_map] using
      reducedDensity_overlap (physicalV b g ψ) (physicalV b g φ) hp hf
  · exact ENNReal.ofReal_le_ofReal (overlap_le_distance ψ φ hψ hφ)

/-- Common arbitrary unitary evolution preserves the overlap and distance. -/
theorem common_unitary {T : Type*} (b : BetheBasis L (1 + q)) (g : Gauge)
    (U : T → HN L (1 + q) ≃ₗᵢ[ℂ] HN L (1 + q))
    (ψ φ : HN L (1 + q)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (t : T) :
    traceNorm (density b g (U t ψ) - density b g (U t φ)) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) := by
  have hp : ‖U t ψ‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hψ]
  have hf : ‖U t φ‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hφ]
  simpa only [LinearIsometryEquiv.inner_map_map] using (stability b g (U t ψ) (U t φ) hp hf).1

/-- Uniformity on every parameter set, without continuity, energy, or domain
hypotheses on the preparations or on the unitary family. -/
theorem uniform_stability {T : Type*} (b : BetheBasis L (1 + q)) (g : Gauge)
    (U : T → HN L (1 + q) ≃ₗᵢ[ℂ] HN L (1 + q))
    (ψ φ : HN L (1 + q)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (K : Set T) :
    (⨆ t : K, traceNorm (density b g (U t ψ) - density b g (U t φ))) ≤
      ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) ∧
    ENNReal.ofReal (2 * Real.sqrt (1 - ‖⟪ψ, φ⟫_ℂ‖ ^ 2)) ≤
      ENNReal.ofReal (2 * ‖ψ - φ‖) := by
  exact ⟨iSup_le (fun t => common_unitary b g U ψ φ hψ hφ t),
    (stability b g ψ φ hψ hφ).2⟩

end Physical
end QuantumNLS.PreparationStability

#print axioms QuantumNLS.PreparationStability.quadratic_pairing_le
#print axioms QuantumNLS.PreparationStability.reducedDensity_contraction
#print axioms QuantumNLS.PreparationStability.reducedDensity_overlap
#print axioms QuantumNLS.PreparationStability.pairEntry
#print axioms QuantumNLS.PreparationStability.pairEntry_sum
#print axioms QuantumNLS.PreparationStability.pairEntry_mem
#print axioms QuantumNLS.PreparationStability.pairVector
#print axioms QuantumNLS.PreparationStability.pairVector_norm
#print axioms QuantumNLS.PreparationStability.pairLinear
#print axioms QuantumNLS.PreparationStability.pairIsometry
#print axioms QuantumNLS.PreparationStability.environmentBasis
#print axioms QuantumNLS.PreparationStability.jointBasis
#print axioms QuantumNLS.PreparationStability.V
#print axioms QuantumNLS.PreparationStability.V_coeff
#print axioms QuantumNLS.PreparationStability.inner_reducedDensity_contract
#print axioms QuantumNLS.PreparationStability.Gamma_eq_reducedDensity
#print axioms QuantumNLS.PreparationStability.overlap_le_distance
#print axioms QuantumNLS.PreparationStability.density
#print axioms QuantumNLS.PreparationStability.density_entry
#print axioms QuantumNLS.PreparationStability.physicalV
#print axioms QuantumNLS.PreparationStability.density_partialTrace
#print axioms QuantumNLS.PreparationStability.stability
#print axioms QuantumNLS.PreparationStability.common_unitary
#print axioms QuantumNLS.PreparationStability.uniform_stability

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.PreparationStability.quadratic_pairing_le,
    ``QuantumNLS.PreparationStability.reducedDensity_contraction,
    ``QuantumNLS.PreparationStability.reducedDensity_overlap,
    ``QuantumNLS.PreparationStability.pairEntry,
    ``QuantumNLS.PreparationStability.pairEntry_sum,
    ``QuantumNLS.PreparationStability.pairEntry_mem,
    ``QuantumNLS.PreparationStability.pairVector,
    ``QuantumNLS.PreparationStability.pairVector_norm,
    ``QuantumNLS.PreparationStability.pairLinear,
    ``QuantumNLS.PreparationStability.pairIsometry,
    ``QuantumNLS.PreparationStability.environmentBasis,
    ``QuantumNLS.PreparationStability.jointBasis,
    ``QuantumNLS.PreparationStability.V,
    ``QuantumNLS.PreparationStability.V_coeff,
    ``QuantumNLS.PreparationStability.inner_reducedDensity_contract,
    ``QuantumNLS.PreparationStability.Gamma_eq_reducedDensity,
    ``QuantumNLS.PreparationStability.overlap_le_distance,
    ``QuantumNLS.PreparationStability.density,
    ``QuantumNLS.PreparationStability.density_entry,
    ``QuantumNLS.PreparationStability.physicalV,
    ``QuantumNLS.PreparationStability.density_partialTrace,
    ``QuantumNLS.PreparationStability.stability,
    ``QuantumNLS.PreparationStability.common_unitary,
    ``QuantumNLS.PreparationStability.uniform_stability]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PreparationStability." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Result nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.PreparationStability.quadratic_pairing_le,
    ``QuantumNLS.PreparationStability.reducedDensity_contraction,
    ``QuantumNLS.PreparationStability.reducedDensity_overlap,
    ``QuantumNLS.PreparationStability.pairEntry,
    ``QuantumNLS.PreparationStability.pairEntry_sum,
    ``QuantumNLS.PreparationStability.pairEntry_mem,
    ``QuantumNLS.PreparationStability.pairVector,
    ``QuantumNLS.PreparationStability.pairVector_norm,
    ``QuantumNLS.PreparationStability.pairLinear,
    ``QuantumNLS.PreparationStability.pairIsometry,
    ``QuantumNLS.PreparationStability.environmentBasis,
    ``QuantumNLS.PreparationStability.jointBasis,
    ``QuantumNLS.PreparationStability.V,
    ``QuantumNLS.PreparationStability.V_coeff,
    ``QuantumNLS.PreparationStability.inner_reducedDensity_contract,
    ``QuantumNLS.PreparationStability.Gamma_eq_reducedDensity,
    ``QuantumNLS.PreparationStability.overlap_le_distance,
    ``QuantumNLS.PreparationStability.density,
    ``QuantumNLS.PreparationStability.density_entry,
    ``QuantumNLS.PreparationStability.physicalV,
    ``QuantumNLS.PreparationStability.density_partialTrace,
    ``QuantumNLS.PreparationStability.stability,
    ``QuantumNLS.PreparationStability.common_unitary,
    ``QuantumNLS.PreparationStability.uniform_stability]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n == ``QuantumNLS.BetheConditionalBasis.AbstractContinuity then
        throwError "Generic definition reached EXT-001 premise: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; {checked.size} generic constants independent of EXT-001. Concrete instantiations require its explicit Prop hypothesis only."
