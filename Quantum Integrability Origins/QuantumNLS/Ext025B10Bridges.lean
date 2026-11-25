import QuantumNLS.Ext025B9Bridges
import QuantumNLS.EnergyPreparationDef
import QuantumNLS.Ext025B7GentleCompression

/-! GP-08: construct an atomic PVM on an arbitrary Hilbert basis and identify
its constructed Borel integral with the actual coefficient multiplier. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025B10Atomic
open BoundedBetheTransfer BetheChargeResolution Ext025B8SimpleCalculus Ext025B8BorelCalculus
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance (p : Prop) : Decidable p := Classical.propDecidable p
omit [CompleteSpace E] in
theorem projection_hasSum (b : HilbertBasis ι ℂ E) (s : Set (ι)) (x : E) :
    HasSum (fun m : s => b.repr x m • b m) (projection b s x) := by
  have hi : HasSum (s.indicator (fun m => b.repr x m • b m)) (projection b s x) := by
    convert (b.hasSum_repr x).mapL (projection b s) using 1
    funext m
    simp only [map_smul, projection_basis, Set.indicator_apply]
    split_ifs <;> simp
  exact hasSum_subtype_iff_indicator.mpr hi

/- Strong countable additivity, even for arbitrary indexed disjoint families.
The proof groups an unconditionally convergent Hilbert basis subseries. -/
omit [CompleteSpace E] in
theorem projection_iUnion_hasSum {J : Type*} (b : HilbertBasis ι ℂ E)
    (s : J → Set (ι)) (hs : Pairwise (Disjoint on s)) (x : E) :
    HasSum (fun j => projection b (s j) x) (projection b (⋃ j, s j) x) := by
  have hu := projection_hasSum b (⋃ j, s j) x
  have he := (Set.unionEqSigmaOfDisjoint hs).symm.hasSum_iff.mpr hu
  exact he.sigma (fun j => projection_hasSum b (s j) x)

/- Label projection intersection law. -/
omit [CompleteSpace E] in
theorem projection_inter (b : HilbertBasis ι ℂ E) (s t : Set (ι)) :
    projection b s * projection b t = projection b (s ∩ t) := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext m
  change b.repr (projection b s (projection b t x)) m = _
  simp only [projection_coord, Set.mem_inter_iff]
  split_ifs <;> simp_all

omit [CompleteSpace E] in
theorem projection_empty (b : HilbertBasis ι ℂ E) : projection b ∅ = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext m
  simp [projection_coord]

omit [CompleteSpace E] in
theorem projection_univ (b : HilbertBasis ι ℂ E) : projection b Set.univ = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext m
  simp [projection_coord]


/- A literal PVM, including repeated eigenvalues. -/
def resolution (b : HilbertBasis ι ℂ E) (a : ι → ℝ) : ProjectionMeasure E where
  toFun s := projection b (a ⁻¹' s)
  empty := by simpa using projection_empty b
  univ := by simpa using projection_univ b
  selfAdjoint s _ := projection_selfAdjoint b _
  inter s t _ _ := projection_inter b _ _
  additive s _ hs x := by
    simpa only [Set.preimage_iUnion] using projection_iUnion_hasSum b
      (fun n => a ⁻¹' s n) (fun i j hij => (hs hij).preimage a) x

theorem simple_basis (b : HilbertBasis ι ℂ E) (a : ι → ℝ)
    (f : SimpleFunc ℝ ℂ) (i : ι) :
    simple (resolution b a) f (b i) = f (a i) • b i := by
  have h := congrArg (fun T : E →L[ℂ] E => T (b i))
    (simple_local (resolution b a) f {a i} (measurableSet_singleton _) (f (a i))
      (fun t ht => congrArg f (Set.mem_singleton_iff.mp ht)))
  have hp : (resolution b a).toFun {a i} (b i) = b i := by
    simp [resolution,projection_basis]
  simpa only [mul_apply_eq_comp,smul_apply,hp] using h

/- Identify the constructed bounded Borel integral on each complete basis vector. -/
theorem bounded_basis (b : HilbertBasis ι ℂ E) (a : ι → ℝ)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) (i : ι) :
    bounded (resolution b a) f hf C hC hb (b i) = f (a i) • b i := by
  have hl := Ext025B8BorelLaws.approx_bounded (resolution b a) f hf C hC hb (b i)
  simp only [simple_basis] at hl
  exact tendsto_nhds_unique hl
    ((Ext025B8BorelLaws.approx_pointwise f hf (a i)).smul_const (b i))

/- Exact coefficients on the whole Hilbert space, not just a core. -/
theorem bounded_coord (b : HilbertBasis ι ℂ E) (a : ι → ℝ)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) (x : E) (i : ι) :
    b.repr (bounded (resolution b a) f hf C hC hb x) i = f (a i)*b.repr x i :=
  diagonal_coord b _ _ (bounded_basis b a f hf C hC hb) x i

end QuantumNLS.Ext025B10Atomic

/-! GP-08 physical bridge for R-C17D95AA. The Hamiltonian here is the
literal physical kinetic A_k = 1 - sum partial_j^2, not an assumed spectral
operator. Its PVM and bounded root cutoff are constructed, then identified
with the frozen physical A_k^(1/2) P_M on its exact domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace BigOperators ENNReal LinearPMap
namespace QuantumNLS.Ext025B10PhysicalEnergy
open EnergyPreparationDef Energy PhysicalEnergyTrace BoundedBetheTransfer
variable {L : ℝ} [Fact (0 < L)] {k : ℕ}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Actual Fourier basis on the physical tensor carrier. -/
def basis (L : ℝ) [Fact (0 < L)] (k : ℕ) : HilbertBasis (Mom k) ℂ (Xk L k) :=
  HilbertBasis.ofRepr (eK L k)

/-- Spectral PVM of the physical kinetic A_k. -/
def spectral (L : ℝ) [Fact (0 < L)] (k : ℕ) :=
  Ext025B10Atomic.resolution (basis L k) (kinWeight L k)

/-- The literal spectral projection 1_[1,M](A_k). -/
def cutoff (L : ℝ) [Fact (0 < L)] (k : ℕ) (M : ℝ) : Xk L k →L[ℂ] Xk L k :=
  (spectral L k).toFun (Set.Icc 1 M)

/-- The constructed PVM square-root cutoff. -/
abbrev root (L : ℝ) [Fact (0 < L)] (k : ℕ) (M : ℝ) :=
  Ext025B8EnergyCompression.rootCutoff (spectral L k) M

theorem cutoff_coord (M : ℝ) (x : Xk L k) (w : Mom k) :
    eK L k (cutoff L k M x) w =
      if kinWeight L k w ∈ Set.Icc 1 M then eK L k x w else 0 :=
  by
    simpa only [cutoff,spectral,Ext025B10Atomic.resolution,basis,Set.mem_preimage] using
      projection_coord (basis L k) (kinWeight L k ⁻¹' Set.Icc 1 M) x w

theorem root_coord (M : ℝ) (x : Xk L k) (w : Mom k) :
    eK L k (root L k M x) w =
      Ext025B8EnergyCompression.rootSymbol M (kinWeight L k w) * eK L k x w :=
  Ext025B10Atomic.bounded_coord (basis L k) (kinWeight L k) _ _ _ _ _ x w

/-- This PVM is supported on [1,infinity), directly from the physical weight. -/
theorem spectral_positive : (spectral L k).toFun (Set.Ici 1) = 1 := by
  have he : kinWeight L k ⁻¹' Set.Ici 1 = Set.univ := by
    ext w
    exact ⟨fun _ => Set.mem_univ w,fun _ => one_le_kinWeight L k w⟩
  change projection (basis L k) _ = 1
  rw [he,Ext025B10Atomic.projection_univ]

/-- W A_k^(1/2) P_M = P_M on the entire physical Hilbert space. -/
theorem W_root (M : ℝ) : W L k * root L k M = cutoff L k M := by
  ext x
  apply (eK L k).injective
  ext w
  rw [mul_apply_eq_comp,eK_W,root_coord,cutoff_coord]
  by_cases hw : kinWeight L k w ∈ Set.Icc 1 M
  · rw [Ext025B8EnergyCompression.rootSymbol,Set.indicator_of_mem hw,ite_eq_left hw]
    change (((kinSqrt L k w)⁻¹ : ℝ) : ℂ) * ((kinSqrt L k w : ℂ) * _) = _
    push_cast
    rw [← mul_assoc,inv_mul_cancel₀,one_mul]
    exact_mod_cast (ne_of_gt (zero_lt_one.trans_le (one_le_kinSqrt L k w)))
  · rw [Ext025B8EnergyCompression.rootSymbol,Set.indicator_of_notMem hw,ite_eq_right hw,zero_mul,mul_zero]

/-- The bounded root cutoff commutes with W, with the same literal product. -/
theorem root_W (M : ℝ) : root L k M * W L k = cutoff L k M := by
  ext x
  apply (eK L k).injective
  ext w
  have h := congrArg (fun T : Xk L k →L[ℂ] Xk L k => eK L k (T x) w) (W_root (L := L) (k := k) M)
  simp only [mul_apply_eq_comp,eK_W,root_coord] at h ⊢
  rw [← h]
  ring

/-- Every spectral-cutoff input belongs to the *physical* form domain. -/
theorem cutoff_mem (M : ℝ) (x : Xk L k) : cutoff L k M x ∈ (AhalfT L k).domain := by
  rw [← W_root]
  exact W_mem _

/-- Required physical identification A_k^(1/2) P_M = the constructed bounded
sqrt(t) 1_[1,M](t) integral. No domain or action identity is assumed. -/
theorem physical_root_cutoff (M : ℝ) (x : Xk L k) :
    AhalfT L k ⟨cutoff L k M x,cutoff_mem M x⟩ = root L k M x := by
  have he : (⟨cutoff L k M x,cutoff_mem M x⟩ : (AhalfT L k).domain) =
      ⟨W L k (root L k M x),W_mem _⟩ := by
    apply Subtype.ext
    exact (congrArg (fun T : Xk L k →L[ℂ] Xk L k => T x) (W_root M)).symm
  rw [he,AhalfT_W]

/-- Compactness needs no compact-resolvent assumption. -/
theorem compact_compression (K : Xk L k →L[ℂ] Xk L k) (hK : IsCompactOperator K) :
    Tendsto (fun n : ℕ => ‖K-cutoff L k n*K*cutoff L k n‖) atTop (𝓝 0) :=
  by
    have h := Ext025B7SpectralCompression.positive_compact_compression
      (spectral L k) spectral_positive K hK
    have hc : Tendsto (fun _ : ℕ => K) atTop (𝓝 K) := tendsto_const_nhds
    have hn := (hc.sub h).norm
    simpa only [cutoff,sub_self,norm_zero] using hn

/-- The uniform-tail step on the actual compact form-vector image.
The set K can be the compact image of t ↦ A_k^(1/2) f(t). -/
theorem compact_vector_tails (K : Set (Xk L k)) (hK : IsCompact K) :
    TendstoUniformly (fun n : ℕ => fun x : K => cutoff L k n x.val)
      (fun x => x.val) atTop := by
  have h := Ext025B7SpectralCompression.exhaustion_uniform_compact (spectral L k)
    (fun n : ℕ => Set.Iic (n : ℝ)) (fun _ => measurableSet_Iic)
    (fun i j hij => Set.Iic_subset_Iic.mpr (Nat.cast_le.mpr hij))
    (show (⋃ n : ℕ, Set.Iic (n : ℝ)) = Set.univ by
      apply Set.eq_univ_of_forall
      intro t
      obtain ⟨n,hn⟩ := exists_nat_ge t
      exact Set.mem_iUnion.mpr ⟨n,hn⟩) K hK
  simpa only [cutoff,Ext025B7SpectralCompression.positive_windows_eq
    (spectral L k) spectral_positive] using h

/-- The literal M ||K|| bound for the physical truncated form. -/
theorem physical_sandwich_norm (M : ℝ) (hM : 0 ≤ M) (K : Xk L k →L[ℂ] Xk L k) :
    ‖root L k M*K*root L k M‖ ≤ M*‖K‖ :=
  Ext025B8EnergyCompression.sandwich_norm (spectral L k) M hM K

/-- Existing finite-energy form realization, now bound to the *same* physical
cutoffs: P_M T P_M = (A_k^(1/2)P_M) rho (A_k^(1/2)P_M). -/
theorem physical_trace_bridge (ρ : Xk L k →L[ℂ] Xk L k) (hρ : ρ.IsPositive)
    (hE : energyTrace ρ ≠ ⊤) :
    ∃ T, T.IsPositive ∧ TraceClass.IsTraceClass T ∧ IsFormRealization ρ T ∧
      TraceClass.posTrace T = energyTrace ρ ∧
      ∀ M : ℝ, cutoff L k M*T*cutoff L k M = root L k M*ρ*root L k M := by
  obtain ⟨T,hT,htc,hr,htr,_⟩ := positive_formRealization hρ hE
  refine ⟨T,hT,htc,hr,htr,fun M => ?_⟩
  rw [(isFormRealization_iff ρ T).mp hr]
  simp only [← mul_assoc]
  rw [root_W]
  simp only [mul_assoc]
  rw [W_root]

end QuantumNLS.Ext025B10PhysicalEnergy

/-! GP-09 / R-6EA807B1: construct the actual physical finite-energy
sandwich family and bind its compressed convergence to ordinary physical
trace-norm convergence. The source's uniform complementary-trace passage
and final gentle-limit assembly are not assumed as premises. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace BigOperators ENNReal LinearPMap
namespace QuantumNLS.Ext025B10EnergyFamily
open EnergyPreparationDef Ext025B10PhysicalEnergy TraceClass TraceIdeal
variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- Positive physical densities with finite physical A_k expectation. -/
def FiniteEnergy (L : ℝ) [Fact (0 < L)] (k : ℕ) :=
  {ρ : Xk L k →L[ℂ] Xk L k // ρ.IsPositive ∧ energyTrace ρ ≠ ⊤}

/-- The sandwich is constructed from the physical form realization theorem. -/
def sandwich (ρ : FiniteEnergy L k) : Xk L k →L[ℂ] Xk L k :=
  (physical_trace_bridge ρ.val ρ.property.1 ρ.property.2).choose

theorem sandwich_spec (ρ : FiniteEnergy L k) :
    (sandwich ρ).IsPositive ∧ IsTraceClass (sandwich ρ) ∧
    IsFormRealization ρ.val (sandwich ρ) ∧
    posTrace (sandwich ρ) = energyTrace ρ.val ∧
    ∀ M : ℝ, cutoff L k M*sandwich ρ*cutoff L k M = root L k M*ρ.val*root L k M :=
  (physical_trace_bridge ρ.val ρ.property.1 ρ.property.2).choose_spec

/-- Source compressed difference identity, with actual physical densities
and constructed sandwiches, rather than independently supplied B_n. -/
theorem compressed_difference (ρ σ : FiniteEnergy L k) (M : ℝ) :
    cutoff L k M*(sandwich ρ-sandwich σ)*cutoff L k M =
      root L k M*(ρ.val-σ.val)*root L k M := by
  rw [mul_sub,sub_mul,(sandwich_spec ρ).2.2.2.2 M,(sandwich_spec σ).2.2.2.2 M,
    mul_sub,sub_mul]

theorem compression_bound (ρ σ : FiniteEnergy L k) (M : ℝ) (hM : 0 ≤ M) :
    traceNorm (cutoff L k M*(sandwich ρ-sandwich σ)*cutoff L k M) ≤
      ENNReal.ofReal M*traceNorm (ρ.val-σ.val) := by
  rw [compressed_difference]
  have hn := Ext025B8EnergyCompression.rootCutoff_norm (spectral L k) M
  have he : ENNReal.ofReal ‖root L k M‖ ≤ ENNReal.ofReal (Real.sqrt M) :=
    ENNReal.ofReal_le_ofReal hn
  calc
    _ ≤ ENNReal.ofReal ‖root L k M‖*traceNorm (ρ.val-σ.val)*ENNReal.ofReal ‖root L k M‖ :=
      traceNorm_mul_mul_le _ _ _
    _ ≤ ENNReal.ofReal (Real.sqrt M)*traceNorm (ρ.val-σ.val)*ENNReal.ofReal (Real.sqrt M) := by
      gcongr
    _ = ENNReal.ofReal M*traceNorm (ρ.val-σ.val) := by
      rw [mul_right_comm,← ENNReal.ofReal_mul (Real.sqrt_nonneg M),← pow_two,
        Real.sq_sqrt hM]

/-- Uniformity in the source parameter is preserved by the literal M bound. -/
theorem uniform_compressed_convergence {T : Type*}
    (ρ : ℕ → T → FiniteEnergy L k) (σ : T → FiniteEnergy L k)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ n t).val-(σ t).val) ≤ ENNReal.ofReal ε)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm (cutoff L k M*(sandwich (ρ n t)-sandwich (σ t))*cutoff L k M) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  have hMp : 0 < M+1 := by linarith
  filter_upwards [h (ε/(M+1)) (div_pos hε hMp)] with n hn
  intro t
  calc
    _ ≤ ENNReal.ofReal M*traceNorm ((ρ n t).val-(σ t).val) :=
      compression_bound _ _ M hM
    _ ≤ ENNReal.ofReal M*ENNReal.ofReal (ε/(M+1)) := by gcongr; exact hn t
    _ = ENNReal.ofReal (M*(ε/(M+1))) := (ENNReal.ofReal_mul hM).symm
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      have he := (div_mul_cancel₀ ε (ne_of_gt hMp))
      nlinarith [div_pos hε hMp]

end QuantumNLS.Ext025B10EnergyFamily
#print axioms QuantumNLS.Ext025B10Atomic.resolution
#print axioms QuantumNLS.Ext025B10Atomic.bounded_coord
#print axioms QuantumNLS.Ext025B10PhysicalEnergy.physical_root_cutoff
#print axioms QuantumNLS.Ext025B10PhysicalEnergy.physical_trace_bridge
#print axioms QuantumNLS.Ext025B10PhysicalEnergy.compact_vector_tails
#print axioms QuantumNLS.Ext025B10EnergyFamily.sandwich_spec
#print axioms QuantumNLS.Ext025B10EnergyFamily.compression_bound
#print axioms QuantumNLS.Ext025B10EnergyFamily.uniform_compressed_convergence
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B10" then
      pending := pending.push n
      roots := roots + 1
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
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Ext025B10Bridges audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
