import QuantumNLS.BetheVandermonde
import QuantumNLS.BetheZeroLimitLiteral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
Source periodic_basis.tex:289–299: coefficient convergence, uniform convergence
on the closed chamber/cube and norm convergence of the symmetric extension.
All Bethe and physical imports are frozen. No completeness is assumed.
-/
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.BetheWavefunctions QuantumNLS.BetheExtension
  QuantumNLS.BetheWeakGradient QuantumNLS.BetheH1

namespace QuantumNLS.BetheWaveContinuity

/-- The compact physical cube, including all collision walls and seams. -/
abbrev Cube (L : ℝ) (N : ℕ) := Icc (fun _ : Fin N => (0 : ℝ)) (fun _ => L)

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- Sorted representatives land in the closed physical cube. -/
def cubeRep (x : Fin N → AddCircle L) : Cube L N :=
  ⟨decreasing (representatives L x), by
    constructor <;> intro i
    · change (0 : ℝ) ≤ (representatives L x) ((Tuple.sort (α := ℝᵒᵈ) (representatives L x)) i)
      exact (AddCircle.equivIco L 0 (x ((Tuple.sort (α := ℝᵒᵈ) (representatives L x)) i))).property.1
    · change (representatives L x) ((Tuple.sort (α := ℝᵒᵈ) (representatives L x)) i) ≤ L
      have h := (AddCircle.equivIco L 0 (x ((Tuple.sort (α := ℝᵒᵈ) (representatives L x)) i))).property.2
      simpa only [zero_add, representatives] using h.le⟩

theorem measurable_cubeRep : Measurable (cubeRep (L := L) (N := N)) :=
  ((continuous_decreasing N).measurable.comp (measurable_representatives N L)).subtype_mk

/-- Measurable pullback of a continuous cube function has finite L² norm. -/
theorem pull_memLp (f : C(Cube L N, ℂ)) :
    MemLp (fun x : Fin N → AddCircle L => f (cubeRep x)) 2 (torusPiMeasure L N) := by
  apply MemLp.of_bound (f.continuous.measurable.comp measurable_cubeRep).aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm _

/-- Pullback uses ordinary mass-L product measure, with its actual norm bound. -/
def cubeToL2 : C(Cube L N, ℂ) →L[ℂ] L2TN L N :=
  LinearMap.mkContinuous
    { toFun := fun f => (pull_memLp f).toLp _
      map_add' := fun f g => (pull_memLp f).toLp_add (pull_memLp g)
      map_smul' := fun a f => (pull_memLp f).toLp_const_smul a }
    ((measureUnivNNReal (torusPiMeasure L N) ^ ((2 : ℝ≥0∞).toReal)⁻¹ : ℝ≥0) : ℝ)
    (fun f => Lp.norm_le_of_ae_bound (norm_nonneg f) (by
      filter_upwards [(pull_memLp f).coeFn_toLp] with x hx
      change ‖((pull_memLp f).toLp _ : L2TN L N) x‖ ≤ ‖f‖
      rw [hx]
      exact f.norm_coe_le_norm _))

/-- Arbitrary finite scattering coefficients and real frequencies on the cube. -/
def cubeSum (A : Equiv.Perm (Fin N) → ℂ) (q : Fin N → ℝ) : C(Cube L N, ℂ) :=
  ⟨fun x => ∑ σ, A σ * planeWave (q ∘ σ) x.val, by
    simp only [planeWave, Function.comp_apply]
    apply continuous_finsetSum
    intro σ _
    apply continuous_const.mul
    apply Complex.continuous_exp.comp
    apply continuous_const.mul
    apply Complex.continuous_ofReal.comp
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)⟩

omit [Fact (0 < L)] in
theorem continuous_cubeSum :
    Continuous (fun p : (Equiv.Perm (Fin N) → ℂ) × (Fin N → ℝ) =>
      cubeSum (L := L) p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ((Equiv.Perm (Fin N) → ℂ) × (Fin N → ℝ)) × Cube L N =>
    ∑ σ, p.1.1 σ * planeWave (p.1.2 ∘ σ) p.2.val)
  simp only [planeWave, Function.comp_apply]
  apply continuous_finsetSum
  intro σ _
  apply Continuous.mul (by fun_prop)
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Complex.continuous_ofReal.comp
  apply continuous_finsetSum
  intro j _
  exact (by fun_prop : Continuous (fun p : ((Equiv.Perm (Fin N) → ℂ) × (Fin N → ℝ)) × Cube L N => p.1.2 (σ j))).mul
    ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))

/-- A total parameterized L² vector, independent of any root or eigenvalue hypothesis. -/
def vector (A : Equiv.Perm (Fin N) → ℂ) (q : Fin N → ℝ) : L2TN L N :=
  cubeToL2 (cubeSum A q)

theorem continuous_vector :
    Continuous (fun p : (Equiv.Perm (Fin N) → ℂ) × (Fin N → ℝ) =>
      vector (L := L) p.1 p.2) :=
  cubeToL2.continuous.comp continuous_cubeSum

theorem coe_vector (A : Equiv.Perm (Fin N) → ℂ) (q : Fin N → ℝ) :
    (vector (L := L) A q : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      (fun x => ∑ σ, A σ * planeWave (q ∘ σ) (decreasing (representatives L x))) :=
  (pull_memLp (cubeSum A q)).coeFn_toLp

/-- This construction gives the identical positive-coupling physical vector. -/
theorem vector_eq_wave {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    vector (L := L) (fun σ => coefficient c (BetheSmooth.sourceRoots L n c ∘ σ))
      (BetheSmooth.sourceRoots L n c) = (waveH1 (L := L) hc hn).val := by
  apply Lp.ext
  exact (coe_vector _ _).trans (coe_waveH1_val hc hn).symm

/-- Printed second root limit, including coincident limiting free momenta,
makes each ratio c/(q_i-q_j) tend to zero. -/
theorem ratio_zero {n : Fin N → ℤ} (hn : Antitone n) {i j : Fin N} (hij : i ≠ j) :
    Tendsto (fun c => c / (BetheSmooth.sourceRoots L n c i - BetheSmooth.sourceRoots L n c j))
      (𝓝[>] 0) (𝓝 0) := by
  have hL : 0 < L := Fact.out
  rcases lt_or_gt_of_ne hij with h | h
  · have he := ((BetheZeroLimitLiteral.zero_limit_literal hL hn).2 i j h).inv_tendsto_atTop
    change Tendsto (fun c => ((BetheSmooth.sourceRoots L n c i - BetheSmooth.sourceRoots L n c j) / c)⁻¹) _ _ at he
    simpa only [inv_div] using he
  · have he := ((BetheZeroLimitLiteral.zero_limit_literal hL hn).2 j i h).inv_tendsto_atTop.neg
    change Tendsto (fun c => -((BetheSmooth.sourceRoots L n c j - BetheSmooth.sourceRoots L n c i) / c)⁻¹) _ _ at he
    simpa only [inv_div, neg_zero, ← div_neg, neg_sub] using he

theorem factor_tendsto_one {n : Fin N → ℤ} (hn : Antitone n)
    (σ : Equiv.Perm (Fin N)) {i j : Fin N} (hij : i ≠ j) :
    Tendsto (fun c => factor c (BetheSmooth.sourceRoots L n c (σ i))
      (BetheSmooth.sourceRoots L n c (σ j))) (𝓝[>] 0) (𝓝 1) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp (ratio_zero (L := L) hn (σ.injective.ne hij))
  have hh := (tendsto_const_nhds (x := (1 : ℂ)) (f := 𝓝[>] (0 : ℝ))).sub
    ((tendsto_const_nhds (x := Complex.I) (f := 𝓝[>] (0 : ℝ))).mul h)
  simpa only [Function.comp_apply, Complex.ofReal_zero, mul_zero, sub_zero,
    factor, Complex.ofReal_div, mul_div_assoc] using hh

theorem coefficient_tendsto_one {n : Fin N → ℤ} (hn : Antitone n)
    (σ : Equiv.Perm (Fin N)) :
    Tendsto (fun c => coefficient c (BetheSmooth.sourceRoots L n c ∘ σ)) (𝓝[>] 0) (𝓝 1) := by
  have ht : Tendsto (fun c => coefficient c (BetheSmooth.sourceRoots L n c ∘ σ))
      (𝓝[>] 0) (𝓝 (∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j), (1 : ℂ))) := by
    exact tendsto_finsetProd Finset.univ (fun i _ =>
      tendsto_finsetProd (Finset.univ.filter (fun j => i < j)) (fun j hj =>
        factor_tendsto_one (L := L) hn σ (ne_of_lt (Finset.mem_filter.1 hj).2)))
  simpa using ht

/-- Exactly the source free rapidities, with repeated integer labels allowed. -/
def freeRoots (L : ℝ) (n : Fin N → ℤ) : Fin N → ℝ := fun i => 2 * Real.pi / L * (n i : ℝ)

/-- The literal free finite sum; no normalization or completeness premise. -/
def freeVector (L : ℝ) [Fact (0 < L)] (n : Fin N → ℤ) : L2TN L N :=
  vector (fun _ => 1) (freeRoots L n)

/-- The source coefficient/rapidity limits give norm convergence of the same
unnormalized physical vectors as c decreases to zero. -/
theorem vector_zero_limit {n : Fin N → ℤ} (hn : Antitone n) :
    Tendsto (fun c => vector (L := L)
      (fun σ => coefficient c (BetheSmooth.sourceRoots L n c ∘ σ))
      (BetheSmooth.sourceRoots L n c)) (𝓝[>] 0) (𝓝 (freeVector L n)) := by
  have hA : Tendsto (fun c => fun σ : Equiv.Perm (Fin N) => coefficient c (BetheSmooth.sourceRoots L n c ∘ σ))
      (𝓝[>] 0) (𝓝 (fun _ => (1 : ℂ))) := tendsto_pi_nhds.2 (fun σ => coefficient_tendsto_one (L := L) hn σ)
  have hq : Tendsto (BetheSmooth.sourceRoots L n) (𝓝[>] 0) (𝓝 (freeRoots L n)) :=
    BetheZeroLimitLiteral.first_limit_literal (Fact.out : 0 < L) hn
  have hp : Tendsto (fun c : ℝ =>
      ((fun σ : Equiv.Perm (Fin N) => coefficient c (BetheSmooth.sourceRoots L n c ∘ σ)),
        BetheSmooth.sourceRoots L n c)) (𝓝[>] 0)
      (𝓝 (((fun _ => 1) : Equiv.Perm (Fin N) → ℂ), freeRoots L n))  := hA.prodMk_nhds hq
  have ht := ((continuous_vector (L := L) (N := N)).tendsto
    ((fun _ => 1), freeRoots L n)).comp hp
  simpa only [Function.comp_def, freeVector] using ht

/-- The same finite sums converge uniformly on the full closed cube,
which is stronger than the printed closed-chamber convergence. -/
theorem cube_zero_limit {n : Fin N → ℤ} (hn : Antitone n) :
    Tendsto (fun c => cubeSum (L := L)
      (fun σ => coefficient c (BetheSmooth.sourceRoots L n c ∘ σ))
      (BetheSmooth.sourceRoots L n c)) (𝓝[>] 0)
      (𝓝 (cubeSum (L := L) (fun _ => 1) (freeRoots L n))) := by
  have hA : Tendsto (fun c => fun σ : Equiv.Perm (Fin N) => coefficient c (BetheSmooth.sourceRoots L n c ∘ σ))
      (𝓝[>] 0) (𝓝 (fun _ => (1 : ℂ))) := tendsto_pi_nhds.2 (fun σ => coefficient_tendsto_one (L := L) hn σ)
  have hq : Tendsto (BetheSmooth.sourceRoots L n) (𝓝[>] 0) (𝓝 (freeRoots L n)) :=
    BetheZeroLimitLiteral.first_limit_literal (Fact.out : 0 < L) hn
  have hp : Tendsto (fun c : ℝ =>
      ((fun σ : Equiv.Perm (Fin N) => coefficient c (BetheSmooth.sourceRoots L n c ∘ σ)),
        BetheSmooth.sourceRoots L n c)) (𝓝[>] 0)
      (𝓝 (((fun _ => 1) : Equiv.Perm (Fin N) → ℂ), freeRoots L n))  := hA.prodMk_nhds hq
  have ht := ((continuous_cubeSum (L := L) (N := N)).tendsto
    ((fun _ => 1), freeRoots L n)).comp hp
  simpa only [Function.comp_def] using ht

/-- Positive-coupling root smoothness and the absence of coefficient poles
imply continuity of each literal scattering coefficient. -/
theorem coefficient_continuousAt {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ}
    (hn : Antitone n) (σ : Equiv.Perm (Fin N)) :
    ContinuousAt (fun d => coefficient d (BetheSmooth.sourceRoots L n d ∘ σ)) c := by
  have hL : 0 < L := Fact.out
  have hq : ContinuousAt (BetheSmooth.sourceRoots L n) c :=
    (BetheSmooth.root_contDiffAt hL hc _).continuousAt
  have hqi (i : Fin N) : ContinuousAt (fun d => ((BetheSmooth.sourceRoots L n d i : ℝ) : ℂ)) c :=
    Complex.continuous_ofReal.continuousAt.comp ((continuous_apply i).continuousAt.comp hq)
  unfold coefficient
  apply tendsto_finsetProd
  intro i _
  apply tendsto_finsetProd
  intro j hj
  have hne := sourceRoots_difference_ne_zero hL hc hn σ (ne_of_lt (Finset.mem_filter.1 hj).2)
  have hden : ContinuousAt (fun d => ((BetheSmooth.sourceRoots L n d (σ i) -
      BetheSmooth.sourceRoots L n d (σ j) : ℝ) : ℂ)) c := by
    convert (hqi (σ i)).sub (hqi (σ j)) using 1
    ext d
    simp
  exact continuousAt_const.sub ((continuousAt_const.mul Complex.continuous_ofReal.continuousAt).div
    hden (Complex.ofReal_ne_zero.mpr hne))

/-- Norm continuity on the entire positive coupling interval, for the
literal unnormalized H¹ vectors viewed in the physical L² space. -/
theorem continuous_positive_wave {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    Continuous (fun c : Ioi (0 : ℝ) => (waveH1 (L := L) c.property hn).val) := by
  have hparam : Continuous (fun c : Ioi (0 : ℝ) =>
      ((fun σ : Equiv.Perm (Fin (N+1)) => coefficient c.val (BetheSmooth.sourceRoots L n c.val ∘ σ)),
        BetheSmooth.sourceRoots L n c.val)) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro σ
      apply continuous_iff_continuousAt.2
      intro c
      exact (coefficient_continuousAt c.property hn σ).comp continuous_subtype_val.continuousAt
    · exact ((BetheSmooth.source_roots_spec (Fact.out : 0 < L) hn).1.continuousOn).domRestrict
  have h := (continuous_vector (L := L) (N := N+1)).comp hparam
  exact h.congr (fun c => vector_eq_wave c.property hn)

/-- Relabeling the positions inversely relabels the frequency tuple. -/
theorem planeWave_permute (q x : Fin N → ℝ) (τ : Equiv.Perm (Fin N)) :
    planeWave q (x ∘ τ) = planeWave (q ∘ τ.symm) x := by
  have hs : (∑ j, q j * x (τ j)) = ∑ j, q (τ.symm j) * x j := by
    simpa only [Equiv.apply_symm_apply] using
      (Equiv.sum_comp τ.symm (fun j => q j * x (τ j))).symm
  exact congrArg (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) hs

/-- Repeated free momenta are retained with their actual multiplicities. -/
theorem freeSum_permute (q x : Fin N → ℝ) (τ : Equiv.Perm (Fin N)) :
    (∑ σ : Equiv.Perm (Fin N), planeWave (q ∘ σ) (x ∘ τ)) =
      ∑ σ : Equiv.Perm (Fin N), planeWave (q ∘ σ) x := by
  calc
    _ = ∑ σ : Equiv.Perm (Fin N), planeWave (q ∘ (σ * τ.symm)) x := by
      apply Finset.sum_congr rfl
      intro σ _
      exact planeWave_permute (q ∘ σ) x τ
    _ = _ := Equiv.sum_comp (Equiv.mulRight τ.symm) (fun σ => planeWave (q ∘ σ) x)

/-- The endpoint is literally the unsorted source free plane-wave sum on
the physical torus, with no factorial or volume normalization inserted. -/
theorem coe_freeVector (n : Fin N → ℤ) :
    (freeVector L n : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      (fun x => ∑ σ : Equiv.Perm (Fin N),
        Complex.exp (Complex.I * ((∑ j, (2 * Real.pi / L * (n (σ j) : ℝ)) *
          representatives L x j : ℝ) : ℂ))) := by
  filter_upwards [coe_vector (L := L) (fun _ => 1) (freeRoots L n)] with x hx
  change (vector (L := L) (fun _ => 1) (freeRoots L n) : (Fin N → AddCircle L) → ℂ) x = _
  rw [hx]
  simp only [one_mul]
  have he := freeSum_permute (freeRoots L n) (representatives L x)
    (Tuple.sort (α := ℝᵒᵈ) (representatives L x))
  exact he

/-- A single explicit extension of the actual positive-coupling vectors. -/
def continuedWave (n : Fin (N+1) → ℤ) (hn : Antitone n) (c : ℝ) : L2TN L (N+1) :=
  if hc : 0 < c then (waveH1 (L := L) hc hn).val else freeVector L n

theorem continuedWave_pos {n : Fin (N+1) → ℤ} (hn : Antitone n) {c : ℝ} (hc : 0 < c) :
    continuedWave (L := L) n hn c = (waveH1 (L := L) hc hn).val := by simp [continuedWave, hc]

theorem continuedWave_zero {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    continuedWave (L := L) n hn 0 = freeVector L n := by simp [continuedWave]

/-- Norm convergence of the actual H¹ representatives in the physical L²
carrier, rather than convergence of a new vector supplied by a hypothesis. -/
theorem continuedWave_zero_limit {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    Tendsto (continuedWave (L := L) n hn) (𝓝[>] 0) (𝓝 (freeVector L n)) := by
  apply (vector_zero_limit (L := L) hn).congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (vector_eq_wave hc hn).trans (continuedWave_pos hn hc).symm

/-- Positive-coupling norm continuity and the free endpoint limit are
obtained from the source's smooth-root/coefficient and zero-root arguments. -/
theorem norm_continuous_extension {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    Continuous (fun c : Ioi (0 : ℝ) => continuedWave (L := L) n hn c) ∧
    continuedWave (L := L) n hn 0 = freeVector L n ∧
    Tendsto (continuedWave (L := L) n hn) (𝓝[>] 0) (𝓝 (freeVector L n)) := by
  refine ⟨?_, continuedWave_zero hn, continuedWave_zero_limit hn⟩
  exact (continuous_positive_wave (L := L) hn).congr
    (fun c => (continuedWave_pos hn c.property).symm)

/-- Literal uniform convergence on the closed cube, hence on the closed
ordered chamber used in the printed proof. -/
theorem uniform_zero_limit {n : Fin N → ℤ} (hn : Antitone n) :
    TendstoUniformly
      (fun c (x : Cube L N) => wavefunction L c n x.val)
      (fun x : Cube L N => ∑ σ : Equiv.Perm (Fin N), planeWave (freeRoots L n ∘ σ) x.val)
      (𝓝[>] 0) := by
  have ht := ContinuousMap.tendsto_iff_tendstoUniformly.1 (cube_zero_limit (L := L) hn)
  simpa only [cubeSum, ContinuousMap.coe_mk, wavefunction, coordinateAnsatz, one_mul] using ht

end QuantumNLS.BetheWaveContinuity

#print axioms QuantumNLS.BetheWaveContinuity.Cube
#print axioms QuantumNLS.BetheWaveContinuity.cubeRep
#print axioms QuantumNLS.BetheWaveContinuity.measurable_cubeRep
#print axioms QuantumNLS.BetheWaveContinuity.pull_memLp
#print axioms QuantumNLS.BetheWaveContinuity.cubeToL2
#print axioms QuantumNLS.BetheWaveContinuity.cubeSum
#print axioms QuantumNLS.BetheWaveContinuity.continuous_cubeSum
#print axioms QuantumNLS.BetheWaveContinuity.vector
#print axioms QuantumNLS.BetheWaveContinuity.continuous_vector
#print axioms QuantumNLS.BetheWaveContinuity.coe_vector
#print axioms QuantumNLS.BetheWaveContinuity.vector_eq_wave
#print axioms QuantumNLS.BetheWaveContinuity.ratio_zero
#print axioms QuantumNLS.BetheWaveContinuity.factor_tendsto_one
#print axioms QuantumNLS.BetheWaveContinuity.coefficient_tendsto_one
#print axioms QuantumNLS.BetheWaveContinuity.freeRoots
#print axioms QuantumNLS.BetheWaveContinuity.freeVector
#print axioms QuantumNLS.BetheWaveContinuity.vector_zero_limit
#print axioms QuantumNLS.BetheWaveContinuity.cube_zero_limit
#print axioms QuantumNLS.BetheWaveContinuity.coefficient_continuousAt
#print axioms QuantumNLS.BetheWaveContinuity.continuous_positive_wave
#print axioms QuantumNLS.BetheWaveContinuity.planeWave_permute
#print axioms QuantumNLS.BetheWaveContinuity.freeSum_permute
#print axioms QuantumNLS.BetheWaveContinuity.coe_freeVector
#print axioms QuantumNLS.BetheWaveContinuity.continuedWave
#print axioms QuantumNLS.BetheWaveContinuity.continuedWave_pos
#print axioms QuantumNLS.BetheWaveContinuity.continuedWave_zero
#print axioms QuantumNLS.BetheWaveContinuity.continuedWave_zero_limit
#print axioms QuantumNLS.BetheWaveContinuity.norm_continuous_extension
#print axioms QuantumNLS.BetheWaveContinuity.uniform_zero_limit

/- Dependency audit of the printed continuity route. -/
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let forbidden : Array Lean.Name := #[
    ``QuantumNLS.BetheEigenGlobal.planeCharacter,
    ``QuantumNLS.BetheEigenGlobal.planeCharacters_independent,
    ``QuantumNLS.BetheEigenGlobal.analyticAt_coordinateAnsatz,
    ``QuantumNLS.BetheEigenGlobal.coordinateAnsatz_chamber_nonzero,
    ``QuantumNLS.BetheEigenGlobal.wave_ne_zero,
    ``QuantumNLS.BetheEigenGlobal.chamber_ansatz_independent,
    ``QuantumNLS.BetheEigenGlobal.waves_independent,
    ``linearIndependent_monoidHom]
  let mut pending := #[``QuantumNLS.BetheWaveContinuity.norm_continuous_extension,
    ``QuantumNLS.BetheWaveContinuity.uniform_zero_limit,
    ``QuantumNLS.BetheWaveContinuity.coe_freeVector]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if forbidden.contains n then
        throwError "Continuity route reached an unrelated independence proof: {n}"
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheZeroLimitLiteral.first_limit_literal,
      ``QuantumNLS.BetheZeroLimitLiteral.zero_limit_literal,
      ``QuantumNLS.BetheWaveContinuity.coefficient_tendsto_one,
      ``QuantumNLS.BetheWaveContinuity.coefficient_continuousAt,
      ``QuantumNLS.BetheWaveContinuity.cubeToL2,
      ``QuantumNLS.BetheWaveContinuity.vector_eq_wave,
      ``QuantumNLS.BetheWaveContinuity.freeSum_permute] do
    unless seen.contains n do
      throwError "Continuity route missed required source step: {n}"
  Lean.logInfo m!"Continuity route PASS: {seen.size} transitive constants; printed root limits, coefficient convergence, positive smoothness, physical cube-to-L2 bound, actual-vector equality and unsorted free formula reached; eight unrelated independence declarations excluded."
