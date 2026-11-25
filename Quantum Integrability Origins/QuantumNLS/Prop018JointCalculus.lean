import QuantumNLS.HighAngleLinearEvolution
import QuantumNLS.Prop020Contour
import QuantumNLS.FunctionalLinearizationParamMeas

/-! Common continuous functional calculus for the transfer and its first
spectral derivative, constructed in the proved complete physical basis. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology MeasureTheory Complex
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop018JointCalculus
open HaarNonlinearAbstract HaarSpectralTail HaarNonlinearTail FunctionalLinearization

section Calculus
variable {ι H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace X] [CompactSpace X]

/-- Spectral integration of a continuous function against the common
complete atomic resolution. -/
def spectralEval (b : HilbertBasis ι ℂ H) (x : ι → X) (g : C(X, ℂ)) : H →L[ℂ] H :=
  Classical.choose (HilbertDiagOp.diag_exists b (fun i => g (x i)) ‖g‖
    (fun i => g.norm_coe_le_norm (x i)) (norm_nonneg _))

lemma hom_norm_le (Φ : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (g : C(X, ℂ)) : ‖Φ g‖ ≤ ‖g‖ :=
  NonUnitalStarAlgHom.norm_apply_le Φ g

lemma hom_continuous (Φ : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) : Continuous Φ :=
  AddMonoidHomClass.continuous_of_bound Φ 1 (fun g => by simpa only [one_mul] using hom_norm_le Φ g)

lemma spectralEval_diag (b : HilbertBasis ι ℂ H) (x : ι → X) (g : C(X, ℂ)) :
    IsDiagC b (spectralEval b x g) (fun i => g (x i)) :=
  (Classical.choose_spec (HilbertDiagOp.diag_exists b (fun i => g (x i)) ‖g‖
    (fun i => g.norm_coe_le_norm (x i)) (norm_nonneg _))).1

lemma spectralEval_eigen (b : HilbertBasis ι ℂ H) (x : ι → X) (g : C(X, ℂ)) (i : ι) :
    spectralEval b x g (b i) = g (x i) • b i := (spectralEval_diag b x g).apply_basis i

/-- A unital star-algebra homomorphism, rather than a mere assignment of
eigenvalues: this is the common continuous functional calculus. -/
def spectralHom (b : HilbertBasis ι ℂ H) (x : ι → X) : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := spectralEval b x
  map_one' := by
    apply TransferNormality.ext_of_hilbertBasis b
    intro i
    rw [spectralEval_eigen]
    simp
  map_mul' := by
    intro f g
    apply TransferNormality.ext_of_hilbertBasis b
    intro i
    simp only [mul_apply_eq_comp, spectralEval_eigen, map_smul,
      smul_smul, ContinuousMap.mul_apply]
    rw [mul_comm]
  map_zero' := by
    apply TransferNormality.ext_of_hilbertBasis b
    intro i
    rw [spectralEval_eigen]
    simp
  map_add' := by
    intro f g
    apply TransferNormality.ext_of_hilbertBasis b
    intro i
    simp only [spectralEval_eigen, add_apply, ContinuousMap.add_apply, add_smul]
  commutes' := by
    intro c
    apply TransferNormality.ext_of_hilbertBasis b
    intro i
    rw [spectralEval_eigen]
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' := by
    intro f
    apply TransferNormality.ext_of_hilbertBasis b
    intro i
    rw [ContinuousLinearMap.star_eq_adjoint, TransferNormality.adjoint_diag b _ _
      (spectralEval_eigen b x f), spectralEval_eigen]
    rfl

lemma spectralHom_eigen (b : HilbertBasis ι ℂ H) (x : ι → X) (g : C(X, ℂ)) (i : ι) :
    spectralHom b x g (b i) = g (x i) • b i := spectralEval_eigen b x g i

lemma spectralHom_commute (b : HilbertBasis ι ℂ H) (x y : ι → X) (f g : C(X, ℂ)) :
    Commute (spectralHom b x f) (spectralHom b y g) :=
  IsDiagC.commute (spectralEval_diag b x f) (spectralEval_diag b y g)

end Calculus

section Pair
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Set (ℂ × ℂ)} [CompactSpace K]

def fstC : C(K, ℂ) := ⟨fun x => x.val.1, continuous_fst.comp continuous_subtype_val⟩
def sndC : C(K, ℂ) := ⟨fun x => x.val.2, continuous_snd.comp continuous_subtype_val⟩

lemma pair_separates : (StarAlgebra.adjoin ℂ ({fstC, sndC} : Set C(K, ℂ))).SeparatesPoints := by
  intro x y hxy
  by_cases h : x.val.1 = y.val.1
  · have h2 : x.val.2 ≠ y.val.2 := fun h2 => hxy (Subtype.ext (Prod.ext h h2))
    exact ⟨_, ⟨sndC, StarAlgebra.subset_adjoin ℂ _ (by simp), rfl⟩, h2⟩
  · exact ⟨_, ⟨fstC, StarAlgebra.subset_adjoin ℂ _ (by simp), rfl⟩, h⟩

/-- The joint calculus agrees with the usual normal-operator CFC for every
function of either constituent. -/
lemma spectralHom_fst_cfc (b : HilbertBasis ι ℂ H) (x : ι → K)
    (S : H →L[ℂ] H) (hS : IsStarNormal S)
    (hdiag : ∀ i, S (b i) = (x i).val.1 • b i) (f : ℂ → ℂ) (hf : Continuous f) :
    spectralHom b x ⟨fun y => f y.val.1, hf.comp fstC.continuous⟩ = cfc f S := by
  apply TransferNormality.ext_of_hilbertBasis b
  intro i
  rw [spectralHom_eigen, Prop020Diag.cfc_eigen hS (hdiag i) (b.orthonormal.ne_zero i) f hf.continuousOn]
  rfl

lemma spectralHom_snd_cfc (b : HilbertBasis ι ℂ H) (x : ι → K)
    (S : H →L[ℂ] H) (hS : IsStarNormal S)
    (hdiag : ∀ i, S (b i) = (x i).val.2 • b i) (f : ℂ → ℂ) (hf : Continuous f) :
    spectralHom b x ⟨fun y => f y.val.2, hf.comp sndC.continuous⟩ = cfc f S := by
  apply TransferNormality.ext_of_hilbertBasis b
  intro i
  rw [spectralHom_eigen, Prop020Diag.cfc_eigen hS (hdiag i) (b.orthonormal.ne_zero i) f hf.continuousOn]
  rfl

/-- Coordinate measurability suffices for operator-valued Bochner
measurability of the common pair calculus, by Stone-Weierstrass. -/
lemma pair_aesm {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (b : HilbertBasis ι ℂ H) (x : Θ → ι → K)
    (h1 : AEStronglyMeasurable (fun θ => spectralHom b (x θ) fstC) ν)
    (h2 : AEStronglyMeasurable (fun θ => spectralHom b (x θ) sndC) ν) (g : C(K, ℂ)) :
    AEStronglyMeasurable (fun θ => spectralHom b (x θ) g) ν := by
  let A := StarAlgebra.adjoin ℂ ({fstC, sndC} : Set C(K, ℂ))
  have hpoly : ∀ a ∈ A, AEStronglyMeasurable (fun θ => spectralHom b (x θ) a) ν := by
    intro a ha
    induction ha using StarAlgebra.adjoin_induction with
    | mem a ha => rcases ha with rfl | rfl <;> assumption
    | algebraMap c =>
      have he : (fun θ => spectralHom b (x θ) (algebraMap ℂ C(K, ℂ) c)) =
          fun _ => algebraMap ℂ (H →L[ℂ] H) c := funext fun θ => AlgHomClass.commutes (spectralHom b (x θ)) c
      rw [he]
      exact aestronglyMeasurable_const
    | add a c ha hc ia ic =>
      have he : (fun θ => spectralHom b (x θ) (a + c)) =
          (fun θ => spectralHom b (x θ) a) + (fun θ => spectralHom b (x θ) c) :=
        funext fun θ => map_add (spectralHom b (x θ)) a c
      rw [he]
      exact ia.add ic
    | mul a c ha hc ia ic =>
      have he : (fun θ => spectralHom b (x θ) (a * c)) =
          (fun θ => spectralHom b (x θ) a) * (fun θ => spectralHom b (x θ) c) :=
        funext fun θ => map_mul (spectralHom b (x θ)) a c
      rw [he]
      exact ia.mul ic
    | star a ha ia =>
      have he : (fun θ => spectralHom b (x θ) (star a)) =
          fun θ => star (spectralHom b (x θ) a) := funext fun θ => map_star (spectralHom b (x θ)) a
      rw [he]
      exact continuous_star.comp_aestronglyMeasurable ia
  have hg : g ∈ closure (A : Set C(K, ℂ)) := by
    have ht := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A pair_separates
    have hmem : g ∈ A.topologicalClosure := by
      rw [ht]
      trivial
    rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hmem
    exact hmem
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp hg
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hpoly (a n) (ha n))
    (ae_of_all _ fun θ => ((hom_continuous (spectralHom b (x θ))).tendsto g).comp hlim)

section Families
variable {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
variable (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
lemma pair_aesm_simple
    (hall : ∀ g : C(K, ℂ), AEStronglyMeasurable (fun θ => Φ θ g) ν)
    (s : SimpleFunc Θ C(K, ℂ)) : AEStronglyMeasurable (fun θ => Φ θ (s θ)) ν := by
  refine SimpleFunc.induction (motive := fun s => AEStronglyMeasurable (fun θ => Φ θ (s θ)) ν)
    (fun c {t} ht => ?_) (fun f g _ hf hg => ?_) s
  · have : (fun θ => Φ θ ((SimpleFunc.piecewise t ht (SimpleFunc.const Θ c)
        (SimpleFunc.const Θ 0)) θ)) = t.indicator (fun θ => Φ θ c) := by
      funext θ
      by_cases h : θ ∈ t
      · simp [SimpleFunc.piecewise_apply, h]
      · simp [SimpleFunc.piecewise_apply, h]
    rw [this]; exact (hall c).indicator ht
  · have : (fun θ => Φ θ ((f + g) θ)) = fun θ => Φ θ (f θ) + Φ θ (g θ) :=
      funext fun θ => by simp [map_add]
    rw [this]; exact hf.add hg

/-- **`θ ↦ Φ θ (g θ)` is strongly measurable when `θ ↦ g θ ∈ C(K,ℂ)` is** (and the coordinates
are). -/
lemma pair_aesm_comp
    (hall : ∀ g : C(K, ℂ), AEStronglyMeasurable (fun θ => Φ θ g) ν)
    (g : Θ → C(K, ℂ)) (hg : AEStronglyMeasurable g ν) :
    AEStronglyMeasurable (fun θ => Φ θ (g θ)) ν := by
  obtain ⟨g', hg', hae⟩ := hg
  have h1 : AEStronglyMeasurable (fun θ => Φ θ (g' θ)) ν := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => pair_aesm_simple ν Φ hall (hg'.approx n))
      (ae_of_all _ fun θ => ?_)
    exact ((hom_continuous (Φ θ)).tendsto (g' θ)).comp (hg'.tendsto_approx θ)
  exact h1.congr (hae.mono fun θ h => by show Φ θ (g' θ) = Φ θ (g θ); rw [h])


end Families

/-- Continuous compact families of functions yield an operator-valued
Bochner integral; no integrability assumption is supplied. -/
lemma pair_integrable {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
    (b : HilbertBasis ι ℂ H) (x : Θ → ι → K)
    (h1 : AEStronglyMeasurable (fun θ => spectralHom b (x θ) fstC) ν)
    (h2 : AEStronglyMeasurable (fun θ => spectralHom b (x θ) sndC) ν)
    (G : C(Θ × K, ℂ)) : Integrable (fun θ => spectralHom b (x θ) (G.curry θ)) ν := by
  borelize C(K, ℂ)
  have hg : AEStronglyMeasurable (fun θ => G.curry θ) ν := G.curry.continuous.aestronglyMeasurable
  have hall := pair_aesm ν b x h1 h2
  have hm := pair_aesm_comp ν (fun θ => spectralHom b (x θ)) hall _ hg
  refine (integrable_const ‖G‖).mono' hm (ae_of_all _ fun θ => ?_)
  refine (hom_norm_le (spectralHom b (x θ)) _).trans ?_
  exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun y => G.norm_coe_le_norm (θ, y))

/-- The real part of the Bochner integral has its actual integrated
spectral eigenvalues. -/
lemma integrated_eigen {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (b : HilbertBasis ι ℂ H) (x : Θ → ι → K) (g : Θ → C(K, ℂ))
    (hi : Integrable (fun θ => spectralHom b (x θ) (g θ)) ν) (i : ι) :
    MixedQuadratures.reOp (∫ θ, spectralHom b (x θ) (g θ) ∂ν) (b i) =
      (((∫ θ, g θ (x θ i) ∂ν).re : ℝ) : ℂ) • b i := by
  let A := ∫ θ, spectralHom b (x θ) (g θ) ∂ν
  have hA (j : ι) : A (b j) = (∫ θ, g θ (x θ j) ∂ν) • b j := by
    rw [ContinuousLinearMap.integral_apply hi]
    simp_rw [spectralHom_eigen]
    exact integral_smul_const _ _
  have hn : IsStarNormal A := ⟨IsDiagC.commute (diagC_of_apply hA).adjoint (diagC_of_apply hA)⟩
  have he := Prop020Diag.reOp_smul_eigen hn (hA i) 1
  simpa only [one_smul, one_mul] using he

end Pair
end QuantumNLS.Prop018JointCalculus

#print axioms QuantumNLS.Prop018JointCalculus.spectralEval
#print axioms QuantumNLS.Prop018JointCalculus.hom_norm_le
#print axioms QuantumNLS.Prop018JointCalculus.hom_continuous
#print axioms QuantumNLS.Prop018JointCalculus.spectralEval_diag
#print axioms QuantumNLS.Prop018JointCalculus.spectralEval_eigen
#print axioms QuantumNLS.Prop018JointCalculus.spectralHom
#print axioms QuantumNLS.Prop018JointCalculus.spectralHom_eigen
#print axioms QuantumNLS.Prop018JointCalculus.spectralHom_commute
#print axioms QuantumNLS.Prop018JointCalculus.fstC
#print axioms QuantumNLS.Prop018JointCalculus.sndC
#print axioms QuantumNLS.Prop018JointCalculus.pair_separates
#print axioms QuantumNLS.Prop018JointCalculus.spectralHom_fst_cfc
#print axioms QuantumNLS.Prop018JointCalculus.spectralHom_snd_cfc
#print axioms QuantumNLS.Prop018JointCalculus.pair_aesm
#print axioms QuantumNLS.Prop018JointCalculus.pair_aesm_simple
#print axioms QuantumNLS.Prop018JointCalculus.pair_aesm_comp
#print axioms QuantumNLS.Prop018JointCalculus.pair_integrable
#print axioms QuantumNLS.Prop018JointCalculus.integrated_eigen

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop018JointCalculus." then
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
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
