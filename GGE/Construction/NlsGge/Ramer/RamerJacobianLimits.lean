import Mathlib
import NlsGge.Ramer.RamerJacobianHead
import NlsGge.Ramer.RamerStep8b

/-!
# R9b: divergence convergences and linearity

See `RamerJacobianLimits.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section Limits

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-! ### Subsequences of in-measure convergent sequences -/

theorem exists_subseq_ae_of_tendstoInMeasure {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ} (h : TendstoInMeasure μ f atTop g) {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂μ, Tendsto (fun j => f (ψ (φ j)) x) atTop (𝓝 (g x)) := by
  have h' : TendstoInMeasure μ (fun n => f (ψ n)) atTop g :=
    fun ε hε => (h ε hε).comp hψ.tendsto_atTop
  exact h'.exists_seq_tendsto_ae

/-! ### Item 1: linearity -/

variable {c s}

theorem ramerA_add (hs0 : 0 ≤ s) (n : ℕ) (M₁ M₂ : FullWeightedHilbert c s → ActualCM c)
    (h₁ : Differentiable ℝ M₁) (h₂ : Differentiable ℝ M₂) :
    ramerA c s hs0 n (M₁ + M₂) = ramerA c s hs0 n M₁ + ramerA c s hs0 n M₂ := by
  funext z
  unfold ramerA
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hf : fderiv ℝ (M₁ + M₂) (NlsGge.Measure.fullWeightedSequenceRealization c s z) =
      fderiv ℝ M₁ (NlsGge.Measure.fullWeightedSequenceRealization c s z) +
      fderiv ℝ M₂ (NlsGge.Measure.fullWeightedSequenceRealization c s z) :=
    fderiv_add (h₁ _) (h₂ _)
  rw [hf, add_apply]
  set b := weightedRealHilbertBasis (cmModeWeight c) p
  set y := NlsGge.Measure.fullWeightedSequenceRealization c s z
  set u := cmToFullWeightedHilbert c s hs0 b
  have e1 : ⟪b, M₁ y + M₂ y⟫ = ⟪b, M₁ y⟫ + ⟪b, M₂ y⟫ := inner_add_right _ _ _
  have e2 : ⟪b, fderiv ℝ M₁ y u + fderiv ℝ M₂ y u⟫ =
      ⟪b, fderiv ℝ M₁ y u⟫ + ⟪b, fderiv ℝ M₂ y u⟫ := inner_add_right _ _ _
  rw [e1, e2]
  ring

variable (c s)

/-- **Item 1.** Linearity of the divergence, a.e. -/
theorem ramerDiv_add_ae (hs : (1 : ℝ) / 2 < s) (M₁ M₂ : FullWeightedHilbert c s → ActualCM c)
    (h₁ : ContDiff ℝ 2 M₁) (h₂ : ContDiff ℝ 2 M₂) :
    ramerDiv c s hs (M₁ + M₂) =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val]
      ramerDiv c s hs M₁ + ramerDiv c s hs M₂ := by
  have h12 : ContDiff ℝ 2 (M₁ + M₂) := h₁.add h₂
  have d₁ : Differentiable ℝ M₁ := h₁.differentiable (by norm_num)
  have d₂ : Differentiable ℝ M₂ := h₂.differentiable (by norm_num)
  have s₁ := (ramerDiv_spec c s hs M₁ h₁).2.2
  have s₂ := (ramerDiv_spec c s hs M₂ h₂).2.2
  have s₁₂ := (ramerDiv_spec c s hs _ h12).2.2
  obtain ⟨ψ, hψ, a₁⟩ := s₁.exists_seq_tendsto_ae
  obtain ⟨φ₂, hφ₂, a₂⟩ := exists_subseq_ae_of_tendstoInMeasure s₂ hψ
  obtain ⟨φ₃, hφ₃, a₃⟩ := exists_subseq_ae_of_tendstoInMeasure s₁₂ (hψ.comp hφ₂)
  filter_upwards [a₁, a₂, a₃] with z z₁ z₂ z₃
  have e₁ : Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (ψ (φ₂ (φ₃ j))) M₁ z) atTop
      (𝓝 (ramerDiv c s hs M₁ z)) :=
    z₁.comp ((hφ₂.comp hφ₃).tendsto_atTop)
  have e₂ : Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (ψ (φ₂ (φ₃ j))) M₂ z) atTop
      (𝓝 (ramerDiv c s hs M₂ z)) :=
    z₂.comp hφ₃.tendsto_atTop
  have e₃ : Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (ψ (φ₂ (φ₃ j))) (M₁ + M₂) z)
      atTop (𝓝 (ramerDiv c s hs (M₁ + M₂) z)) := z₃
  have e₄ := e₁.add e₂
  have : (fun j => ramerA c s (zero_le_of_half_lt hs) (ψ (φ₂ (φ₃ j))) (M₁ + M₂) z) =
      fun j => ramerA c s (zero_le_of_half_lt hs) (ψ (φ₂ (φ₃ j))) M₁ z +
        ramerA c s (zero_le_of_half_lt hs) (ψ (φ₂ (φ₃ j))) M₂ z := by
    funext j
    rw [ramerA_add _ _ _ _ d₁ d₂]; rfl
  rw [this] at e₃
  exact tendsto_nhds_unique e₃ e₄

/-! ### Item 2: range projections -/

variable {c s}

theorem headProj_idem (k : ℕ) (w : ActualCM c) : headProj c k (headProj c k w) = headProj c k w := by
  apply cmCoord_ext
  intro n
  rw [headProj_apply, headProj_apply, cmCoord_cmTrunc, cmCoord_cmTrunc]
  split_ifs <;> rfl

theorem inner_basis_headProj (k : ℕ) (p : ℤ × Fin 2) (hp : p.1 ∈ symmetricModes k) (w : ActualCM c) :
    ⟪weightedRealHilbertBasis (cmModeWeight c) p, headProj c k w⟫ =
      ⟪weightedRealHilbertBasis (cmModeWeight c) p, w⟫ := by
  rw [headProj_apply, inner_basis_cmTrunc]; simp [hp]

/-- The projected field `P_k ∘ M`. -/
abbrev projField (k : ℕ) (M : FullWeightedHilbert c s → ActualCM c) :
    FullWeightedHilbert c s → ActualCM c := fun y => headProj c k (M y)

theorem contDiff_projField (k : ℕ) (M : FullWeightedHilbert c s → ActualCM c) {n : ℕ∞}
    (hM : ContDiff ℝ n M) : ContDiff ℝ n (projField k M) :=
  (headProj c k).contDiff.comp hM

theorem ramerA_projField (hs0 : 0 ≤ s) (k : ℕ) (M : FullWeightedHilbert c s → ActualCM c)
    (hM : Differentiable ℝ M) :
    ramerA c s hs0 k (projField k M) = ramerA c s hs0 k M := by
  funext z
  unfold ramerA
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp1 : p.1 ∈ symmetricModes k := (Finset.mem_product.1 hp).1
  have hf : fderiv ℝ (projField k M) (NlsGge.Measure.fullWeightedSequenceRealization c s z) =
      (headProj c k).comp (fderiv ℝ M (NlsGge.Measure.fullWeightedSequenceRealization c s z)) :=
    ((headProj c k).hasFDerivAt.comp _ (hM _).hasFDerivAt).fderiv
  set y := NlsGge.Measure.fullWeightedSequenceRealization c s z
  set b := weightedRealHilbertBasis (cmModeWeight c) p
  set u := cmToFullWeightedHilbert c s hs0 b
  have e1 : ⟪b, ((headProj c k).comp (fderiv ℝ M y)) u⟫ = ⟪b, fderiv ℝ M y u⟫ :=
    inner_basis_headProj k p hp1 _
  have e2 : ⟪b, projField k M y⟫ = ⟪b, M y⟫ := inner_basis_headProj k p hp1 _
  rw [hf]
  erw [e1, e2]

variable (c s)

/-- **Item 2 (divergence).** -/
theorem ramerDiv_projField_subseq (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (hM : ContDiff ℝ 2 M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
        (∀ j, ramerDiv c s hs (projField (φ j) M) z =
          ramerA c s (zero_le_of_half_lt hs) (φ j) M z) ∧
        Tendsto (fun j => ramerDiv c s hs (projField (φ j) M) z) atTop
          (𝓝 (ramerDiv c s hs M z)) := by
  obtain ⟨φ, hφ, hlim⟩ := (ramerDiv_spec c s hs M hM).2.1
  refine ⟨φ, hφ, ?_⟩
  have hall : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val), ∀ j,
      ramerDiv c s hs (projField (φ j) M) z = ramerA c s (zero_le_of_half_lt hs) (φ j) M z := by
    rw [ae_all_iff]
    intro j
    filter_upwards [ramerDiv_ae_eq_ramerA c s hs (projField (φ j) M)
      (contDiff_projField _ M hM) (fun x => headProj_idem _ _)] with z hz
    rw [hz, ramerA_projField _ _ M (hM.differentiable (by norm_num))]
  filter_upwards [hall, hlim] with z h1 h2
  exact ⟨h1, h2.congr (fun j => (h1 j).symm)⟩

/-- **Item 2 (derivative and values).** -/
theorem tendsto_hsDerivH_projField (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (hM : Differentiable ℝ M) (x : FullWeightedHilbert c s) :
    Tendsto (fun k : ℕ => hsDerivH c s hs (projField k M) x) atTop (𝓝 (hsDerivH c s hs M x)) :=
  tendsto_hsDerivH_headProj c s hs M hM x

theorem tendsto_projField_apply (M : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) :
    Tendsto (fun k : ℕ => projField k M x) atTop (𝓝 (M x)) :=
  headProj_tendsto c (M x)

/-! ### Item 4: generic `J`-convergence -/

theorem tendsto_ramerJac {ι : Type*} {l : Filter ι} (hs : (1 : ℝ) / 2 < s)
    (Mj : ι → FullWeightedHilbert c s → ActualCM c) (M : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s)
    (h1 : Tendsto (fun j => Mj j x) l (𝓝 (M x)))
    (h2 : Tendsto (fun j => hsDerivH c s hs (Mj j) x) l (𝓝 (hsDerivH c s hs M x)))
    (h3 : Tendsto (fun j => ramerDiv c s hs (Mj j) (coordE c s x)) l
      (𝓝 (ramerDiv c s hs M (coordE c s x)))) :
    Tendsto (fun j => ramerJac c s hs (Mj j) x) l (𝓝 (ramerJac c s hs M x)) := by
  simp only [ramerJac_eq]
  have d : Tendsto (fun j => |det2 (hsDerivH c s hs (Mj j) x)|) l
      (𝓝 |det2 (hsDerivH c s hs M x)|) :=
    ((continuous_det2.tendsto _).comp h2).abs
  have e : Tendsto (fun j => Real.exp (-(ramerDiv c s hs (Mj j) (coordE c s x)) -
      ‖Mj j x‖ ^ 2 / 2)) l
      (𝓝 (Real.exp (-(ramerDiv c s hs M (coordE c s x)) - ‖M x‖ ^ 2 / 2))) :=
    (Real.continuous_exp.tendsto _).comp
      (h3.neg.sub ((h1.norm.pow 2).div_const 2))
  exact d.mul e

/-! ### Item 3: fixed finite range, varying argument -/

variable {c s}

/-- The field `R ∘ G ∘ T` with `R = P_m`. -/
abbrev rangeComp (m : ℕ) (G : FullWeightedHilbert c s → ActualCM c)
    (T : FullWeightedHilbert c s → FullWeightedHilbert c s) :
    FullWeightedHilbert c s → ActualCM c := fun y => headProj c m (G (T y))

theorem fderiv_TM (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (hM : Differentiable ℝ M) (y u : FullWeightedHilbert c s) :
    fderiv ℝ (TM c s hs M) y u = u + inclE c s hs (fderiv ℝ M y u) := by
  have h : HasFDerivAt (TM c s hs M) (ContinuousLinearMap.id ℝ _ + (inclE c s hs).comp (fderiv ℝ M y)) y :=
    (hasFDerivAt_id y).add ((inclE c s hs).hasFDerivAt.comp y (hM y).hasFDerivAt)
  rw [h.fderiv]
  rfl

theorem fderiv_rangeComp (hs : (1 : ℝ) / 2 < s) (m : ℕ) (G : FullWeightedHilbert c s → ActualCM c)
    (hG : Differentiable ℝ G) (M : FullWeightedHilbert c s → ActualCM c)
    (hM : Differentiable ℝ M) (y u : FullWeightedHilbert c s) :
    fderiv ℝ (rangeComp m G (TM c s hs M)) y u =
      headProj c m (fderiv ℝ G (TM c s hs M y) (u + inclE c s hs (fderiv ℝ M y u))) := by
  have hT := differentiable_TM c s hs M hM
  have h : HasFDerivAt (rangeComp m G (TM c s hs M))
      ((headProj c m).comp ((fderiv ℝ G (TM c s hs M y)).comp (fderiv ℝ (TM c s hs M) y))) y :=
    (headProj c m).hasFDerivAt.comp y ((hG _).hasFDerivAt.comp y (hT y).hasFDerivAt)
  have e : fderiv ℝ (rangeComp m G (TM c s hs M)) y u =
      headProj c m (fderiv ℝ G (TM c s hs M y) (fderiv ℝ (TM c s hs M) y u)) := by
    erw [h.fderiv]; rfl
  rw [e, fderiv_TM hs M hM]

theorem contDiff_rangeComp (hs : (1 : ℝ) / 2 < s) (m : ℕ) (G : FullWeightedHilbert c s → ActualCM c)
    (M : FullWeightedHilbert c s → ActualCM c) {n : ℕ∞} (hG : ContDiff ℝ n G)
    (hM : ContDiff ℝ n M) : ContDiff ℝ n (rangeComp m G (TM c s hs M)) :=
  (headProj c m).contDiff.comp (hG.comp (contDiff_TM c s hs M hM))

theorem tendsto_ramerSum_rangeComp (hs : (1 : ℝ) / 2 < s) (m : ℕ)
    (G K : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G) (hK : ContDiff ℝ 1 K)
    (x : ActualCM c) (y : FullWeightedHilbert c s) :
    Tendsto (fun k : ℕ => ramerSum c s (zero_le_of_half_lt hs) m
        (rangeComp m G (TM c s hs (projField k K))) x y) atTop
      (𝓝 (ramerSum c s (zero_le_of_half_lt hs) m (rangeComp m G (TM c s hs K)) x y)) := by
  have dG : Differentiable ℝ G := hG.differentiable one_ne_zero
  have dK : Differentiable ℝ K := hK.differentiable one_ne_zero
  have dKk : ∀ k, Differentiable ℝ (projField k K) := fun k =>
    (contDiff_projField k K hK).differentiable one_ne_zero
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hTy : Tendsto (fun k : ℕ => TM c s hs (projField k K) y) atTop (𝓝 (TM c s hs K y)) := by
    unfold TM
    exact tendsto_const_nhds.add ((inclE c s hs).continuous.continuousAt.tendsto.comp
      (tendsto_projField_apply c s K y))
  have hGy : Tendsto (fun k : ℕ => G (TM c s hs (projField k K) y)) atTop
      (𝓝 (G (TM c s hs K y))) := (hG.continuous.tendsto _).comp hTy
  have hDy : Tendsto (fun k : ℕ => fderiv ℝ G (TM c s hs (projField k K) y)) atTop
      (𝓝 (fderiv ℝ G (TM c s hs K y))) := (hD.tendsto _).comp hTy
  unfold ramerSum
  refine tendsto_finsetSum _ (fun p _ => ?_)
  set b := weightedRealHilbertBasis (cmModeWeight c) p
  set u := cmToFullWeightedHilbert c s (zero_le_of_half_lt hs) b
  have hDK : Tendsto (fun k : ℕ => fderiv ℝ (projField k K) y u) atTop (𝓝 (fderiv ℝ K y u)) := by
    have : ∀ k, fderiv ℝ (projField k K) y u = headProj c k (fderiv ℝ K y u) := by
      intro k
      have hf : fderiv ℝ (projField k K) y = (headProj c k).comp (fderiv ℝ K y) :=
        ((headProj c k).hasFDerivAt.comp _ (dK y).hasFDerivAt).fderiv
      rw [hf]; rfl
    simp only [this]
    exact headProj_tendsto c _
  have hv : Tendsto (fun k : ℕ => u + inclE c s hs (fderiv ℝ (projField k K) y u)) atTop
      (𝓝 (u + inclE c s hs (fderiv ℝ K y u))) :=
    tendsto_const_nhds.add ((inclE c s hs).continuous.continuousAt.tendsto.comp hDK)
  have hw : Tendsto (fun k : ℕ => fderiv ℝ G (TM c s hs (projField k K) y)
      (u + inclE c s hs (fderiv ℝ (projField k K) y u))) atTop
      (𝓝 (fderiv ℝ G (TM c s hs K y) (u + inclE c s hs (fderiv ℝ K y u)))) :=
    (isBoundedBilinearMap_apply.continuous.tendsto
      (fderiv ℝ G (TM c s hs K y), u + inclE c s hs (fderiv ℝ K y u))).comp (hDy.prodMk_nhds hv)
  have hP := (headProj c m).continuous
  have t1 : Tendsto (fun k : ℕ => rangeComp m G (TM c s hs (projField k K)) y) atTop
      (𝓝 (rangeComp m G (TM c s hs K) y)) := (hP.tendsto _).comp hGy
  have t2 : Tendsto (fun k : ℕ => fderiv ℝ (rangeComp m G (TM c s hs (projField k K))) y u) atTop
      (𝓝 (fderiv ℝ (rangeComp m G (TM c s hs K)) y u)) := by
    simp only [fderiv_rangeComp hs m G dG _ (dKk _), fderiv_rangeComp hs m G dG _ dK]
    exact (hP.tendsto _).comp hw
  exact (tendsto_const_nhds.mul (tendsto_const_nhds.inner t1)).sub (tendsto_const_nhds.inner t2)

variable (c s)

/-- **Item 3.** -/
theorem ramerDiv_rangeComp_tendsto_ae (hs : (1 : ℝ) / 2 < s) (m : ℕ)
    (G K : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K) :
    ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun k : ℕ => ramerDiv c s hs (rangeComp m G (TM c s hs (projField k K))) z) atTop
        (𝓝 (ramerDiv c s hs (rangeComp m G (TM c s hs K)) z)) := by
  have hall : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val), ∀ k : ℕ,
      ramerDiv c s hs (rangeComp m G (TM c s hs (projField k K))) z =
        ramerA c s (zero_le_of_half_lt hs) m (rangeComp m G (TM c s hs (projField k K))) z := by
    rw [ae_all_iff]
    intro k
    exact ramerDiv_ae_eq_ramerA c s hs _
      (contDiff_rangeComp hs m G _ hG (contDiff_projField k K hK))
      (fun x => headProj_idem _ _)
  have h0 := ramerDiv_ae_eq_ramerA c s hs (rangeComp m G (TM c s hs K))
    (contDiff_rangeComp hs m G K hG hK) (fun x => headProj_idem _ _)
  filter_upwards [hall, h0] with z h1 h2
  rw [h2]
  have := tendsto_ramerSum_rangeComp hs m G K (hG.of_le (by norm_num)) (hK.of_le (by norm_num))
    (headPt c m z : ActualCM c) (NlsGge.Measure.fullWeightedSequenceRealization c s z)
  simp only [h1]
  exact this

end Limits

end NlsGge.Ramer
