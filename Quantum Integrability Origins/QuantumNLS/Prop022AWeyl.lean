import Mathlib
import QuantumNLS.Prop022ACoherent
import QuantumNLS.Prop022SmoothDomainR126

/-! PROP-022 route A, stage A2b: `Γ(R)`-covariance of the source/printed Weyl operators for every
unitary `R` of `L²(𝕋_L)`.

`TT R = Vtil (Γ(R))` is `Γ(R)` in free occupation coordinates.  Using the frozen
`Prop022OWeylField.sourceWeyl_of_field`, it suffices to show that `TT R` is field covariant for
`coordinateMap R`.  The proof:

1. `AC1`: on a sector, the coordinate annihilation `A h` is covariant (both sides are bounded maps
   `Sym^{n+1} → ℓ²(Occ)`; they agree on the power vectors by `ann_emb_power`, whose span is dense
   by `powers_total`).
2. `CC`: the coordinate creation `C h` is covariant on a sector, by duality with `AC1`
   (the frozen adjoint relations `C_adjoint`, tested against kets).
3. `field_cov_sector`, then `fieldCovariant` for all smooth vectors, testing against kets and using
   the symmetry of the field.
4. `weyl_covariant`: `Γ(R) W(f) Γ(R)⁻¹ = W(R f)`, and the printed version. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop022AWeyl
open Occupation OccupationUnitary TensorCarrier PhysicalTensor BetheCoefficientTransform
open Ext025B3PhysicalSectors Ext006PhysFockCoord Ext006PhysicalVacuum Prop022TensorCompressionR115
open Ext006SmoothOperatorsR34a Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006QuasifreeWeak
open Ext006PhysQuasifree Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006IdentityCyclicR35a
open Prop022ACoherent Prop022GTensor
variable {L : ℝ} [Fact (0 < L)]

/-- `Γ(R)` in free occupation coordinates. -/
def TT (R : L2T L ≃ₗᵢ[ℂ] L2T L) : OF ≃ₗᵢ[ℂ] OF :=
  Vtil (L := L) (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L)

lemma fockMap_single (R : L2T L ≃ₗᵢ[ℂ] L2T L) (n : ℕ) (x : HN L n) :
    (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) (lp.single 2 n x : Fock L) =
      (lp.single 2 n (symMap R n x) : Fock L) := by
  apply lp.ext
  funext k
  change symMap R k ((lp.single 2 n x : Fock L) k) = (lp.single 2 n (symMap R n x) : Fock L) k
  by_cases hk : k = n
  · subst hk
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ hk, lp.single_apply_ne _ _ _ hk]
    simp

lemma TT_emb (R : L2T L ≃ₗᵢ[ℂ] L2T L) (n : ℕ) (x : HN L n) :
    TT R (secEmb n x) = secEmb n (symMap R n x) := by
  change Phi ((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) ((Phi (L := L)).symm (secEmb n x))) = _
  rw [secEmb, LinearIsometryEquiv.symm_apply_apply, fockMap_single]
  rfl

lemma TT_symm_emb (R : L2T L ≃ₗᵢ[ℂ] L2T L) (n : ℕ) (x : HN L n) :
    (TT R).symm (secEmb n x) = secEmb n ((symMap R n).symm x) := by
  rw [LinearIsometryEquiv.symm_apply_eq, TT_emb, LinearIsometryEquiv.apply_symm_apply]

lemma symMap_power (R : L2T L ≃ₗᵢ[ℂ] L2T L) (m : ℕ) (g : L2T L) :
    symMap R m (power m g) = power m (R g) :=
  Subtype.ext (tensorMap_htpow R m g)

lemma norm_emb (n : ℕ) (x : HN L n) : ‖secEmb n x‖ = ‖x‖ := by
  rw [secEmb, LinearIsometryEquiv.norm_map]
  exact lp.norm_single (by norm_num) n x

lemma mass_emb (n : ℕ) (x : HN L n) :
    ∑' m : Occ, (total m : ℝ) * ‖secEmb n x m‖ ^ 2 = (n : ℝ) * ‖x‖ ^ 2 := by
  have h1 : ∀ m : Occ, (total m : ℝ) * ‖secEmb n x m‖ ^ 2 = (n : ℝ) * ‖secEmb n x m‖ ^ 2 := by
    intro m
    by_cases h : total m = n
    · rw [h]
    · rw [emb_apply_of_ne n x m h]
      simp
  have h2 := (lp.hasSum_norm (p := 2) (by norm_num) (secEmb n x)).tsum_eq
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  simp only [h1]
  rw [tsum_mul_left, h2, norm_emb]

/-! ### Annihilation on a sector, as a bounded map -/

/-- The coordinate annihilation restricted to the sector `n+1`. -/
def annLin (h : OneParticle) (n : ℕ) : HN L (n + 1) →ₗ[ℂ] OF where
  toFun x := (A h ⟨secEmb (n + 1) x, emb_smooth _ _⟩).1
  map_add' x y := by
    change (A h ⟨secEmb (n + 1) (x + y), emb_smooth _ _⟩).1 =
      (A h ⟨secEmb (n + 1) x, emb_smooth _ _⟩).1 + (A h ⟨secEmb (n + 1) y, emb_smooth _ _⟩).1
    have : (⟨secEmb (n + 1) (x + y), emb_smooth _ _⟩ : D) =
        ⟨secEmb (n + 1) x, emb_smooth _ _⟩ + ⟨secEmb (n + 1) y, emb_smooth _ _⟩ :=
      Subtype.ext (emb_add _ _ _)
    rw [this, map_add]
    rfl
  map_smul' c x := by
    change (A h ⟨secEmb (n + 1) (c • x), emb_smooth _ _⟩).1 =
      c • (A h ⟨secEmb (n + 1) x, emb_smooth _ _⟩).1
    have : (⟨secEmb (n + 1) (c • x), emb_smooth _ _⟩ : D) =
        c • (⟨secEmb (n + 1) x, emb_smooth _ _⟩ : D) := Subtype.ext (emb_smul _ _ _)
    rw [this, map_smul]
    rfl

lemma annLin_bound (h : OneParticle) (n : ℕ) (x : HN L (n + 1)) :
    ‖annLin h n x‖ ≤ (‖h‖ * Real.sqrt ((n : ℝ) + 1)) * ‖x‖ := by
  have h1 := A_norm_sq_le_mass h ⟨secEmb (n + 1) x, emb_smooth _ _⟩
  change ‖annLin h n x‖ ^ 2 ≤ ‖h‖ ^ 2 * ∑' m : Occ, (total m : ℝ) * ‖secEmb (n + 1) x m‖ ^ 2 at h1
  rw [mass_emb] at h1
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc ‖annLin h n x‖ ^ 2 ≤ ‖h‖ ^ 2 * (((n + 1 : ℕ) : ℝ) * ‖x‖ ^ 2) := h1
    _ = ((‖h‖ * Real.sqrt ((n : ℝ) + 1)) * ‖x‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      push_cast
      ring

/-- Annihilation on the sector `n+1` as a bounded operator into `ℓ²(Occ)`. -/
def annMap (h : OneParticle) (n : ℕ) : HN L (n + 1) →L[ℂ] OF :=
  (annLin h n).mkContinuous (‖h‖ * Real.sqrt ((n : ℝ) + 1)) (annLin_bound h n)

lemma annMap_apply (h : OneParticle) (n : ℕ) (x : HN L (n + 1)) :
    annMap h n x = (A h ⟨secEmb (n + 1) x, emb_smooth _ _⟩).1 := rfl

lemma ann_emb_zero (h : OneParticle) (x : HN L 0) :
    (A h ⟨secEmb 0 x, emb_smooth _ _⟩).1 = 0 := by
  apply lp.ext
  funext m
  change inner ℂ h (xvec (secEmb 0 x) m) = 0
  have : xvec (secEmb 0 x) m = 0 := by
    apply lp.ext
    funext a
    change (Real.sqrt ((m a : ℝ) + 1) : ℂ) * secEmb 0 x (m + e a) = 0
    rw [emb_apply_of_ne 0 x (m + e a) (by simp [total_add_e])]
    simp
  rw [this]
  simp

/-- The coordinate map of `R`. -/
def Rr (R : L2T L ≃ₗᵢ[ℂ] L2T L) : L2T L ≃L[ℝ] L2T L :=
  R.toContinuousLinearEquiv.restrictScalars ℝ

lemma coordinateMap_Rr (R : L2T L ≃ₗᵢ[ℂ] L2T L) (h : OneParticle) :
    Prop022OWeylField.coordinateMap (Rr R) h = ghat (R ((QuantumNLS.Fourier.fourierL2 L).symm h)) := rfl

lemma inner_coordinateMap (R : L2T L ≃ₗᵢ[ℂ] L2T L) (h : OneParticle) (g : L2T L) :
    inner ℂ (Prop022OWeylField.coordinateMap (Rr R) h) (ghat (R g)) = inner ℂ h (ghat g) := by
  rw [coordinateMap_Rr]
  unfold ghat
  rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
  conv_rhs => rw [← (QuantumNLS.Fourier.fourierL2 L).apply_symm_apply h]
  rw [LinearIsometryEquiv.inner_map_map]

lemma dense_powers (n : ℕ) :
    Dense (Submodule.span ℂ (Set.range (power (L := L) n)) : Set (HN L n)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply powers_total
  intro g
  have := (Submodule.mem_orthogonal _ x).mp hx (power n g) (Submodule.subset_span ⟨g, rfl⟩)
  exact this

/-- **A-covariance on a sector.** -/
theorem AC1 (R : L2T L ≃ₗᵢ[ℂ] L2T L) (h : OneParticle) (n : ℕ) (x : HN L (n + 1)) :
    TT R (annMap h n x) =
      annMap (Prop022OWeylField.coordinateMap (Rr R) h) n (symMap R (n + 1) x) := by
  let F₁ : HN L (n + 1) →L[ℂ] OF :=
    (TT R).toContinuousLinearEquiv.toContinuousLinearMap ∘L annMap h n
  let F₂ : HN L (n + 1) →L[ℂ] OF :=
    annMap (Prop022OWeylField.coordinateMap (Rr R) h) n ∘L
      (symMap R (n + 1)).toContinuousLinearEquiv.toContinuousLinearMap
  have hext : F₁ = F₂ := by
    apply ContinuousLinearMap.ext_on (dense_powers (n + 1))
    rintro _ ⟨g, rfl⟩
    change TT R (annMap h n (power (n + 1) g)) =
      annMap (Prop022OWeylField.coordinateMap (Rr R) h) n (symMap R (n + 1) (power (n + 1) g))
    rw [annMap_apply, ann_emb_power, symMap_power, annMap_apply, ann_emb_power, map_smul, TT_emb,
      symMap_power, inner_coordinateMap]
  exact congrArg (fun F => F x) hext

/-! ### Creation by duality, the field on a sector, and the field covariance -/

/-- Smooth-vector version of an embedded sector vector. -/
def embD (n : ℕ) (x : HN L n) : D := ⟨secEmb n x, emb_smooth n x⟩

/-- The ket `|k⟩` as a sector vector. -/
def ketVec (k : Occ) : HN L (total k) :=
  (physicalOccupation L (total k)).symm (lp.single 2 (⟨k, rfl⟩ : Arr (total k)) (1 : ℂ))

lemma ket_eq_emb (k : Occ) : (ketD k).1 = secEmb (total k) (ketVec (L := L) k) := by
  apply lp.ext
  funext m
  by_cases h : total m = total k
  · rw [emb_apply_of_total _ _ m h, ketVec, LinearIsometryEquiv.apply_symm_apply]
    by_cases hmk : m = k
    · subst hmk
      simp [ketD]
    · have hne : (⟨m, h⟩ : Arr (total k)) ≠ ⟨k, rfl⟩ := fun hh => hmk (congrArg Subtype.val hh)
      rw [lp.single_apply_ne _ _ _ hne]
      change (lp.single 2 k (1 : ℂ) : OF) m = 0
      rw [lp.single_apply_ne _ _ _ hmk]
  · rw [emb_apply_of_ne _ _ m h]
    have hmk : m ≠ k := fun hh => h (by rw [hh])
    change (lp.single 2 k (1 : ℂ) : OF) m = 0
    rw [lp.single_apply_ne _ _ _ hmk]

lemma TT_symm_ket (R : L2T L ≃ₗᵢ[ℂ] L2T L) (k : Occ) :
    (TT R).symm (ketD k).1 = secEmb (total k) ((symMap R (total k)).symm (ketVec (L := L) k)) := by
  rw [ket_eq_emb (L := L), TT_symm_emb]

lemma ann_pair (R : L2T L ≃ₗᵢ[ℂ] L2T L) (h : OneParticle) (j : ℕ) (y : HN L j) (n : ℕ)
    (x : HN L n) :
    inner ℂ (A h (embD j y)).1 (secEmb n x) =
      inner ℂ (A (Prop022OWeylField.coordinateMap (Rr R) h) (embD j (symMap R j y))).1
        (secEmb n (symMap R n x)) := by
  cases j with
  | zero =>
    rw [show (A h (embD 0 y)).1 = 0 from ann_emb_zero h y,
      show (A (Prop022OWeylField.coordinateMap (Rr R) h) (embD 0 (symMap R 0 y))).1 = 0 from
        ann_emb_zero _ _]
    simp
  | succ j' =>
    change inner ℂ (annMap h j' y) (secEmb n x) = inner ℂ
      (annMap (Prop022OWeylField.coordinateMap (Rr R) h) j' (symMap R (j' + 1) y))
        (secEmb n (symMap R n x))
    rw [← AC1, ← TT_emb, LinearIsometryEquiv.inner_map_map]

/-- **C-covariance on a sector**, by duality with `AC1`. -/
theorem CC (R : L2T L ≃ₗᵢ[ℂ] L2T L) (h : OneParticle) (n : ℕ) (x : HN L n) :
    TT R (C h (embD n x)).1 =
      (C (Prop022OWeylField.coordinateMap (Rr R) h) (embD n (symMap R n x))).1 := by
  apply Ext006ClosedFieldGraphsR36a.ket_total
  intro k
  set y : HN L (total k) := (symMap R (total k)).symm (ketVec k) with hy
  have hsy : symMap R (total k) y = ketVec k := by simp [hy]
  have h1 : inner ℂ (ketD k).1 (TT R (C h (embD n x)).1) =
      inner ℂ (embD (total k) y).1 (C h (embD n x)).1 := by
    rw [← (TT R).symm.inner_map_map, LinearIsometryEquiv.symm_apply_apply, TT_symm_ket]
    rfl
  rw [h1, C_adjoint]
  have h2 := ann_pair R h (total k) y n x
  rw [hsy] at h2
  show inner ℂ (A h (embD (total k) y)).1 (secEmb n x) = _
  rw [h2]
  have h3 : (ketD k).1 = (embD (total k) (ketVec (L := L) k)).1 := ket_eq_emb k
  rw [h3, C_adjoint]
  try rfl

lemma field_apply (h : OneParticle) (v : D) : (field h v).1 = (A h v).1 + (C h v).1 := rfl

theorem field_cov_sector (R : L2T L ≃ₗᵢ[ℂ] L2T L) (h : OneParticle) (n : ℕ) (x : HN L n) :
    TT R (field h (embD n x)).1 =
      (field (Prop022OWeylField.coordinateMap (Rr R) h) (embD n (symMap R n x))).1 := by
  rw [field_apply, field_apply, map_add, CC]
  congr 1
  cases n with
  | zero =>
    rw [show (A h (embD 0 x)).1 = 0 from ann_emb_zero h x,
      show (A (Prop022OWeylField.coordinateMap (Rr R) h) (embD 0 (symMap R 0 x))).1 = 0 from
        ann_emb_zero _ _]
    simp
  | succ n' =>
    exact AC1 R h n' x

lemma field_symm (h : OneParticle) (v w : D) :
    inner ℂ v.1 (field h w).1 = inner ℂ (field h v).1 w.1 := by
  rw [field_apply, field_apply, inner_add_right, inner_add_left, A_adjoint, C_adjoint]
  ring

lemma moment_gamma (R : L2T L ≃ₗᵢ[ℂ] L2T L) (j : ℕ) (y : Fock L) :
    (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) y ∈ Ext005Moments.momentDomain (L := L) j ↔
      y ∈ Ext005Moments.momentDomain (L := L) j := by
  rw [Ext005Moments.momentDomain_iff, Ext005Moments.momentDomain_iff]
  change Summable (fun N : ℕ => Ext005Moments.momentWeight j N * ‖fockMap R y N‖ ^ 2) ↔ _
  simp only [norm_fockMap_sector]

lemma smooth_TT (R : L2T L ≃ₗᵢ[ℂ] L2T L) (x : OF) : Smooth x ↔ Smooth (TT R x) := by
  have e1 : Smooth x ↔ ∀ j : ℕ, (Phi (L := L)).symm x ∈ Ext005Moments.momentDomain (L := L) j := by
    rw [← Prop022SmoothDomainR126.smooth_iff_moments, Prop022OCovariance.coefficient_symm]
  have e2 : Smooth (TT R x) ↔ ∀ j : ℕ,
      (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) ((Phi (L := L)).symm x) ∈
        Ext005Moments.momentDomain (L := L) j := by
    rw [← Prop022SmoothDomainR126.smooth_iff_moments]
    rfl
  rw [e1, e2]
  exact forall_congr' (fun j => (moment_gamma R j _).symm)

/-- **Field covariance of `Γ(R)`.** -/
theorem fieldCovariant (R : L2T L ≃ₗᵢ[ℂ] L2T L) :
    Prop022OWeylField.FieldCovariant (TT R) (Prop022OWeylField.coordinateMap (Rr R)) := by
  refine ⟨smooth_TT R, fun h v w hw => ?_⟩
  apply Ext006ClosedFieldGraphsR36a.ket_total
  intro k
  set y : HN L (total k) := (symMap R (total k)).symm (ketVec k) with hy
  have hsy : symMap R (total k) y = ketVec k := by simp [hy]
  have hket : (ketD k).1 = (embD (total k) (ketVec (L := L) k)).1 := ket_eq_emb k
  have hTy : (TT R).symm (ketD k).1 = (embD (total k) y).1 := TT_symm_ket R k
  have hf := field_cov_sector R h (total k) y
  rw [hsy] at hf
  calc inner ℂ (ketD k).1 (TT R (field h v).1)
      = inner ℂ (embD (total k) y).1 (field h v).1 := by
        rw [← (TT R).symm.inner_map_map, LinearIsometryEquiv.symm_apply_apply, hTy]
    _ = inner ℂ (field h (embD (total k) y)).1 v.1 := field_symm h _ v
    _ = inner ℂ (TT R (field h (embD (total k) y)).1) (TT R v.1) := by
        rw [(TT R).inner_map_map]
    _ = inner ℂ (field (Prop022OWeylField.coordinateMap (Rr R) h) (embD (total k) (ketVec k))).1 w.1 := by
        rw [hf, hw]
    _ = inner ℂ (embD (total k) (ketVec (L := L) k)).1
          (field (Prop022OWeylField.coordinateMap (Rr R) h) w).1 :=
        (field_symm _ _ w).symm
    _ = _ := by rw [← hket]

/-- **Weyl covariance of the source Weyl operator under `Γ(R)`.** -/
theorem sourceWeyl_covariant (R : L2T L ≃ₗᵢ[ℂ] L2T L) (f : L2T L) (x : Fock L) :
    (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) (Ext006SourceWeylR44a.sourceWeyl f x) =
      Ext006SourceWeylR44a.sourceWeyl (R f)
        ((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) x) := by
  have h := Prop022OWeylField.sourceWeyl_of_field (Rr R)
    (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) (fieldCovariant R) f
    ((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) x)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h

/-- **Printed Weyl covariance** `Γ(R) W(v) Γ(R)⁻¹ = W(R v)`, `W(v) = exp(a*(v) - a(v))`. -/
theorem printedWeyl_covariant (R : L2T L ≃ₗᵢ[ℂ] L2T L) (v : L2T L) (x : Fock L) :
    (fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) (Prop022OVacuum.printedWeyl v x) =
      Prop022OVacuum.printedWeyl (R v)
        ((fockMap R : Fock L ≃ₗᵢ[ℂ] Fock L) x) := by
  unfold Prop022OVacuum.printedWeyl
  rw [sourceWeyl_covariant, map_smul]

end QuantumNLS.Prop022AWeyl

#print axioms QuantumNLS.Prop022AWeyl.AC1
#print axioms QuantumNLS.Prop022AWeyl.fieldCovariant
#print axioms QuantumNLS.Prop022AWeyl.sourceWeyl_covariant
#print axioms QuantumNLS.Prop022AWeyl.printedWeyl_covariant
