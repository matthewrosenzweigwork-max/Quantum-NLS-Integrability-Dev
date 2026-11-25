import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.LIB.LIB023
import NlsGge.ThirdConsultation.DM.DMShared78

/- DM-009 production module (assembled by proof development from compiled blocks, each inlined exactly once;
   lane selftest: DM009_HEAD_SELFTEST01.lean.txt, which inlines the DMShared78 definitions because the
   worker mirror lacks that module). Block order: S1 (transport), S2 helpers, S8, S9, S3 (compactness),
   S7 IDENT01 (includes S4 Riesz), S6C (path reversal), S7C (diagonal identity), S10PART, HEADCOND, HEAD. -/
/- DM-009 support S1 (proof development). Generic transport of TOTALIZED `Ring.inverse` through a
   conjugate-linear continuous bijection `Φ` intertwining operators: `B (Φ.f x) = Φ.f (A x)`.
   No KST/DM dependency (pure Mathlib). Used for the total-inverse step of DM-009 (MAP01 M3).
   Totalization: when `1 - A` is not a unit, both sides vanish (`Ring.inverse_non_unit`). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.DM009Transport

/-- A conjugate-linear continuous bijection of a complex normed space, given with its two-sided
inverse `g`. -/
structure ConjBij (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  f : E → E
  g : E → E
  f_add : ∀ x y : E, f (x + y) = f x + f y
  f_smul : ∀ (c : ℂ) (x : E), f (c • x) = star c • f x
  g_add : ∀ x y : E, g (x + y) = g x + g y
  g_smul : ∀ (c : ℂ) (x : E), g (c • x) = star c • g x
  f_cont : Continuous f
  g_cont : Continuous g
  fg : ∀ x : E, f (g x) = x
  gf : ∀ x : E, g (f x) = x

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The two-sided inverse, as a conjugate-linear bijection. -/
def ConjBij.symm (Φ : ConjBij E) : ConjBij E where
  f := Φ.g
  g := Φ.f
  f_add := Φ.g_add
  f_smul := Φ.g_smul
  g_add := Φ.f_add
  g_smul := Φ.f_smul
  f_cont := Φ.g_cont
  g_cont := Φ.f_cont
  fg := Φ.gf
  gf := Φ.fg

theorem ConjBij.f_zero (Φ : ConjBij E) : Φ.f 0 = 0 := by
  have h := Φ.f_add 0 0
  rw [add_zero] at h
  simpa using h

theorem ConjBij.f_sub (Φ : ConjBij E) (x y : E) : Φ.f (x - y) = Φ.f x - Φ.f y := by
  have h := Φ.f_add (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-- Conjugation of an operator by `Φ`. -/
def conjOp (Φ : ConjBij E) (R : E →L[ℂ] E) : E →L[ℂ] E where
  toFun x := Φ.f (R (Φ.g x))
  map_add' x y := by
    simp only [Φ.g_add, map_add, Φ.f_add]
  map_smul' c x := by
    simp only [Φ.g_smul, map_smul, Φ.f_smul, RingHom.id_apply, star_star]
  cont := Φ.f_cont.comp (R.continuous.comp Φ.g_cont)

theorem conjOp_apply (Φ : ConjBij E) (R : E →L[ℂ] E) (x : E) :
    conjOp Φ R x = Φ.f (R (Φ.g x)) := rfl

theorem conjOp_one (Φ : ConjBij E) : conjOp Φ 1 = 1 := by
  ext x
  simp [conjOp_apply, Φ.fg]

theorem conjOp_sub (Φ : ConjBij E) (R S : E →L[ℂ] E) :
    conjOp Φ (R - S) = conjOp Φ R - conjOp Φ S := by
  ext x
  simp [conjOp_apply, Φ.f_sub]

/-- The intertwining relation read backwards: `Φ.g (B y) = A (Φ.g y)`. -/
theorem g_intertwine (Φ : ConjBij E) (A B : E →L[ℂ] E)
    (hint : ∀ x : E, B (Φ.f x) = Φ.f (A x)) (y : E) : Φ.g (B y) = A (Φ.g y) := by
  have h := hint (Φ.g y)
  rw [Φ.fg] at h
  rw [h, Φ.gf]

/-- Core transport: a unit `1 - A` gives a unit `1 - B`, with inverse the conjugated inverse. -/
theorem transport_core (Φ : ConjBij E) (A B : E →L[ℂ] E)
    (hint : ∀ x : E, B (Φ.f x) = Φ.f (A x)) (hu : IsUnit (1 - A)) :
    IsUnit (1 - B) ∧ Ring.inverse (1 - B) = conjOp Φ (Ring.inverse (1 - A)) := by
  set R : E →L[ℂ] E := Ring.inverse (1 - A) with hRdef
  have hRL : (1 - A) * R = 1 := Ring.mul_inverse_cancel (1 - A) hu
  have hLR : R * (1 - A) = 1 := Ring.inverse_mul_cancel (1 - A) hu
  have hg : ∀ y : E, Φ.g (B y) = A (Φ.g y) := g_intertwine Φ A B hint
  have hBop : ∀ X : E →L[ℂ] E, B * conjOp Φ X = conjOp Φ (A * X) := by
    intro X
    ext y
    simp only [mul_apply_eq_comp, conjOp_apply, hint]
  have hBop' : ∀ X : E →L[ℂ] E, conjOp Φ X * B = conjOp Φ (X * A) := by
    intro X
    ext y
    simp only [mul_apply_eq_comp, conjOp_apply, hg]
  have e1 : R - A * R = (1 - A) * R := by rw [sub_mul, one_mul]
  have e2 : R - R * A = R * (1 - A) := by rw [mul_sub, mul_one]
  have h1 : (1 - B) * conjOp Φ R = 1 := by
    rw [sub_mul, one_mul, hBop R, ← conjOp_sub, e1, hRL, conjOp_one]
  have h2 : conjOp Φ R * (1 - B) = 1 := by
    rw [mul_sub, mul_one, hBop' R, ← conjOp_sub, e2, hLR, conjOp_one]
  have hU : IsUnit (1 - B) := isUnit_iff_exists.mpr ⟨conjOp Φ R, h1, h2⟩
  refine ⟨hU, ?_⟩
  calc Ring.inverse (1 - B)
      = Ring.inverse (1 - B) * ((1 - B) * conjOp Φ R) := by rw [h1, mul_one]
    _ = (Ring.inverse (1 - B) * (1 - B)) * conjOp Φ R := by rw [mul_assoc]
    _ = conjOp Φ R := by rw [Ring.inverse_mul_cancel (1 - B) hU, one_mul]

/-- Totalized transport of `Ring.inverse` (no unit hypothesis) through a conjugate-linear
intertwining bijection: `Ring.inverse (1 - B) (Φ.f v) = Φ.f (Ring.inverse (1 - A) v)`. -/
theorem transport_inverse (Φ : ConjBij E) (A B : E →L[ℂ] E)
    (hint : ∀ x : E, B (Φ.f x) = Φ.f (A x)) (v : E) :
    Ring.inverse (1 - B) (Φ.f v) = Φ.f (Ring.inverse (1 - A) v) := by
  by_cases hu : IsUnit (1 - A)
  · rw [(transport_core Φ A B hint hu).2, conjOp_apply, Φ.gf]
  · have hnu : ¬ IsUnit (1 - B) := by
      intro hB
      exact hu (transport_core Φ.symm B A (fun x => (g_intertwine Φ A B hint x).symm) hB).1
    rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ hnu]
    simp [Φ.f_zero]

end NlsGge.DM009Transport

/- DM-009 S2 helpers (proof development, 2026-10-31).
   Re-proved LOCALLY (not edited in KST015): the body below is KST015 lines 18-363
   (`NlsGge/Atomic/KST/KST015.lean`, sha256 a00896ca...) copied byte-identically except that
   the `private` modifiers are removed and the namespace is `NlsGge.DM009Psi`.
   It contains the conjugate-linear map `PsiMap` on KSTPairL2, its algebra, the Q-intertwining
   `PsiMap_Q` (for the KST006 qOperator with a real-form potential) and the potential
   intertwining `PsiMap_potential`. KST015 `reduced_realForm_symmetry` is NOT used.
   Imports: production KST018 only (no own-folder import). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory NlsGge.Schur NlsGge.Analysis NlsGge.Pilot
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
  NlsGge.Atomic.KST007 NlsGge.Atomic.KST013
open scoped InnerProductSpace

namespace NlsGge.DM009Psi


/-! ### Pointwise star on the doubled-circle scalar space -/

lemma starS_add (f g : SpectralScalarL2) : star (f + g) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add f g, Lp.coeFn_star (f + g), Lp.coeFn_add (star f) (star g),
    Lp.coeFn_star f, Lp.coeFn_star g] with x h1 h2 h3 h4 h5
  simp only [h2, h3, h4, h5, Pi.star_apply, Pi.add_apply, h1, star_add]

lemma starS_smul (c : ℂ) (f : SpectralScalarL2) : star (c • f) = star c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_star (c • f), Lp.coeFn_smul (star c) (star f),
    Lp.coeFn_star f] with x h1 h2 h3 h4
  simp only [h2, h3, h4, Pi.star_apply, Pi.smul_apply, h1, smul_eq_mul, star_mul']

lemma starS_sub (f g : SpectralScalarL2) : star (f - g) = star f - star g := by
  have h := starS_add f (-g)
  have h2 := starS_smul (-1 : ℂ) g
  rw [sub_eq_add_neg, h]
  rw [sub_eq_add_neg]
  congr 1
  have : (-g) = (-1 : ℂ) • g := by simp
  rw [this, h2]
  simp

lemma starS_zero : star (0 : SpectralScalarL2) = 0 := by
  have h := starS_add (0 : SpectralScalarL2) 0
  rw [add_zero] at h
  exact left_eq_add.mp h

lemma starS_inner (f g : SpectralScalarL2) :
    ⟪star f, star g⟫_ℂ = star ⟪f, g⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hae : (fun a => ⟪(star f : SpectralScalarL2) a, (star g : SpectralScalarL2) a⟫_ℂ) =ᵐ[spectralHaar]
      fun a => star ⟪f a, g a⟫_ℂ := by
    filter_upwards [Lp.coeFn_star f, Lp.coeFn_star g] with x h1 h2
    rw [h1, h2]
    simp [RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae hae]
  exact integral_conj


lemma starS_star (f : SpectralScalarL2) : star (star f) = f := star_star f

lemma starS_basis (m : ℤ) : star (spectralBasis m) = spectralBasis (-m) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (spectralBasis m), coeFn_fourierLp (T := (2 : ℝ)) 2 m,
    coeFn_fourierLp (T := (2 : ℝ)) 2 (-m)] with x h1 h2 h3
  change (star (spectralBasis m) : SpectralScalarL2) x = (spectralBasis (-m) : SpectralScalarL2) x
  rw [h1]
  change star ((fourierLp 2 m : SpectralScalarL2) x) = (fourierLp 2 (-m) : SpectralScalarL2) x
  rw [h2, h3, fourier_neg]
  rfl

lemma spectralCoeff_eq_inner (g : SpectralScalarL2) (k : ℤ) :
    spectralCoeff g k = ⟪spectralBasis k, g⟫_ℂ := by
  have hb : (fourierBasis (T := (2 : ℝ))) k = spectralBasis k := congrFun coe_fourierBasis k
  unfold spectralCoeff
  calc _ = ⟪fourierBasis (T := (2 : ℝ)) k, g⟫_ℂ :=
        (fourierBasis (T := (2 : ℝ))).repr_apply_apply g k
    _ = ⟪spectralBasis k, g⟫_ℂ := by rw [hb]; rfl

lemma spectralCoeff_star (g : SpectralScalarL2) (l : ℤ) :
    spectralCoeff (star g) l = star (spectralCoeff g (-l)) := by
  rw [spectralCoeff_eq_inner, spectralCoeff_eq_inner]
  have h : spectralBasis l = star (spectralBasis (-l)) := by
    rw [starS_basis, neg_neg]
  rw [h, starS_inner]

lemma starS_mult (k : ℤ) (f : SpectralScalarL2) :
    star (fourierMultiplier k f) = fourierMultiplier (-k) (star f) := by
  apply Lp.ext
  have hm : (fourierMultiplier k f : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => fourier k x * f x) := fourierMultiplierValue_ae k f
  have hm' : (fourierMultiplier (-k) (star f) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (fun x => fourier (-k) x * (star f : SpectralScalarL2) x) :=
    fourierMultiplierValue_ae (-k) (star f)
  filter_upwards [Lp.coeFn_star (fourierMultiplier k f), hm, hm', Lp.coeFn_star f] with x h1 h2 h3 h4
  change (star (fourierMultiplier k f) : SpectralScalarL2) x =
    (fourierMultiplier (-k) (star f) : SpectralScalarL2) x
  rw [h1, h3, Pi.star_apply, h2, h4, Pi.star_apply, fourier_neg]
  simp [star_mul']

lemma cover_star (u : NlsGge.Pilot.PhysicalL2) :
    naturalPhysicalCoverL2 (star u) = star (naturalPhysicalCoverL2 u) := by
  apply Lp.ext
  have hq := naturalPhysicalCover_preserving.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_star u)
  filter_upwards [naturalPhysicalCoverL2_ae (star u), naturalPhysicalCoverL2_ae u,
    Lp.coeFn_star (naturalPhysicalCoverL2 u), hq] with x h1 h2 h3 h4
  change (naturalPhysicalCoverL2 (star u) : SpectralScalarL2) x =
    (star (naturalPhysicalCoverL2 u) : SpectralScalarL2) x
  rw [h1, h3, Pi.star_apply, h2]
  exact h4

/-! ### Real-form symmetry of the Fourier coefficients of the potential -/

lemma potentialCoeff_eq (φ : PhysicalPairLp) (b : Bool) (k : ℤ) :
    potentialCoeff φ b k = spectralCoeff (naturalPhysicalCoverL2 (φ b)) k := by
  unfold potentialCoeff spectralCoeff
  exact (fourierBasis_repr _ k).symm

lemma spectralCoeff_smul (c : ℂ) (g : SpectralScalarL2) (k : ℤ) :
    spectralCoeff (c • g) k = c * spectralCoeff g k := by
  rw [spectralCoeff_eq_inner, spectralCoeff_eq_inner, inner_smul_right]

lemma potentialCoeff_false (φ : PhysicalPairLp) (ε : ℝ)
    (h : φ false = (ε : ℂ) • star (φ true)) (k : ℤ) :
    potentialCoeff φ false k = (ε : ℂ) * star (potentialCoeff φ true (-k)) := by
  rw [potentialCoeff_eq, potentialCoeff_eq, h, map_smul, cover_star, spectralCoeff_smul,
    spectralCoeff_star]


/-! ### Scalars -/

lemma epsilon_sq (ε : ℝ) (hε : ε = 1 ∨ ε = -1) : (ε : ℂ) * (ε : ℂ) = 1 := by
  rcases hε with rfl | rfl <;> simp

lemma star_epsilon (ε : ℝ) : star (ε : ℂ) = (ε : ℂ) := by simp

lemma scalar_ext {f g : SpectralScalarL2}
    (h : ∀ l, spectralCoeff f l = spectralCoeff g l) : f = g := by
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext l
  exact h l

lemma tsum_neg_reindex (G : ℤ → ℂ) : ∑' m : ℤ, G (-m) = ∑' m : ℤ, G m :=
  (Equiv.neg ℤ).tsum_eq G

lemma star_tsum_int (F : ℤ → ℂ) : star (∑' m : ℤ, F m) = ∑' m : ℤ, star (F m) := by
  simpa [Complex.star_def] using Complex.conj_tsum F

lemma star_mem_strip {n : ℤ} {z : ℂ} (hz : z ∈ spectralStrip n) :
    star z ∈ spectralStrip n := by
  simpa only [spectralStrip, Set.mem_setOf_eq, Complex.star_def, Complex.conj_re] using hz

lemma star_compl (n : ℤ) (z : ℂ) (k : ℤ) :
    star (complementaryResolventCoeff n z k) = complementaryResolventCoeff n (star z) k := by
  unfold complementaryResolventCoeff
  split_ifs
  · simp
  · rw [star_inv₀]
    congr 1
    simp [Complex.star_def]

/-! ### The conjugate-linear map Psi on the doubled pair space -/

def PsiMap (ε : ℝ) (f : KSTPairL2) : KSTPairL2 :=
  WithLp.toLp 2 (fun b : Bool => if b then star (f false) else (ε : ℂ) • star (f true))

lemma PsiMap_true (ε : ℝ) (f : KSTPairL2) : PsiMap ε f true = star (f false) := rfl

lemma PsiMap_false (ε : ℝ) (f : KSTPairL2) :
    PsiMap ε f false = (ε : ℂ) • star (f true) := rfl

lemma PsiMap_add (ε : ℝ) (f g : KSTPairL2) :
    PsiMap ε (f + g) = PsiMap ε f + PsiMap ε g := by
  apply PiLp.ext
  intro b
  cases b
  · simp [PsiMap_false, starS_add, smul_add]
  · simp [PsiMap_true, starS_add]

lemma PsiMap_smul (ε : ℝ) (c : ℂ) (f : KSTPairL2) :
    PsiMap ε (c • f) = star c • PsiMap ε f := by
  apply PiLp.ext
  intro b
  cases b
  · simp [PsiMap_false, starS_smul, smul_comm]
  · simp [PsiMap_true, starS_smul]

lemma PsiMap_sub (ε : ℝ) (f g : KSTPairL2) :
    PsiMap ε (f - g) = PsiMap ε f - PsiMap ε g := by
  apply PiLp.ext
  intro b
  cases b
  · simp [PsiMap_false, starS_sub, smul_sub]
  · simp [PsiMap_true, starS_sub]

lemma PsiMap_inner (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (x y : KSTPairL2) :
    ⟪PsiMap ε x, PsiMap ε y⟫_ℂ = star ⟪x, y⟫_ℂ := by
  have h1 := epsilon_sq ε hε
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_bool, Fintype.sum_bool]
  simp only [PsiMap_true, PsiMap_false, starS_inner, inner_smul_left, inner_smul_right]
  rw [Complex.conj_ofReal, ← mul_assoc, h1, one_mul, star_add, add_comm]

lemma PsiMap_lower (ε : ℝ) (n : ℤ) : PsiMap ε (kstPnLower n) = kstPnUpper n := by
  apply PiLp.ext
  intro b
  cases b
  · simp [PsiMap_false, kstPnLower, kstPnUpper, starS_zero]
  · simp [PsiMap_true, kstPnLower, kstPnUpper, starS_basis]

lemma PsiMap_upper (ε : ℝ) (n : ℤ) :
    PsiMap ε (kstPnUpper n) = (ε : ℂ) • kstPnLower n := by
  have h1 : (PiLp.single 2 true (spectralBasis (-n)) : KSTPairL2) false = 0 :=
    PiLp.single_eq_of_ne 2 (by decide) _
  have h2 : (PiLp.single 2 false (spectralBasis n) : KSTPairL2) true = 0 :=
    PiLp.single_eq_of_ne 2 (by decide) _
  apply PiLp.ext
  intro b
  cases b
  · rw [PsiMap_false, PiLp.smul_apply]
    simp only [kstPnUpper, kstPnLower, PiLp.single_eq_same, starS_basis, neg_neg]
  · rw [PsiMap_true, PiLp.smul_apply]
    simp only [kstPnUpper, kstPnLower, h1, h2, starS_zero, smul_zero]

lemma inner_upper_Psi (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (n : ℤ) (x : KSTPairL2) :
    ⟪kstPnUpper n, PsiMap ε x⟫_ℂ = star ⟪kstPnLower n, x⟫_ℂ := by
  rw [← PsiMap_lower ε n, PsiMap_inner ε hε]

lemma inner_lower_Psi (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (n : ℤ) (x : KSTPairL2) :
    ⟪kstPnLower n, PsiMap ε x⟫_ℂ = (ε : ℂ) * star ⟪kstPnUpper n, x⟫_ℂ := by
  have h1 := epsilon_sq ε hε
  have h : kstPnLower n = (ε : ℂ) • PsiMap ε (kstPnUpper n) := by
    rw [PsiMap_upper, smul_smul, h1, one_smul]
  calc ⟪kstPnLower n, PsiMap ε x⟫_ℂ
      = ⟪(ε : ℂ) • PsiMap ε (kstPnUpper n), PsiMap ε x⟫_ℂ := by rw [← h]
    _ = (ε : ℂ) * star ⟪kstPnUpper n, x⟫_ℂ := by
      rw [inner_smul_left, PsiMap_inner ε hε, Complex.conj_ofReal]

lemma PsiMap_Pn (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (n : ℤ) (x : KSTPairL2) :
    PsiMap ε (spectralPn n x) = spectralPn n (PsiMap ε x) := by
  rw [spectralPn_apply, spectralPn_apply, PsiMap_add, PsiMap_smul, PsiMap_smul,
    PsiMap_upper, PsiMap_lower, inner_upper_Psi ε hε, inner_lower_Psi ε hε]
  module


/-! ### Intertwining of the Q operator -/

lemma Q_true_coeff (φ : PhysicalPairLp) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (f : KSTPairL2) (k : ℤ) :
    spectralCoeff ((NlsGge.Atomic.KST006.qOperator φ n z hz f) true) k =
      ∑' m : ℤ, potentialCoeff φ true (k - m) *
        (complementaryResolventCoeff n z m * spectralCoeff (f false) m) :=
  NlsGge.Atomic.KST006.qOperator_upper_coeff φ n z hz f k

lemma Q_false_coeff (φ : PhysicalPairLp) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (f : KSTPairL2) (k : ℤ) :
    spectralCoeff ((NlsGge.Atomic.KST006.qOperator φ n z hz f) false) k =
      ∑' m : ℤ, potentialCoeff φ false (k - m) *
        (complementaryResolventCoeff n z (-m) * spectralCoeff (f true) m) :=
  NlsGge.Atomic.KST006.qOperator_lower_coeff φ n z hz f k

lemma PsiMap_Q (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hzb : star z ∈ spectralStrip n) (f : KSTPairL2) :
    PsiMap ε (NlsGge.Atomic.KST006.qOperator φ n z hz f) =
      NlsGge.Atomic.KST006.qOperator φ n (star z) hzb (PsiMap ε f) := by
  have hεε := epsilon_sq ε hε
  have hrelF : ∀ k, potentialCoeff φ false k = (ε : ℂ) * star (potentialCoeff φ true (-k)) :=
    potentialCoeff_false φ ε h
  have hrelT : ∀ k, star (potentialCoeff φ true k) = (ε : ℂ) * potentialCoeff φ false (-k) := by
    intro k
    rw [hrelF (-k), neg_neg, ← mul_assoc, hεε, one_mul]
  have hrelF' : ∀ k, star (potentialCoeff φ false k) = (ε : ℂ) * potentialCoeff φ true (-k) := by
    intro k
    rw [hrelF k, star_mul', star_star, star_epsilon, mul_comm]
  apply PiLp.ext
  intro b
  cases b
  · -- false component
    apply scalar_ext
    intro l
    rw [PsiMap_false, spectralCoeff_smul, spectralCoeff_star, Q_true_coeff φ n z hz f (-l),
      Q_false_coeff φ n (star z) hzb (PsiMap ε f) l]
    simp only [PsiMap_true, spectralCoeff_star]
    have hR : ∑' m : ℤ, potentialCoeff φ false (l - m) *
          (complementaryResolventCoeff n (star z) (-m) * star (spectralCoeff (f false) (-m))) =
        ∑' m : ℤ, potentialCoeff φ false (l + m) *
          (complementaryResolventCoeff n (star z) m * star (spectralCoeff (f false) m)) := by
      rw [← tsum_neg_reindex (fun m : ℤ => potentialCoeff φ false (l - m) *
          (complementaryResolventCoeff n (star z) (-m) * star (spectralCoeff (f false) (-m))))]
      refine tsum_congr (fun m => ?_)
      simp only [neg_neg, sub_neg_eq_add]
    rw [hR, star_tsum_int, ← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    simp only [star_mul']
    have e : -(-l - m) = l + m := by ring
    rw [hrelT, e, star_compl]
    linear_combination (potentialCoeff φ false (l + m) *
      (complementaryResolventCoeff n (star z) m * star (spectralCoeff (f false) m))) * hεε
  · -- true component
    apply scalar_ext
    intro l
    rw [PsiMap_true, spectralCoeff_star, Q_false_coeff φ n z hz f (-l),
      Q_true_coeff φ n (star z) hzb (PsiMap ε f) l]
    simp only [PsiMap_false, spectralCoeff_smul, spectralCoeff_star]
    have hR : ∑' m : ℤ, potentialCoeff φ true (l - m) *
          (complementaryResolventCoeff n (star z) m *
            ((ε : ℂ) * star (spectralCoeff (f true) (-m)))) =
        ∑' m : ℤ, potentialCoeff φ true (l + m) *
          (complementaryResolventCoeff n (star z) (-m) *
            ((ε : ℂ) * star (spectralCoeff (f true) m))) := by
      rw [← tsum_neg_reindex (fun m : ℤ => potentialCoeff φ true (l - m) *
          (complementaryResolventCoeff n (star z) m *
            ((ε : ℂ) * star (spectralCoeff (f true) (-m)))))]
      refine tsum_congr (fun m => ?_)
      simp only [neg_neg, sub_neg_eq_add]
    rw [hR, star_tsum_int]
    refine tsum_congr (fun m => ?_)
    simp only [star_mul']
    have e : -(-l - m) = l + m := by ring
    rw [hrelF', e, star_compl]
    ring


/-! ### The potential on P_n, inverse transport, reduced matrix -/

lemma potentialOnPn_true (φ : PhysicalPairLp) (n : ℤ) (u : KSTPairL2) :
    NlsGge.Atomic.KST012.potentialOnPn φ n u true =
      ⟪kstPnLower n, u⟫_ℂ • fourierMultiplier n (naturalPhysicalCoverL2 (φ true)) := by
  simp [NlsGge.Atomic.KST012.potentialOnPn, InnerProductSpace.rankOne_apply]

lemma potentialOnPn_false (φ : PhysicalPairLp) (n : ℤ) (u : KSTPairL2) :
    NlsGge.Atomic.KST012.potentialOnPn φ n u false =
      ⟪kstPnUpper n, u⟫_ℂ • fourierMultiplier (-n) (naturalPhysicalCoverL2 (φ false)) := by
  simp [NlsGge.Atomic.KST012.potentialOnPn, InnerProductSpace.rankOne_apply]

lemma PsiMap_potential (φ : PhysicalPairLp) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h : φ false = (ε : ℂ) • star (φ true)) (n : ℤ) (u : KSTPairL2) :
    PsiMap ε (NlsGge.Atomic.KST012.potentialOnPn φ n u) =
      NlsGge.Atomic.KST012.potentialOnPn φ n (PsiMap ε u) := by
  have hεε := epsilon_sq ε hε
  have hcf : naturalPhysicalCoverL2 (φ false) =
      (ε : ℂ) • star (naturalPhysicalCoverL2 (φ true)) := by
    rw [h, map_smul, cover_star]
  have hst : star (naturalPhysicalCoverL2 (φ false)) =
      (ε : ℂ) • naturalPhysicalCoverL2 (φ true) := by
    rw [hcf, starS_smul, starS_star, star_epsilon]
  have hst' : star (naturalPhysicalCoverL2 (φ true)) =
      (ε : ℂ) • naturalPhysicalCoverL2 (φ false) := by
    rw [hcf, smul_smul, hεε, one_smul]
  apply PiLp.ext
  intro b
  cases b
  · rw [PsiMap_false, potentialOnPn_true, starS_smul, starS_mult, hst', map_smul,
      potentialOnPn_false, inner_upper_Psi ε hε]
    have key : ∀ (X : ℂ) (M : SpectralScalarL2),
        (ε : ℂ) • (X • ((ε : ℂ) • M)) = X • M := by
      intro X M
      rw [smul_comm X (ε : ℂ) M, smul_smul, hεε, one_smul]
    exact key _ _
  · rw [PsiMap_true, potentialOnPn_false, starS_smul, starS_mult, hst, neg_neg, map_smul,
      potentialOnPn_true, inner_lower_Psi ε hε]
    module

end NlsGge.DM009Psi

/- DM-009 S2 + S8 (proof development, 2026-10-31). Totalized real-form intertwining of the KST local
   objects with the conjugate-linear isometry Psi := PsiMap 1, and the off-diagonal identity
   `c φ n w = star (b φ n (star w))` for ALL n and ALL w (no |n| restriction, no strip
   restriction on w), for every potential with `φ false = star (φ true)`.
   Depends on: DM009_S1 transport (`NlsGge.DM009Transport`, proof development PRODUCTION02) and
   DM009_S2_HELPERS (`NlsGge.DM009Psi`, KST015 helpers re-proved locally).
   Totalization: `Ring.inverse` is transported by the S1 lemma, which needs no unit hypothesis.
   Uses ε = 1 throughout (Psi is an involution only for ε = 1). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.DM009Psi

open MeasureTheory NlsGge.Schur NlsGge.Analysis NlsGge.Pilot
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
  NlsGge.Atomic.KST006 NlsGge.Atomic.KST007 NlsGge.Atomic.KST012
  NlsGge.Atomic.KST016
open scoped InnerProductSpace

/-! ### Basic facts at eps = 1 -/

theorem center_star (n : ℤ) :
    star (NlsGge.ThirdConsultation.KST.center n) = NlsGge.ThirdConsultation.KST.center n := by
  simp [NlsGge.ThirdConsultation.KST.center, Complex.star_def]

theorem psi1_false (f : KSTPairL2) : PsiMap 1 f false = star (f true) := by
  rw [PsiMap_false]
  simp

theorem psi1_true (f : KSTPairL2) : PsiMap 1 f true = star (f false) :=
  PsiMap_true 1 f

theorem coeff_scalarCM (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (upper : Bool)
    (g : SpectralScalarL2) (m : ℤ) :
    spectralCoeff (scalarComplementaryMultiplier n z hz upper g) m =
      complementaryResolventCoeff n z (sourceModeIndex upper m) * spectralCoeff g m :=
  scalarComplementaryMultiplier_repr n z hz upper g m

/-- Psi intertwines the complementary multiplier, the parameter being conjugated. -/
theorem psi1_compMult (n : ℤ) (z z' : ℂ) (hz : z ∈ spectralStrip n) (hz' : z' ∈ spectralStrip n)
    (hzz : star z = z') (f : KSTPairL2) :
    PsiMap 1 (complementaryMultiplier n z hz f) =
      complementaryMultiplier n z' hz' (PsiMap 1 f) := by
  apply PiLp.ext
  intro b
  cases b
  · rw [psi1_false, compMult_component, compMult_component, psi1_false]
    apply scalar_ext
    intro l
    rw [spectralCoeff_star, coeff_scalarCM n z hz true, coeff_scalarCM n z' hz' false,
      spectralCoeff_star]
    simp [NlsGge.Atomic.KST004.sourceModeIndex, star_mul', star_compl, hzz]
  · rw [psi1_true, compMult_component, compMult_component, psi1_true]
    apply scalar_ext
    intro l
    rw [spectralCoeff_star, coeff_scalarCM n z hz false, coeff_scalarCM n z' hz' true,
      spectralCoeff_star]
    simp [NlsGge.Atomic.KST004.sourceModeIndex, star_mul', star_compl, hzz]

/-! ### The free factor and the totalized inverse -/

/-- `localFreeFactor n z₀ hz₀ (w, φ) = 1 - freeB n z₀ hz₀ w`. -/
def freeB (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) (w : ℂ) : KSTPairL2 →L[ℂ] KSTPairL2 :=
  (z₀ - w) • complementaryMultiplier n z₀ hz₀

theorem localFreeFactor_eq_sub (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) (w : ℂ)
    (φ : Potential) :
    localFreeFactor n z₀ hz₀ (w, φ) = 1 - freeB n z₀ hz₀ w := by
  unfold localFreeFactor freeB
  dsimp only
  module

theorem psi1_freeB (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) (hreal : star z₀ = z₀)
    (w : ℂ) (x : KSTPairL2) :
    freeB n z₀ hz₀ (star w) (PsiMap 1 x) = PsiMap 1 (freeB n z₀ hz₀ w x) := by
  unfold freeB
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, PsiMap_smul,
    psi1_compMult n z₀ z₀ hz₀ hz₀ hreal x, star_sub, hreal]

/-! ### Psi as a conjugate-linear isometric involution (eps = 1) -/

theorem psi1_norm (x : KSTPairL2) : ‖PsiMap 1 x‖ = ‖x‖ := by
  have hε : (1:ℝ) = 1 ∨ (1:ℝ) = -1 := Or.inl rfl
  have h1 := PsiMap_inner 1 hε x x
  have e : ∀ y : KSTPairL2, inner ℂ y y = ((‖y‖ : ℝ) : ℂ) ^ 2 :=
    fun y => inner_self_eq_norm_sq_to_K (𝕜 := ℂ) y
  have h2 : ((‖PsiMap 1 x‖ : ℝ) : ℂ) ^ 2 = ((‖x‖ : ℝ) : ℂ) ^ 2 := by
    rw [← e (PsiMap 1 x), ← e x, h1, e x]
    simp
  have h3 : ‖PsiMap 1 x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

theorem psi1_continuous : Continuous (PsiMap 1) := by
  refine Isometry.continuous (Isometry.of_dist_eq fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← PsiMap_sub 1, psi1_norm]

theorem psi1_invol (x : KSTPairL2) : PsiMap 1 (PsiMap 1 x) = x := by
  apply PiLp.ext
  intro b
  cases b
  · rw [psi1_false, psi1_true, star_star]
  · rw [psi1_true, psi1_false, star_star]

/-- Psi as a `ConjBij` (S1), with itself as the two-sided inverse. -/
def psi1Bij : NlsGge.DM009Transport.ConjBij KSTPairL2 where
  f := PsiMap 1
  g := PsiMap 1
  f_add := PsiMap_add 1
  f_smul := PsiMap_smul 1
  g_add := PsiMap_add 1
  g_smul := PsiMap_smul 1
  f_cont := psi1_continuous
  g_cont := psi1_continuous
  fg := psi1_invol
  gf := psi1_invol

theorem psi1_freeInv (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n) (hreal : star z₀ = z₀)
    (w : ℂ) (x : KSTPairL2) :
    PsiMap 1 (Ring.inverse (1 - freeB n z₀ hz₀ w) x) =
      Ring.inverse (1 - freeB n z₀ hz₀ (star w)) (PsiMap 1 x) :=
  (NlsGge.DM009Transport.transport_inverse psi1Bij (freeB n z₀ hz₀ w) (freeB n z₀ hz₀ (star w))
    (fun y => psi1_freeB n z₀ hz₀ hreal w y) x).symm

/-! ### Intertwining of localQ and localCorrection (centre z₀ = center n, real) -/

theorem psi1_qOperator (φ : Potential) (hφ : φ false = star (φ true)) (n : ℤ)
    (z z' : ℂ) (hz : z ∈ spectralStrip n) (hz' : z' ∈ spectralStrip n) (hzz : star z = z')
    (f : KSTPairL2) :
    PsiMap 1 (qOperator φ n z hz f) = qOperator φ n z' hz' (PsiMap 1 f) := by
  subst hzz
  exact PsiMap_Q φ 1 (Or.inl rfl) (by simpa using hφ) n z hz hz' f

theorem psi1_localQ (φ : Potential) (hφ : φ false = star (φ true)) (n : ℤ) (w : ℂ)
    (x : KSTPairL2) :
    PsiMap 1 (localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) x) =
      localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ) (PsiMap 1 x) := by
  unfold localQ
  simp only [ContinuousLinearMap.mul_apply, qParameter_apply]
  rw [localFreeFactor_eq_sub, localFreeFactor_eq_sub,
    psi1_qOperator φ hφ n _ _ (NlsGge.ThirdConsultation.KST.center_mem_strip n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (center_star n),
    psi1_freeInv n _ (NlsGge.ThirdConsultation.KST.center_mem_strip n) (center_star n)]

theorem psi1_localQ_inv (φ : Potential) (hφ : φ false = star (φ true)) (n : ℤ) (w : ℂ)
    (y : KSTPairL2) :
    PsiMap 1 (Ring.inverse (1 - localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ)) y) =
      Ring.inverse (1 - localQ n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ)) (PsiMap 1 y) :=
  (NlsGge.DM009Transport.transport_inverse psi1Bij
    (localQ n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ))
    (localQ n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ))
    (fun u => (psi1_localQ φ hφ n w u).symm) y).symm

theorem psi1_potentialParameter (φ : Potential) (hφ : φ false = star (φ true)) (n : ℤ)
    (x : KSTPairL2) :
    PsiMap 1 (potentialParameter n φ x) = potentialParameter n φ (PsiMap 1 x) :=
  PsiMap_potential φ 1 (Or.inl rfl) (by simpa using hφ) n x

theorem psi1_localCorrection (φ : Potential) (hφ : φ false = star (φ true)) (n : ℤ) (w : ℂ)
    (x : KSTPairL2) :
    PsiMap 1 (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) x) =
      localCorrection n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (star w, φ) (PsiMap 1 x) := by
  unfold localCorrection
  simp only [ContinuousLinearMap.mul_apply]
  rw [PsiMap_Pn 1 (Or.inl rfl), psi1_localQ_inv φ hφ n w, psi1_potentialParameter φ hφ n x]

/-! ### Off-diagonal real form, S8 -/

theorem c_formula (φ : Potential) (n : ℤ) (w : ℂ) :
    NlsGge.ThirdConsultation.KST.c φ n w =
      inner ℂ (kstPnUpper n) (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) (kstPnLower n)) :=
  rfl

theorem b_formula (φ : Potential) (n : ℤ) (w : ℂ) :
    NlsGge.ThirdConsultation.KST.b φ n w =
      inner ℂ (kstPnLower n) (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) (kstPnUpper n)) :=
  rfl

/-- S8: the off-diagonal real-form identity, all `n`, all `w`, totalized. -/
theorem c_eq_conj_b (φ : Potential) (hφ : φ false = star (φ true)) (n : ℤ) (w : ℂ) :
    NlsGge.ThirdConsultation.KST.c φ n w =
      star (NlsGge.ThirdConsultation.KST.b φ n (star w)) := by
  have hε : (1:ℝ) = 1 ∨ (1:ℝ) = -1 := Or.inl rfl
  have h1 := PsiMap_inner 1 hε (kstPnUpper n)
    (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) (kstPnLower n))
  rw [PsiMap_upper, psi1_localCorrection φ hφ n w (kstPnLower n), PsiMap_lower] at h1
  simp only [Complex.ofReal_one, one_smul] at h1
  rw [c_formula, b_formula, h1, star_star]

end NlsGge.DM009Psi

/- DM-009 S9, CONDITIONAL form (proof development, 2026-10-31). The diagonal identity S7 is an explicit
   hypothesis `hdiag` (for one potential and one label n, all w); nothing else is assumed.
   Proved: `a φ n (star w) = star (a φ n w)` from `hdiag`, via Psi (ε = 1) and the S8 machinery.
   `diagU φ n w := ⟪e_U, C(w,φ) e_U⟫` is the (2,2) entry; S7 (`hdiag`) is open. Namespace
   NlsGge.DM009Psi (requires DM009_S8_PRODUCTION02 and DM009_S2_HELPERS). -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.DM009Psi

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
  NlsGge.Atomic.KST016
open scoped InnerProductSpace

/-- The (2,2) correction entry `⟪e_U, C(w,φ) e_U⟫` at the centre `center n`. -/
def diagU (φ : Potential) (n : ℤ) (w : ℂ) : ℂ :=
  inner ℂ (kstPnUpper n) (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
    (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) (kstPnUpper n))

theorem a_formula (φ : Potential) (n : ℤ) (w : ℂ) :
    NlsGge.ThirdConsultation.KST.a φ n w =
      inner ℂ (kstPnLower n) (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
        (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) (kstPnLower n)) :=
  rfl

/-- Psi identity: `a φ n w = star (diagU φ n (star w))`, for every w (no hypothesis). -/
theorem a_conj_identity (φ : Potential) (hφ : φ false = star (φ true)) (n : ℤ) (w : ℂ) :
    NlsGge.ThirdConsultation.KST.a φ n w = star (diagU φ n (star w)) := by
  have hε : (1:ℝ) = 1 ∨ (1:ℝ) = -1 := Or.inl rfl
  have h1 := PsiMap_inner 1 hε (kstPnLower n)
    (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) (kstPnLower n))
  rw [psi1_localCorrection φ hφ n w (kstPnLower n), PsiMap_lower] at h1
  rw [a_formula, diagU, h1, star_star]

/-- S9 (conditional on the diagonal identity `hdiag`, which is the open input S7). -/
theorem a_eq_conj_a_of_diag (φ : Potential) (hφ : φ false = star (φ true)) (n : ℤ)
    (hdiag : ∀ w : ℂ, diagU φ n w = NlsGge.ThirdConsultation.KST.a φ n w) (w : ℂ) :
    NlsGge.ThirdConsultation.KST.a φ n (star w) =
      star (NlsGge.ThirdConsultation.KST.a φ n w) := by
  have h1 := a_conj_identity φ hφ n w
  rw [hdiag (star w)] at h1
  rw [h1, star_star]

end NlsGge.DM009Psi

/- DM-009 support S3 (proof development). Compactness of the KST Q-operator at any strip point, hence of
   `localQ` (in particular at the centre `center n`), by reduction to landed production facts:
   * `qBlock` is complex Hilbert--Schmidt: its matrix entries are dominated by those of the landed
     Hilbert--Schmidt `positiveBlock` (KST007 `qBlock_matrix_majorant`, `positiveBlock_matrix`);
   * HS implies compact: LIB023 `hs_columns_compact` (Fourier basis, summable squared columns);
   * `qOperator = scalarIn true ∘ qBlock true ∘ scalarOut false + scalarIn false ∘ qBlock false ∘
     scalarOut true` (off-diagonal channel structure via KST016 `qOperator_flips`);
   * `localQ = qOperator * Ring.inverse(freeFactor)`: totalized inverse is a CLM when a unit and 0
     otherwise, so compactness passes through.
   No new hypotheses. Statement in this file: `s3_localQ_center_isCompactOperator`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.DM009S3

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST006
open NlsGge.Atomic.KST007 NlsGge.Atomic.KST016 NlsGge.ThirdConsultation.KST
open NlsGge.Pilot NlsGge.Schur

/-- The Fourier basis of the scalar space, ascribed to `SpectralScalarL2` (as KST007 does). -/
def s3Basis : HilbertBasis ℤ ℂ SpectralScalarL2 := fourierBasis (T := (2 : ℝ))

theorem s3Basis_apply (j : ℤ) : s3Basis j = spectralBasis j :=
  congrFun (coe_fourierBasis (T := (2 : ℝ))) j

theorem s3_scalarIn_apply (b : Bool) (x : SpectralScalarL2) : scalarIn b x = PiLp.single 2 b x :=
  rfl

theorem s3_scalarOut_apply (b : Bool) (f : KSTPairL2) : scalarOut b f = f b :=
  rfl

/-- The scalar block `qBlock` is complex Hilbert--Schmidt (entrywise domination by the positive
block, whose energy is finite). -/
theorem s3_qBlock_isComplexHilbertSchmidt (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    IsComplexHilbertSchmidt (qBlock φ n z hz upper) := by
  have hP := positiveBlock_isComplexHilbertSchmidt φ n upper
  have hEP := complexHilbertSchmidtEnergy_eq_matrix (positiveBlock φ n upper)
    s3Basis s3Basis
  have hEQ := complexHilbertSchmidtEnergy_eq_matrix (qBlock φ n z hz upper)
    s3Basis s3Basis
  have he : complexHilbertSchmidtEnergy (qBlock φ n z hz upper) ≤
      complexHilbertSchmidtEnergy (positiveBlock φ n upper) := by
    rw [hEQ, hEP]
    apply ENNReal.tsum_le_tsum
    intro j
    apply ENNReal.tsum_le_tsum
    intro l
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    rw [← s3Basis.repr_apply_apply,
      ← s3Basis.repr_apply_apply]
    change ‖spectralCoeff (qBlock φ n z hz upper (s3Basis j)) l‖ ≤
      ‖spectralCoeff (positiveBlock φ n upper (s3Basis j)) l‖
    rw [s3Basis_apply, positiveBlock_matrix, Complex.norm_real, Real.norm_eq_abs]
    exact (qBlock_matrix_majorant φ n z hz upper l j).trans (le_abs_self _)
  unfold IsComplexHilbertSchmidt at hP ⊢
  exact ne_of_lt (lt_of_le_of_lt he (lt_top_iff_ne_top.mpr hP))

/-- Each scalar block is compact (Hilbert--Schmidt, via the landed LIB023 column criterion). -/
theorem s3_qBlock_isCompactOperator (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    IsCompactOperator (qBlock φ n z hz upper) :=
  NlsGge.Atomic.LIB023.hs_columns_compact s3Basis
    (qBlock φ n z hz upper)
    (summable_basis_of_isComplexHilbertSchmidt s3Basis
      (s3_qBlock_isComplexHilbertSchmidt φ n z hz upper))

/-- Output of the true component of `qOperator` is the `true` block applied to the false input. -/
theorem s3_qOperator_apply_true (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f : KSTPairL2) :
    NlsGge.Atomic.KST006.qOperator φ n z hz f true =
      qBlock φ n z hz true (scalarOut false f) := by
  have hsplit : f = scalarIn true (f true) + scalarIn false (f false) := by
    apply PiLp.ext
    intro c
    cases c <;> simp [s3_scalarIn_apply]
  have h1 : NlsGge.Atomic.KST006.qOperator φ n z hz (scalarIn true (f true)) true = 0 := by
    have hin : InChannel true (scalarIn true (f true)) := by
      intro c hc
      rw [s3_scalarIn_apply, PiLp.single_apply]
      cases c
      · simp
      · exact absurd rfl hc
    exact qOperator_flips φ n z hz true (scalarIn true (f true)) hin true (by decide)
  have key : NlsGge.Atomic.KST006.qOperator φ n z hz f =
      NlsGge.Atomic.KST006.qOperator φ n z hz (scalarIn true (f true)) +
        NlsGge.Atomic.KST006.qOperator φ n z hz (scalarIn false (f false)) := by
    conv_lhs => rw [hsplit]
    rw [map_add]
  rw [key, PiLp.add_apply, h1, zero_add]
  rfl

/-- Output of the false component of `qOperator` is the `false` block applied to the true input. -/
theorem s3_qOperator_apply_false (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f : KSTPairL2) :
    NlsGge.Atomic.KST006.qOperator φ n z hz f false =
      qBlock φ n z hz false (scalarOut true f) := by
  have hsplit : f = scalarIn true (f true) + scalarIn false (f false) := by
    apply PiLp.ext
    intro c
    cases c <;> simp [s3_scalarIn_apply]
  have h2 : NlsGge.Atomic.KST006.qOperator φ n z hz (scalarIn false (f false)) false = 0 := by
    have hin : InChannel false (scalarIn false (f false)) := by
      intro c hc
      rw [s3_scalarIn_apply, PiLp.single_apply]
      cases c
      · exact absurd rfl hc
      · simp
    exact qOperator_flips φ n z hz false (scalarIn false (f false)) hin false (by decide)
  have key : NlsGge.Atomic.KST006.qOperator φ n z hz f =
      NlsGge.Atomic.KST006.qOperator φ n z hz (scalarIn true (f true)) +
        NlsGge.Atomic.KST006.qOperator φ n z hz (scalarIn false (f false)) := by
    conv_lhs => rw [hsplit]
    rw [map_add]
  rw [key, PiLp.add_apply, h2, add_zero]
  rfl

/-- Off-diagonal block decomposition of the full Q-operator. -/
theorem s3_qOperator_eq_blocks (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
    (NlsGge.Atomic.KST006.qOperator φ n z hz : KSTPairL2 →L[ℂ] KSTPairL2) =
      (scalarIn true).comp ((qBlock φ n z hz true).comp (scalarOut false)) +
        (scalarIn false).comp ((qBlock φ n z hz false).comp (scalarOut true)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro c
  cases c
  · rw [s3_qOperator_apply_false]
    simp [s3_scalarIn_apply, s3_scalarOut_apply]
  · rw [s3_qOperator_apply_true]
    simp [s3_scalarIn_apply, s3_scalarOut_apply]

/-- The full Q-operator is compact at every point of the closed strip. -/
theorem s3_qOperator_isCompactOperator (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
    IsCompactOperator (NlsGge.Atomic.KST006.qOperator φ n z hz : KSTPairL2 →L[ℂ] KSTPairL2) := by
  rw [s3_qOperator_eq_blocks φ n z hz]
  have h1 : IsCompactOperator
      ⇑((scalarIn true).comp ((qBlock φ n z hz true).comp (scalarOut false))) :=
    ((s3_qBlock_isCompactOperator φ n z hz true).comp_clm (scalarOut false)).clm_comp
      (scalarIn true)
  have h2 : IsCompactOperator
      ⇑((scalarIn false).comp ((qBlock φ n z hz false).comp (scalarOut true))) :=
    ((s3_qBlock_isCompactOperator φ n z hz false).comp_clm (scalarOut true)).clm_comp
      (scalarIn false)
  exact h1.add h2

/-- `localQ` is compact at every point of the strip and every potential (the totalized inverse
is either a bounded inverse or zero). -/
theorem s3_localQ_isCompactOperator (n : ℤ) (z₀ : ℂ) (hz₀ : z₀ ∈ spectralStrip n)
    (w : ℂ) (φ : PhysicalPairLp) :
    IsCompactOperator (localQ n z₀ hz₀ (w, φ)) := by
  unfold localQ
  rw [qParameter_apply]
  by_cases hu : IsUnit (localFreeFactor n z₀ hz₀ (w, φ))
  · rw [← hu.unit_spec, Ring.inverse_unit, ContinuousLinearMap.mul_def]
    exact (s3_qOperator_isCompactOperator φ n z₀ hz₀).comp_clm
      (((hu.unit⁻¹ : (KSTPairL2 →L[ℂ] KSTPairL2)ˣ) : KSTPairL2 →L[ℂ] KSTPairL2))
  · rw [Ring.inverse_non_unit _ hu, mul_zero]
    exact isCompactOperator_zero

/-- The centre specialisation `localQ n (center n) (center_mem_strip n) (w, φ)`. -/
theorem s3_localQ_center_isCompactOperator (n : ℤ) (w : ℂ) (φ : PhysicalPairLp) :
    IsCompactOperator (localQ n (center n) (center_mem_strip n) (w, φ)) :=
  s3_localQ_isCompactOperator n (center n) (center_mem_strip n) w φ

end NlsGge.DM009S3

/- DM-009 support S7 analytic step (proof development). Contains the S4 finiteness block INLINED
   BYTE-IDENTICALLY (except the hoisted import) from proof development DM009_S4_PRODUCTION01.lean.txt,
   sha256 59b79b44bab88ebcb606926d4d8f48af2a682eb407a24fe7f775ce33cb92a1d9, because that owner is not
   landed. Root must dedupe to the single owner once S4 lands. -/
/- DM-009 support S4 (proof development). Mathlib-level, no KST/DM dependency.
   For a compact operator `T` on a normed space over `ℂ`, the eigenvalues with `ε ≤ ‖μ‖`
   (ε > 0) form a finite set (`eigen_finite_outside`; no completeness used). With completeness,
   the nonzero spectral values with `ε ≤ ‖μ‖` form a finite set (`spectrum_finite_outside`), and
   `compact_finite_bounded_nonunit` is the DM-009 MAP form
   `{t | ‖t‖ ≤ r ∧ ¬IsUnit (1 - t • A)}.Finite`.
   Proof of the eigenvalue step: eigenvectors `v i` of distinct eigenvalues are linearly
   independent (Mathlib `Module.End.eigenvectors_linearIndependent'`). If the eigenvalue set
   were infinite, Riesz's lemma inside the finite-dimensional spans `V n = span{v i | i < n}`
   gives unit vectors `x n ∈ V (n+1)` at distance `≥ 1/2` from `V n`; then for `m < n`,
   `‖T (x n) - T (x m)‖ ≥ ‖μ n‖ / 2 ≥ ε / 2`, contradicting the convergent subsequence that
   compactness of `T` gives on the image of the closed unit ball. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.DM009Riesz

open Module Metric Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Riesz's lemma inside a subspace `G`: if `F ≤ G` is closed in `E` and `G` is not contained in
`F`, there is a unit vector `x ∈ G` at distance at least `1/2` from every `y ∈ F`. -/
theorem exists_riesz_pair {F G : Submodule ℂ E} (hFG : F ≤ G) (hFc : IsClosed (F : Set E))
    (hne : ∃ x ∈ G, x ∉ F) :
    ∃ x ∈ G, ‖x‖ = 1 ∧ ∀ y ∈ F, (1 / 2 : ℝ) ≤ ‖x - y‖ := by
  let F' : Submodule ℂ G := F.comap G.subtype
  have hF'c : IsClosed (F' : Set G) := hFc.preimage continuous_subtype_val
  have hF' : ∃ x : G, x ∉ F' := by
    obtain ⟨x, hxG, hxF⟩ := hne
    exact ⟨⟨x, hxG⟩, hxF⟩
  obtain ⟨x₀, -, hx₀1, hx₀⟩ := riesz_lemma_of_lt_one hF'c hF' (r := 1 / 2) (by norm_num)
  refine ⟨(x₀ : E), x₀.2, ?_, ?_⟩
  · rw [Submodule.norm_coe, hx₀1]
  · intro y hy
    have hyG : y ∈ G := hFG hy
    have h := hx₀ ⟨y, hyG⟩ (by simpa [F', Submodule.mem_comap] using hy)
    show (1 / 2 : ℝ) ≤ ‖(x₀ : E) - y‖
    exact h

/-- The span of the first `n` enumerated vectors `v 0, …, v (n-1)`. -/
def enumSpan (v : ℕ → E) (n : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (v '' Set.Iio n)

theorem enumSpan_mono (v : ℕ → E) {m n : ℕ} (h : m ≤ n) : enumSpan v m ≤ enumSpan v n :=
  Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

theorem mem_enumSpan_succ (v : ℕ → E) (n : ℕ) : v n ∈ enumSpan v (n + 1) :=
  Submodule.subset_span ⟨n, Set.mem_Iio.2 (Nat.lt_succ_self n), rfl⟩

theorem finiteDimensional_enumSpan (v : ℕ → E) (n : ℕ) : FiniteDimensional ℂ (enumSpan v n) :=
  FiniteDimensional.span_of_finite (K := ℂ) ((Set.finite_Iio n).image v)

theorem isClosed_enumSpan (v : ℕ → E) (n : ℕ) : IsClosed (enumSpan v n : Set E) := by
  have := finiteDimensional_enumSpan v n
  exact Submodule.closed_of_finiteDimensional _

/-- `T` maps each enumerated span into itself, because the `v i` are eigenvectors. -/
theorem clm_mem_enumSpan (T : E →L[ℂ] E) (v : ℕ → E) (μ : ℕ → ℂ)
    (hv : ∀ i, T (v i) = μ i • v i) (k : ℕ) : ∀ x ∈ enumSpan v k, T x ∈ enumSpan v k := by
  intro x hx
  unfold enumSpan at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [hv i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ hy

/-- `(T - μ n)` maps `enumSpan v (n+1)` into `enumSpan v n`. -/
theorem sub_smul_mem_enumSpan (T : E →L[ℂ] E) (v : ℕ → E) (μ : ℕ → ℂ)
    (hv : ∀ i, T (v i) = μ i • v i) (n : ℕ) :
    ∀ x ∈ enumSpan v (n + 1), T x - μ n • x ∈ enumSpan v n := by
  intro x hx
  unfold enumSpan at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [hv i]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 (Set.mem_Iio.1 hi)) with h | h
    · rw [← sub_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Set.mem_Iio.2 h, rfl⟩)
    · subst h
      simp
  | zero => simp
  | add y z _ _ hy hz =>
    have e : T (y + z) - μ n • (y + z) = (T y - μ n • y) + (T z - μ n • z) := by
      rw [map_add, smul_add]
      abel
    rw [e]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have e : T (c • y) - μ n • (c • y) = c • (T y - μ n • y) := by
      rw [map_smul, smul_sub, smul_comm (μ n) c y]
    rw [e]
    exact Submodule.smul_mem _ _ hy

/-- Riesz estimate: for `x ∈ enumSpan v (n+1)` at distance `≥ 1/2` from `enumSpan v n`, and any
`w ∈ enumSpan v n`, we have `‖μ n‖ / 2 ≤ ‖T x - w‖`. -/
theorem key_bound (T : E →L[ℂ] E) (v : ℕ → E) (μ : ℕ → ℂ) (hv : ∀ i, T (v i) = μ i • v i)
    (n : ℕ) (hμ : μ n ≠ 0) (x : E) (hx : x ∈ enumSpan v (n + 1))
    (hfar : ∀ y ∈ enumSpan v n, (1 / 2 : ℝ) ≤ ‖x - y‖) (w : E) (hw : w ∈ enumSpan v n) :
    ‖μ n‖ / 2 ≤ ‖T x - w‖ := by
  have ha : T x - μ n • x ∈ enumSpan v n := sub_smul_mem_enumSpan T v μ hv n x hx
  have hq : (μ n)⁻¹ • (w - (T x - μ n • x)) ∈ enumSpan v n :=
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hw ha)
  have heq : T x - w = μ n • (x - (μ n)⁻¹ • (w - (T x - μ n • x))) := by
    rw [smul_sub, smul_inv_smul₀ hμ]
    abel
  rw [heq, norm_smul]
  have h2 := mul_le_mul_of_nonneg_left (hfar _ hq) (norm_nonneg (μ n))
  linarith

/-- Eigenvalues of a compact operator on a normed `ℂ`-space with modulus at least `ε > 0` form
a finite set. -/
theorem eigen_finite_outside (T : E →L[ℂ] E) (hT : IsCompactOperator T) (ε : ℝ) (hε : 0 < ε) :
    {μ : ℂ | Module.End.HasEigenvalue (T : Module.End ℂ E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  by_contra hinf
  have hSinf : Set.Infinite {μ : ℂ | Module.End.HasEigenvalue (T : Module.End ℂ E) μ ∧ ε ≤ ‖μ‖} := hinf
  obtain ⟨g, hg_inj, hg_mem⟩ : ∃ g : ℕ → ℂ, Function.Injective g ∧
      ∀ n, Module.End.HasEigenvalue (T : Module.End ℂ E) (g n) ∧ ε ≤ ‖g n‖ :=
    ⟨fun n => ((hSinf.natEmbedding _ n :
        {μ : ℂ | Module.End.HasEigenvalue (T : Module.End ℂ E) μ ∧ ε ≤ ‖μ‖}) : ℂ),
      Subtype.val_injective.comp (hSinf.natEmbedding _).injective,
      fun n => (hSinf.natEmbedding _ n).2⟩
  have hg_ne : ∀ n, g n ≠ 0 := fun n h => by
    have h' := (hg_mem n).2
    rw [h, norm_zero] at h'
    linarith
  choose v hv using fun n => (hg_mem n).1.exists_hasEigenvector
  have hvT : ∀ i, T (v i) = g i • v i := fun i => by
    have h := (hv i).apply_eq_smul
    simpa using h
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (T : Module.End ℂ E) g hg_inj v hv
  have hnot : ∀ n, v n ∉ enumSpan v n := fun n =>
    hli.notMem_span_image (s := Set.Iio n) (x := n) (by simp)
  have hfar : ∀ n, ∃ x ∈ enumSpan v (n + 1), ‖x‖ = 1 ∧
      ∀ y ∈ enumSpan v n, (1 / 2 : ℝ) ≤ ‖x - y‖ := fun n =>
    exists_riesz_pair (enumSpan_mono v (Nat.le_succ n)) (isClosed_enumSpan v n)
      ⟨v n, mem_enumSpan_succ v n, hnot n⟩
  choose x hxmem hxnorm hxfar using hfar
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun n => T (x n))
    (fun n => hK' ⟨x n, mem_closedBall_zero_iff.2 (le_of_eq (hxnorm n)), rfl⟩)
  have hcau : CauchySeq (fun n => T (x (φ n))) := hlim.cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hcau (ε / 2) (by positivity)
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  have hmem : T (x (φ N)) ∈ enumSpan v (φ (N + 1)) :=
    enumSpan_mono v (Nat.succ_le_of_lt hlt)
      (clm_mem_enumSpan T v g hvT (φ N + 1) (x (φ N)) (hxmem (φ N)))
  have hkey := key_bound T v g hvT (φ (N + 1)) (hg_ne _) (x (φ (N + 1))) (hxmem _)
    (hxfar _) (T (x (φ N))) hmem
  have hdist : ‖T (x (φ (N + 1))) - T (x (φ N))‖ < ε / 2 := by
    have := hN (N + 1) (by omega)
    rwa [dist_eq_norm] at this
  have hgε := (hg_mem (φ (N + 1))).2
  linarith

/-- Spectral form: the nonzero spectral values of a compact operator on a complete space with
modulus at least `ε > 0` form a finite set. -/
theorem spectrum_finite_outside [CompleteSpace E] (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (ε : ℝ) (hε : 0 < ε) :
    {μ : ℂ | μ ∈ spectrum ℂ T ∧ μ ≠ 0 ∧ ε ≤ ‖μ‖}.Finite := by
  refine (eigen_finite_outside T hT ε hε).subset ?_
  rintro μ ⟨hsp, hne, hle⟩
  exact ⟨(IsCompactOperator.hasEigenvalue_iff_mem_spectrum hT hne).2 hsp, hle⟩

/-- DM-009 MAP form (S4): for a compact operator `A` on a complete space and any radius `r`, the
set of `t` with `‖t‖ ≤ r` at which `1 - t • A` is not invertible is finite. -/
theorem compact_finite_bounded_nonunit [CompleteSpace E] (A : E →L[ℂ] E)
    (hA : IsCompactOperator A) (r : ℝ) :
    {t : ℂ | ‖t‖ ≤ r ∧ ¬ IsUnit (1 - t • A)}.Finite := by
  rcases le_or_gt r 0 with hr | hr
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro t ⟨ht, hnu⟩
    have ht0 : t = 0 := norm_le_zero_iff.1 (ht.trans hr)
    subst ht0
    simp at hnu
  · have hfin := spectrum_finite_outside A hA (1 / r) (by positivity)
    refine Set.Finite.subset (hfin.image (fun μ : ℂ => μ⁻¹)) ?_
    rintro t ⟨ht, hnu⟩
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hnu (by simp)
    refine ⟨t⁻¹, ⟨?_, inv_ne_zero ht0, ?_⟩, inv_inv t⟩
    · rw [spectrum.mem_iff]
      intro hu
      apply hnu
      have e : (1 : E →L[ℂ] E) - t • A = t • (algebraMap ℂ (E →L[ℂ] E) t⁻¹ - A) := by
        rw [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, mul_inv_cancel₀ ht0, one_smul]
      have h2 : IsUnit ((Units.mk0 t ht0 : ℂˣ) • (algebraMap ℂ (E →L[ℂ] E) t⁻¹ - A)) :=
        (isUnit_smul_iff _ _).2 hu
      rw [Units.smul_def, Units.val_mk0] at h2
      rw [e]
      exact h2
    · rw [norm_inv, one_div]
      exact inv_anti₀ (norm_pos_iff.2 ht0) ht

end NlsGge.DM009Riesz

namespace NlsGge.DM009Ident

open Filter Topology

/-! S7 analytic step (proof development). For a compact operator `A` on a complete complex normed space
and a continuous linear functional `Ψ` on `E →L E`, if `t ↦ t * Ψ (Ring.inverse (1 - t • A))`
vanishes near `0`, it vanishes for every `t ∈ ℂ` (identity theorem on `ℂ \ S`, `S` the nonunit
scalars; `Ring.inverse = 0` on `S`). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem nonunit_set_countable (A : E →L[ℂ] E) (hA : IsCompactOperator A) :
    {t : ℂ | ¬ IsUnit (1 - t • A)}.Countable := by
  have h : {t : ℂ | ¬ IsUnit (1 - t • A)} ⊆
      ⋃ n : ℕ, {t : ℂ | ‖t‖ ≤ (n : ℝ) ∧ ¬ IsUnit (1 - t • A)} := by
    intro t ht
    exact Set.mem_iUnion.2 ⟨⌈‖t‖⌉₊, Nat.le_ceil _, ht⟩
  refine Set.Countable.mono h (Set.countable_iUnion fun n => ?_)
  exact (NlsGge.DM009Riesz.compact_finite_bounded_nonunit A hA (n : ℝ)).countable

theorem unit_set_isOpen (A : E →L[ℂ] E) : IsOpen {t : ℂ | IsUnit (1 - t • A)} := by
  have hc : Continuous fun t : ℂ => (1 : E →L[ℂ] E) - t • A := by fun_prop
  exact Units.isOpen.preimage hc

theorem inverse_analyticAt (A : E →L[ℂ] E) (t₀ : ℂ) (hu : IsUnit (1 - t₀ • A)) :
    AnalyticAt ℂ (fun t : ℂ => Ring.inverse (1 - t • A)) t₀ := by
  have hg : AnalyticAt ℂ (fun t : ℂ => (1 : E →L[ℂ] E) - t • A) t₀ :=
    analyticAt_const.sub (analyticAt_id.smul analyticAt_const)
  have hc : AnalyticAt ℂ (Ring.inverse : (E →L[ℂ] E) → (E →L[ℂ] E))
      ((fun t : ℂ => (1 : E →L[ℂ] E) - t • A) t₀) := by
    have h := analyticAt_inverse (𝕜 := ℂ) hu.unit
    simpa using h
  exact AnalyticAt.comp (f := fun t : ℂ => (1 : E →L[ℂ] E) - t • A)
    (g := Ring.inverse) (x := t₀) hc hg

/-- The identity-theorem step on `ℂ \ S`. -/
theorem vanish_of_near_zero (A : E →L[ℂ] E) (hA : IsCompactOperator A)
    (Ψ : (E →L[ℂ] E) →L[ℂ] ℂ)
    (h0 : ∀ᶠ t in 𝓝 (0 : ℂ), t * Ψ (Ring.inverse (1 - t • A)) = 0) (t : ℂ) :
    t * Ψ (Ring.inverse (1 - t • A)) = 0 := by
  set S : Set ℂ := {s : ℂ | ¬ IsUnit (1 - s • A)} with hS
  have hSc : S.Countable := nonunit_set_countable A hA
  have hpc : IsPathConnected Sᶜ :=
    hSc.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have hUeq : Sᶜ = {s : ℂ | IsUnit (1 - s • A)} := by
    ext s
    simp [hS]
  have hanal : AnalyticOnNhd ℂ (fun s : ℂ => s * Ψ (Ring.inverse (1 - s • A))) Sᶜ := by
    intro s hs
    have hu : IsUnit (1 - s • A) := by
      rw [hUeq] at hs
      exact hs
    exact analyticAt_id.mul ((Ψ.analyticAt _).comp (inverse_analyticAt A s hu))
  have h0mem : (0 : ℂ) ∈ Sᶜ := by
    rw [hUeq]
    simp
  by_cases ht : t ∈ S
  · have hnu : ¬ IsUnit (1 - t • A) := ht
    simp [Ring.inverse_non_unit _ hnu]
  · have hmem : t ∈ Sᶜ := ht
    have hEq := hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hpc.isConnected.isPreconnected h0mem h0
    exact hEq hmem

end NlsGge.DM009Ident

/- DM-009 S6-concrete (proof development, 2026-10-31). Path reversal for the fixed-w local resolvent,
   formalized at the level of Fourier coordinates, without any unbounded operator.
   Notation: `pcf x c l` is the l-th Fourier coordinate of component c of x : KSTPairL2;
   `pB x y = sum_c sum_l pcf x c l * pcf y c l` (bilinear, NO conjugation);
   `pRefl x` has coordinates `pcf (pRefl x) c l = pcf x (!c) (-l)` (swap components, reflect mode);
   `pD = M0 * Ring.inverse(F(w))` is the diagonal operator with weights `peta c l` (R-invariant,
   square-summable), and `pA = localQ`.
   Key transposition identity (`pP`, Fubini on absolutely summable double sums):
     `B (D v) (A y) = B (D (A (R v))) (R y)`   [A = K D, K the bare convolution kernel].
   Claim_j (`pClaim`): `B x (D (A^j y)) = B (D (A^j (R x))) (R y)` for all x y, by induction.
   Main result (`preversal`): for every m, phi, n, w (no reality hypothesis on phi):
     `<e_L, A^m (V e_L)> = <e_U, A^m (V e_U)>`  (`e_L = kstPnLower n`, `e_U = kstPnUpper n`,
   `V = potentialOnPn phi n`).  This replaces the abstract K-based `reversal_core`, because the bare
   kernel K is not bounded on l^2 (phi-hat is only l^2); only `K D` (Hilbert--Schmidt) is used. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory NlsGge.Schur NlsGge.Analysis NlsGge.Pilot
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST006
  NlsGge.Atomic.KST007 NlsGge.Atomic.KST012 NlsGge.Atomic.KST016
open scoped InnerProductSpace

namespace NlsGge.DM009Conc

/-! ### Fourier coordinates, pairing, reflection -/

def pcf (x : KSTPairL2) (c : Bool) (l : ℤ) : ℂ := spectralCoeff (x c) l

lemma spectralCoeff_zero (l : ℤ) : spectralCoeff (0 : SpectralScalarL2) l = 0 := by
  have h0 : (fourierBasis (T := (2 : ℝ))).repr (0 : SpectralScalarL2) = 0 :=
    LinearIsometryEquiv.map_zero _
  unfold spectralCoeff
  rw [h0]
  rfl

lemma pcf_zero (c : Bool) (l : ℤ) : pcf (0 : KSTPairL2) c l = 0 := by
  simp [pcf, spectralCoeff_zero]

lemma pcf_sq_summable (x : KSTPairL2) (c : Bool) :
    Summable (fun l : ℤ => ‖pcf x c l‖ ^ 2) := by
  simpa only [pcf, spectralCoeff, ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp ((fourierBasis (T := (2 : ℝ))).repr (x c))).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)

lemma pcf_le_norm (x : KSTPairL2) (c : Bool) (l : ℤ) : ‖pcf x c l‖ ≤ ‖x‖ := by
  have h1 := lp.norm_apply_le_norm (two_ne_zero : (2 : ENNReal) ≠ 0)
    ((fourierBasis (T := (2 : ℝ))).repr (x c)) l
  have h2 : ‖(fourierBasis (T := (2 : ℝ))).repr (x c)‖ = ‖x c‖ :=
    (fourierBasis (T := (2 : ℝ))).repr.norm_map (x c)
  rw [h2] at h1
  exact h1.trans (PiLp.norm_apply_le x c)

lemma pcf_ext {x y : KSTPairL2} (h : ∀ c l, pcf x c l = pcf y c l) : x = y := by
  apply PiLp.ext
  intro c
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext l
  exact h c l

def pB (x y : KSTPairL2) : ℂ := ∑ c : Bool, ∑' l : ℤ, pcf x c l * pcf y c l

lemma pB_symm (x y : KSTPairL2) : pB x y = pB y x := by
  unfold pB
  exact Finset.sum_congr rfl (fun c _ => tsum_congr (fun l => mul_comm _ _))

lemma reflLp_mem (f : lp (fun _ : ℤ => ℂ) 2) : Memℓp (fun m : ℤ => f (-m)) 2 := by
  have hs : Summable (fun k : ℤ => ‖f k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hs' : Summable (fun m : ℤ => ‖f (-m)‖ ^ 2) :=
    hs.comp_injective neg_injective
  exact memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs')

def reflLp (f : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun m => f (-m), reflLp_mem f⟩

/-- The reflection `(c, m) ↦ (¬c, -m)` on the doubled pair space. -/
def pRefl (x : KSTPairL2) : KSTPairL2 :=
  WithLp.toLp 2 (fun c : Bool =>
    (fourierBasis (T := (2 : ℝ))).repr.symm
      (reflLp ((fourierBasis (T := (2 : ℝ))).repr (x (!c)))))

lemma pcf_refl (x : KSTPairL2) (c : Bool) (l : ℤ) : pcf (pRefl x) c l = pcf x (!c) (-l) := by
  have h : (pRefl x) c = (fourierBasis (T := (2 : ℝ))).repr.symm
      (reflLp ((fourierBasis (T := (2 : ℝ))).repr (x (!c)))) := rfl
  unfold pcf spectralCoeff
  rw [h, LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma pRefl_refl (x : KSTPairL2) : pRefl (pRefl x) = x := by
  apply pcf_ext
  intro c l
  rw [pcf_refl, pcf_refl]
  simp

lemma pB_refl (x y : KSTPairL2) : pB (pRefl x) (pRefl y) = pB x y := by
  have e : ∀ (c : Bool), ∑' l : ℤ, pcf (pRefl x) c l * pcf (pRefl y) c l =
      ∑' l : ℤ, pcf x (!c) l * pcf y (!c) l := by
    intro c
    simp only [pcf_refl]
    exact (Equiv.neg ℤ).tsum_eq (fun l => pcf x (!c) l * pcf y (!c) l)
  simp only [pB, Fintype.sum_bool, e, Bool.not_true, Bool.not_false]
  exact add_comm _ _

lemma pB_refl_right (z w : KSTPairL2) : pB z (pRefl w) = pB (pRefl z) w := by
  have h := pB_refl z (pRefl w)
  rw [pRefl_refl] at h
  exact h.symm

/-! ### Basis vectors and inner products -/

lemma spectralCoeff_eq_inner (g : SpectralScalarL2) (k : ℤ) :
    spectralCoeff g k = ⟪spectralBasis k, g⟫_ℂ := by
  have hb : (fourierBasis (T := (2 : ℝ))) k = spectralBasis k := congrFun coe_fourierBasis k
  unfold spectralCoeff
  calc _ = ⟪fourierBasis (T := (2 : ℝ)) k, g⟫_ℂ :=
        (fourierBasis (T := (2 : ℝ))).repr_apply_apply g k
    _ = ⟪spectralBasis k, g⟫_ℂ := by rw [hb]; rfl

lemma spectralCoeff_smul (c : ℂ) (g : SpectralScalarL2) (k : ℤ) :
    spectralCoeff (c • g) k = c * spectralCoeff g k := by
  rw [spectralCoeff_eq_inner, spectralCoeff_eq_inner, inner_smul_right]

lemma spectralCoeff_fm (k a : ℤ) (g : SpectralScalarL2) :
    spectralCoeff (NlsGge.Schur.fourierMultiplier k g) a = fourierCoeff g (a - k) := by
  rw [spectralCoeff_eq_inner]
  exact inner_basis_mul a k g

lemma spectralCoeff_basis (m l : ℤ) :
    spectralCoeff (spectralBasis m) l = if l = m then 1 else 0 := by
  have hrepr : (fourierBasis (T := (2 : ℝ))).repr (spectralBasis m) = lp.single 2 m (1 : ℂ) := by
    simpa [spectralBasis] using (fourierBasis (T := (2 : ℝ))).repr_self m
  unfold spectralCoeff
  rw [hrepr]
  by_cases h : l = m
  · subst h
    simp
  · simp [h]

def pEb (c : Bool) (m : ℤ) : KSTPairL2 := PiLp.single 2 c (spectralBasis m)

lemma pcf_eb (c' : Bool) (m : ℤ) (c : Bool) (l : ℤ) :
    pcf (pEb c' m) c l = if c = c' ∧ l = m then 1 else 0 := by
  cases c <;> cases c' <;> simp [pcf, pEb, spectralCoeff_basis, spectralCoeff_zero]

lemma inner_pEb (c : Bool) (m : ℤ) (x : KSTPairL2) : inner ℂ (pEb c m) x = pcf x c m := by
  unfold pEb pcf
  rw [inner_single_left, spectralCoeff_eq_inner]

lemma pEb_norm (c : Bool) (m : ℤ) : ‖pEb c m‖ = 1 := by
  unfold pEb
  rw [PiLp.norm_single]
  exact spectralBasis_norm m

/-! ### The free factor, its inverse, and the diagonal operator D -/

abbrev pF (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) : EndH :=
  1 + (w - z0) • complementaryMultiplier n z0 hz0

def pfc (n : ℤ) (z0 w : ℂ) (c : Bool) (l : ℤ) : ℂ :=
  1 + (w - z0) * complementaryResolventCoeff n z0 (sourceModeIndex c l)

lemma pcf_M0 (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (y : KSTPairL2) (c : Bool) (l : ℤ) :
    pcf (complementaryMultiplier n z hz y) c l =
      complementaryResolventCoeff n z (sourceModeIndex c l) * pcf y c l := by
  unfold pcf spectralCoeff
  exact compMult_repr n z hz y c l

lemma pcf_pF (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (x : KSTPairL2)
    (c : Bool) (l : ℤ) : pcf (pF n z0 hz0 w x) c l = pfc n z0 w c l * pcf x c l := by
  have hF : (pF n z0 hz0 w x) c = x c + (w - z0) • (complementaryMultiplier n z0 hz0 x) c := rfl
  have h := pcf_M0 n z0 hz0 x c l
  unfold pcf spectralCoeff at h ⊢
  rw [hF, coe_repr_add, coe_repr_smul, h]
  unfold pfc
  ring

lemma pfc_ne_zero (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ)
    (hu : IsUnit (pF n z0 hz0 w)) (c : Bool) (l : ℤ) : pfc n z0 w c l ≠ 0 := by
  intro h0
  obtain ⟨u, hu'⟩ := hu
  have hFx : pF n z0 hz0 w (pEb c l) = 0 := by
    apply pcf_ext
    intro c' l'
    rw [pcf_pF, pcf_zero, pcf_eb]
    by_cases hh : c' = c ∧ l' = l
    · obtain ⟨rfl, rfl⟩ := hh
      simp [h0]
    · simp [hh]
  have h1 := ContinuousLinearMap.ext_iff.mp (Units.inv_mul u) (pEb c l)
  rw [ContinuousLinearMap.mul_apply, hu', hFx, map_zero, ContinuousLinearMap.one_apply] at h1
  have h2 := pcf_eb c l c l
  rw [← h1, pcf_zero] at h2
  simp at h2

open Classical in
def pgc (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (c : Bool) (l : ℤ) : ℂ :=
  if IsUnit (pF n z0 hz0 w) then (pfc n z0 w c l)⁻¹ else 0

lemma pcf_inverse (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (x : KSTPairL2)
    (c : Bool) (l : ℤ) :
    pcf (Ring.inverse (pF n z0 hz0 w) x) c l = pgc n z0 hz0 w c l * pcf x c l := by
  by_cases hu : IsUnit (pF n z0 hz0 w)
  · have hFy : pF n z0 hz0 w (Ring.inverse (pF n z0 hz0 w) x) = x := by
      have h := Ring.mul_inverse_cancel (pF n z0 hz0 w) hu
      calc pF n z0 hz0 w (Ring.inverse (pF n z0 hz0 w) x)
          = ((pF n z0 hz0 w) * Ring.inverse (pF n z0 hz0 w)) x := rfl
        _ = x := by rw [h, ContinuousLinearMap.one_apply]
    have hf := pfc_ne_zero n z0 hz0 w hu c l
    have h2 := pcf_pF n z0 hz0 w (Ring.inverse (pF n z0 hz0 w) x) c l
    rw [hFy] at h2
    unfold pgc
    rw [if_pos hu, h2, inv_mul_cancel_left₀ hf]
  · rw [Ring.inverse_non_unit _ hu]
    unfold pgc
    rw [if_neg hu]
    simp [pcf_zero]

lemma pgc_le (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (c : Bool) (l : ℤ) :
    ‖pgc n z0 hz0 w c l‖ ≤ ‖Ring.inverse (pF n z0 hz0 w)‖ := by
  have h := pcf_inverse n z0 hz0 w (pEb c l) c l
  have h1 : pcf (pEb c l) c l = 1 := by rw [pcf_eb]; simp
  rw [h1, mul_one] at h
  rw [← h]
  calc ‖pcf (Ring.inverse (pF n z0 hz0 w) (pEb c l)) c l‖
      ≤ ‖Ring.inverse (pF n z0 hz0 w) (pEb c l)‖ := pcf_le_norm _ _ _
    _ ≤ ‖Ring.inverse (pF n z0 hz0 w)‖ * ‖pEb c l‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖Ring.inverse (pF n z0 hz0 w)‖ := by rw [pEb_norm, mul_one]

def peta (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (c : Bool) (l : ℤ) : ℂ :=
  complementaryResolventCoeff n z0 (sourceModeIndex c l) * pgc n z0 hz0 w c l

def pD (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) : EndH :=
  complementaryMultiplier n z0 hz0 * Ring.inverse (pF n z0 hz0 w)

lemma pcf_pD (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (x : KSTPairL2)
    (c : Bool) (l : ℤ) : pcf (pD n z0 hz0 w x) c l = peta n z0 hz0 w c l * pcf x c l := by
  have e : pD n z0 hz0 w x =
      complementaryMultiplier n z0 hz0 (Ring.inverse (pF n z0 hz0 w) x) := rfl
  rw [e, pcf_M0, pcf_inverse]
  unfold peta
  ring

lemma smi_refl (c : Bool) (l : ℤ) : sourceModeIndex (!c) (-l) = sourceModeIndex c l := by
  cases c <;> simp [sourceModeIndex]

lemma pfc_refl (n : ℤ) (z0 w : ℂ) (c : Bool) (l : ℤ) :
    pfc n z0 w (!c) (-l) = pfc n z0 w c l := by
  unfold pfc
  rw [smi_refl]

lemma pgc_refl (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (c : Bool) (l : ℤ) :
    pgc n z0 hz0 w (!c) (-l) = pgc n z0 hz0 w c l := by
  unfold pgc
  rw [pfc_refl]

lemma peta_refl (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (c : Bool) (l : ℤ) :
    peta n z0 hz0 w (!c) (-l) = peta n z0 hz0 w c l := by
  unfold peta
  rw [smi_refl, pgc_refl]

lemma peta_refl' (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (c : Bool) (l : ℤ) :
    peta n z0 hz0 w c (-l) = peta n z0 hz0 w (!c) l := by
  have h := peta_refl n z0 hz0 w (!c) l
  rw [Bool.not_not] at h
  exact h

lemma pD_refl (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (x : KSTPairL2) :
    pD n z0 hz0 w (pRefl x) = pRefl (pD n z0 hz0 w x) := by
  apply pcf_ext
  intro c l
  rw [pcf_pD, pcf_refl, pcf_refl, pcf_pD, peta_refl]

lemma pB_pD (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (x y : KSTPairL2) :
    pB (pD n z0 hz0 w x) y = pB x (pD n z0 hz0 w y) := by
  unfold pB
  refine Finset.sum_congr rfl (fun c _ => tsum_congr (fun l => ?_))
  rw [pcf_pD, pcf_pD]
  ring

/-! ### Square summability of the weights -/

lemma dist_sq_summable (n : ℤ) :
    Summable (fun m : ℤ => 1 / (Int.natAbs (m - n) : ℝ) ^ 2) := by
  have hbase0 : Summable (fun d : ℤ => 1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hbase : Summable (fun d : ℤ => 1 / (Int.natAbs d : ℝ) ^ 2) := by
    convert hbase0 using 1 <;> simp [Nat.cast_natAbs, Int.cast_abs, abs_pow]
  have hshift := (Equiv.addRight (-n)).summable_iff.mpr hbase
  have hs : Summable (fun m : ℤ => 1 / (Int.natAbs (m + -n) : ℝ) ^ 2) :=
    hshift.congr fun m => by rfl
  exact hs.congr fun m => by rw [show m + -n = m - n by omega]

lemma resolvent_sq_summable (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (b : Bool) :
    Summable (fun m : ℤ =>
      ‖complementaryResolventCoeff n z (sourceModeIndex b m)‖ ^ 2) := by
  have hs : Summable (fun k : ℤ => ‖complementaryResolventCoeff n z k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
      (dist_sq_summable n)
    have hsq := (sq_le_sq₀ (norm_nonneg (complementaryResolventCoeff n z k))
      (by positivity : 0 ≤ 1 / (Int.natAbs (k - n) : ℝ))).2
        (complementaryResolventCoeff_bound n k z hz)
    simpa only [div_pow, one_pow] using hsq
  cases b
  · simpa [sourceModeIndex] using hs
  · simpa [sourceModeIndex, Function.comp_def] using (Equiv.neg ℤ).summable_iff.mpr hs

lemma peta_sq_summable (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (c : Bool) :
    Summable (fun l : ℤ => ‖peta n z0 hz0 w c l‖ ^ 2) := by
  have hs := resolvent_sq_summable n z0 hz0 c
  refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_)
    (hs.mul_left (‖Ring.inverse (pF n z0 hz0 w)‖ ^ 2))
  unfold peta
  rw [norm_mul, mul_pow]
  have h2 : ‖pgc n z0 hz0 w c l‖ ^ 2 ≤ ‖Ring.inverse (pF n z0 hz0 w)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (pgc_le n z0 hz0 w c l) 2
  calc ‖complementaryResolventCoeff n z0 (sourceModeIndex c l)‖ ^ 2 * ‖pgc n z0 hz0 w c l‖ ^ 2
      ≤ ‖complementaryResolventCoeff n z0 (sourceModeIndex c l)‖ ^ 2 *
          ‖Ring.inverse (pF n z0 hz0 w)‖ ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = ‖Ring.inverse (pF n z0 hz0 w)‖ ^ 2 *
          ‖complementaryResolventCoeff n z0 (sourceModeIndex c l)‖ ^ 2 := mul_comm _ _

lemma summable_norm_mul_of_sq (a b : ℤ → ℂ) (ha : Summable fun l => ‖a l‖ ^ 2)
    (hb : Summable fun l => ‖b l‖ ^ 2) : Summable fun l => ‖a l * b l‖ := by
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
    ((ha.add hb).mul_left (1 / 2))
  rw [norm_mul]
  nlinarith [sq_nonneg (‖a l‖ - ‖b l‖)]

lemma pD_norm_summable (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (v : KSTPairL2)
    (c : Bool) : Summable fun l : ℤ => ‖pcf (pD n z0 hz0 w v) c l‖ :=
  (summable_norm_mul_of_sq _ _ (peta_sq_summable n z0 hz0 w c) (pcf_sq_summable v c)).congr
    (fun l => by rw [pcf_pD])

/-! ### The Fubini identity -/

theorem swap_sum (a b k : ℤ → ℂ) (ha : Summable fun l => ‖a l‖) (hb : Summable fun l => ‖b l‖)
    (M : ℝ) (hk : ∀ j, ‖k j‖ ≤ M) :
    ∑' l, a l * ∑' m, k (l - m) * b m = ∑' l, b (-l) * ∑' m, k (l - m) * a (-m) := by
  obtain ⟨h, hh⟩ : ∃ h : ℤ × ℤ → ℂ, ∀ l m, h (l, m) = a l * (k (l - m) * b m) :=
    ⟨fun p => a p.1 * (k (p.1 - p.2) * b p.2), fun _ _ => rfl⟩
  have hsum : Summable h := by
    refine Summable.of_norm_bounded
      (g := fun p : ℤ × ℤ => M * (‖a p.1‖ * ‖b p.2‖))
      ((ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left M) ?_
    rintro ⟨l, m⟩
    rw [hh, norm_mul, norm_mul]
    have h1 : ‖k (l - m)‖ * ‖b m‖ ≤ M * ‖b m‖ :=
      mul_le_mul_of_nonneg_right (hk _) (norm_nonneg _)
    calc ‖a l‖ * (‖k (l - m)‖ * ‖b m‖) ≤ ‖a l‖ * (M * ‖b m‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = M * (‖a l‖ * ‖b m‖) := by ring
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (-p.2, -p.1)
      invFun := fun p => (-p.2, -p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have hsum' : Summable (fun p => h (e p)) := e.summable_iff.mpr hsum
  have hL : ∑' l, a l * ∑' m, k (l - m) * b m = ∑' p, h p := by
    rw [hsum.tsum_prod]
    refine tsum_congr fun l => ?_
    rw [← tsum_mul_left]
    exact tsum_congr fun m => (hh l m).symm
  have hR : ∑' l, b (-l) * ∑' m, k (l - m) * a (-m) = ∑' p, h (e p) := by
    rw [hsum'.tsum_prod]
    refine tsum_congr fun l => ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    show _ = h (-m, -l)
    rw [hh, show -m - -l = l - m by ring]
    ring
  rw [hL, hR]
  exact (e.tsum_eq h).symm

abbrev pA (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential) : EndH :=
  localQ n z0 hz0 (w, φ)

lemma pcf_localQ (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential)
    (y : KSTPairL2) (c : Bool) (l : ℤ) :
    pcf (pA n z0 hz0 w φ y) c l =
      ∑' m : ℤ, potentialCoeff φ c (l - m) * pcf (pD n z0 hz0 w y) (!c) m := by
  have e : pA n z0 hz0 w φ y = qOperator φ n z0 hz0 (Ring.inverse (pF n z0 hz0 w) y) := rfl
  rw [e]
  unfold pcf spectralCoeff
  rw [q_coeff_via_D]
  rfl

lemma potentialCoeff_le (φ : Potential) (c : Bool) (k : ℤ) :
    ‖potentialCoeff φ c k‖ ≤ ‖naturalPhysicalCoverL2 (φ c)‖ := by
  have h : potentialCoeff φ c k = spectralCoeff (naturalPhysicalCoverL2 (φ c)) k := by
    unfold potentialCoeff spectralCoeff
    exact (fourierBasis_repr _ k).symm
  rw [h]
  unfold spectralCoeff
  have h1 := lp.norm_apply_le_norm (two_ne_zero : (2 : ENNReal) ≠ 0)
    ((fourierBasis (T := (2 : ℝ))).repr (naturalPhysicalCoverL2 (φ c))) k
  have h2 : ‖(fourierBasis (T := (2 : ℝ))).repr (naturalPhysicalCoverL2 (φ c))‖ =
      ‖naturalPhysicalCoverL2 (φ c)‖ :=
    (fourierBasis (T := (2 : ℝ))).repr.norm_map _
  rwa [h2] at h1

lemma pP_term (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential)
    (v y : KSTPairL2) (c : Bool) (l : ℤ) :
    pcf (pD n z0 hz0 w (pA n z0 hz0 w φ (pRefl v))) c l * pcf (pRefl y) c l =
      pcf (pD n z0 hz0 w y) (!c) (-l) *
        ∑' m : ℤ, potentialCoeff φ c (l - m) * pcf (pD n z0 hz0 w v) c (-m) := by
  rw [pcf_pD, pcf_localQ, pcf_refl y]
  simp only [pcf_pD, pcf_refl, Bool.not_not, peta_refl, peta_refl']
  ring

theorem pP (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential)
    (v y : KSTPairL2) :
    pB (pD n z0 hz0 w v) (pA n z0 hz0 w φ y) =
      pB (pD n z0 hz0 w (pA n z0 hz0 w φ (pRefl v))) (pRefl y) := by
  unfold pB
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hS := swap_sum (fun l => pcf (pD n z0 hz0 w v) c l)
    (fun m => pcf (pD n z0 hz0 w y) (!c) m) (fun j => potentialCoeff φ c j)
    (pD_norm_summable n z0 hz0 w v c) (pD_norm_summable n z0 hz0 w y (!c))
    ‖naturalPhysicalCoverL2 (φ c)‖ (fun j => potentialCoeff_le φ c j)
  beta_reduce at hS
  calc ∑' l, pcf (pD n z0 hz0 w v) c l * pcf (pA n z0 hz0 w φ y) c l
      = ∑' l, pcf (pD n z0 hz0 w v) c l *
          ∑' m, potentialCoeff φ c (l - m) * pcf (pD n z0 hz0 w y) (!c) m :=
        tsum_congr (fun l => by rw [pcf_localQ])
    _ = ∑' l, pcf (pD n z0 hz0 w y) (!c) (-l) *
          ∑' m, potentialCoeff φ c (l - m) * pcf (pD n z0 hz0 w v) c (-m) := hS
    _ = ∑' l, pcf (pD n z0 hz0 w (pA n z0 hz0 w φ (pRefl v))) c l * pcf (pRefl y) c l :=
        tsum_congr (fun l => (pP_term n z0 hz0 w φ v y c l).symm)

/-! ### Claim_j, the potential on P_n, the endpoints, and path reversal -/

theorem pClaim (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential) (j : ℕ) :
    ∀ x y : KSTPairL2,
      pB x (pD n z0 hz0 w ((pA n z0 hz0 w φ ^ j) y)) =
        pB (pD n z0 hz0 w ((pA n z0 hz0 w φ ^ j) (pRefl x))) (pRefl y) := by
  induction j with
  | zero =>
    intro x y
    simp only [pow_zero, ContinuousLinearMap.one_apply]
    rw [pD_refl, pB_refl, pB_pD]
  | succ j ih =>
    intro x y
    have e1 : ∀ u : KSTPairL2, ((pA n z0 hz0 w φ) ^ (j + 1)) u =
        (pA n z0 hz0 w φ ^ j) (pA n z0 hz0 w φ u) := by
      intro u
      rw [pow_succ, ContinuousLinearMap.mul_apply]
    have e2 : ∀ u : KSTPairL2, ((pA n z0 hz0 w φ) ^ (j + 1)) u =
        pA n z0 hz0 w φ ((pA n z0 hz0 w φ ^ j) u) := by
      intro u
      rw [pow_succ', ContinuousLinearMap.mul_apply]
    rw [e1 y, ih x (pA n z0 hz0 w φ y),
      pB_refl_right (pD n z0 hz0 w ((pA n z0 hz0 w φ ^ j) (pRefl x))) (pA n z0 hz0 w φ y),
      ← pD_refl n z0 hz0 w ((pA n z0 hz0 w φ ^ j) (pRefl x)),
      pP n z0 hz0 w φ (pRefl ((pA n z0 hz0 w φ ^ j) (pRefl x))) y,
      pRefl_refl ((pA n z0 hz0 w φ ^ j) (pRefl x)), e2 (pRefl x)]

lemma pot_true (φ : Potential) (n : ℤ) (u : KSTPairL2) :
    potentialOnPn φ n u true =
      inner ℂ (kstPnLower n) u • NlsGge.Schur.fourierMultiplier n
        (naturalPhysicalCoverL2 (φ true)) := by
  simp [potentialOnPn, InnerProductSpace.rankOne_apply]

lemma pot_false (φ : Potential) (n : ℤ) (u : KSTPairL2) :
    potentialOnPn φ n u false =
      inner ℂ (kstPnUpper n) u • NlsGge.Schur.fourierMultiplier (-n)
        (naturalPhysicalCoverL2 (φ false)) := by
  simp [potentialOnPn, InnerProductSpace.rankOne_apply]

lemma pcf_pot_true (φ : Potential) (n : ℤ) (u : KSTPairL2) (q : ℤ) :
    pcf (potentialOnPn φ n u) true q =
      inner ℂ (kstPnLower n) u * potentialCoeff φ true (q - n) := by
  unfold pcf
  rw [pot_true, spectralCoeff_smul, spectralCoeff_fm]
  rfl

lemma pcf_pot_false (φ : Potential) (n : ℤ) (u : KSTPairL2) (q : ℤ) :
    pcf (potentialOnPn φ n u) false q =
      inner ℂ (kstPnUpper n) u * potentialCoeff φ false (q - -n) := by
  unfold pcf
  rw [pot_false, spectralCoeff_smul, spectralCoeff_fm]
  rfl

lemma kstPnLower_eq (n : ℤ) : kstPnLower n = pEb false n := rfl

lemma kstPnUpper_eq (n : ℤ) : kstPnUpper n = pEb true (-n) := rfl

lemma inner_LL (n : ℤ) : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by
  rw [kstPnLower_eq, inner_pEb, pcf_eb]
  simp

lemma inner_UL (n : ℤ) : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by
  rw [kstPnUpper_eq, kstPnLower_eq, inner_pEb, pcf_eb]
  simp

lemma inner_LU (n : ℤ) : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by
  rw [kstPnUpper_eq, kstPnLower_eq, inner_pEb, pcf_eb]
  simp

lemma inner_UU (n : ℤ) : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by
  rw [kstPnUpper_eq, inner_pEb, pcf_eb]
  simp

lemma pE1 (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential)
    (y : KSTPairL2) :
    inner ℂ (kstPnLower n) (pA n z0 hz0 w φ y) =
      pB (pRefl (potentialOnPn φ n (kstPnUpper n))) (pD n z0 hz0 w y) := by
  have hUt : ∀ q, pcf (potentialOnPn φ n (kstPnUpper n)) true q = 0 := by
    intro q
    rw [pcf_pot_true, inner_LU, zero_mul]
  have hUf : ∀ q, pcf (potentialOnPn φ n (kstPnUpper n)) false q =
      potentialCoeff φ false (q - -n) := by
    intro q
    rw [pcf_pot_false, inner_UU, one_mul]
  rw [kstPnLower_eq, inner_pEb, pcf_localQ]
  unfold pB
  rw [Fintype.sum_bool]
  simp only [pcf_refl, Bool.not_true, Bool.not_false, hUt, hUf, zero_mul, tsum_zero, add_zero]
  exact tsum_congr (fun m => by rw [show -m - -n = n - m by ring])

lemma pE2 (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential)
    (y : KSTPairL2) :
    inner ℂ (kstPnUpper n) (pA n z0 hz0 w φ y) =
      pB (pRefl (potentialOnPn φ n (kstPnLower n))) (pD n z0 hz0 w y) := by
  have hLt : ∀ q, pcf (potentialOnPn φ n (kstPnLower n)) true q =
      potentialCoeff φ true (q - n) := by
    intro q
    rw [pcf_pot_true, inner_LL, one_mul]
  have hLf : ∀ q, pcf (potentialOnPn φ n (kstPnLower n)) false q = 0 := by
    intro q
    rw [pcf_pot_false, inner_UL, zero_mul]
  rw [kstPnUpper_eq, inner_pEb, pcf_localQ]
  unfold pB
  rw [Fintype.sum_bool]
  simp only [pcf_refl, Bool.not_true, Bool.not_false, hLt, hLf, zero_mul, tsum_zero, zero_add]
  exact tsum_congr (fun m => by rw [show -n - m = -m - n by ring])

/-- Path reversal: the diagonal entries of the Neumann terms at the two resonant vectors agree.
No reality hypothesis on the potential and no restriction on `n`, `w`. -/
theorem preversal (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential)
    (m : ℕ) :
    inner ℂ (kstPnLower n) ((pA n z0 hz0 w φ ^ m) (potentialOnPn φ n (kstPnLower n))) =
      inner ℂ (kstPnUpper n) ((pA n z0 hz0 w φ ^ m) (potentialOnPn φ n (kstPnUpper n))) := by
  cases m with
  | zero =>
    simp only [pow_zero, ContinuousLinearMap.one_apply]
    rw [kstPnLower_eq, kstPnUpper_eq, inner_pEb, inner_pEb]
    rw [← kstPnLower_eq, ← kstPnUpper_eq, pcf_pot_false, pcf_pot_true, inner_UL, inner_LU]
    simp
  | succ j =>
    have e2 : ∀ u : KSTPairL2, ((pA n z0 hz0 w φ) ^ (j + 1)) u =
        pA n z0 hz0 w φ ((pA n z0 hz0 w φ ^ j) u) := by
      intro u
      rw [pow_succ', ContinuousLinearMap.mul_apply]
    rw [e2, e2, pE1, pE2,
      pClaim n z0 hz0 w φ j (pRefl (potentialOnPn φ n (kstPnUpper n)))
        (potentialOnPn φ n (kstPnLower n)),
      pRefl_refl, pB_symm]

end NlsGge.DM009Conc

/- DM-009 S7-concrete (proof development, 2026-10-31). Discharges the diagonal identity for EVERY
   potential `φ`, label `n` and complex `w` (no reality hypothesis, no strip restriction):
     `<e_U, C(w,φ) e_U> = a φ n w`,   `C = localCorrection n (center n) _ (w, φ)`.
   Proof: `A := localQ n (center n) _ (w, φ)` is compact (DM009_S3). With the continuous linear
   functional `Ψ X := <e_L, X (V e_L)> - <e_U, X (V e_U)>` on `E →L E`, path reversal
   (`NlsGge.DM009Conc.preversal`) gives `Ψ (A^m) = 0` for all m, hence by the Neumann series
   `Ψ (Ring.inverse (1 - t • A)) = 0` for `‖t • A‖ < 1`; the identity theorem
   (`NlsGge.DM009Ident.vanish_of_near_zero`) extends `t * Ψ (Ring.inverse (1 - t • A)) = 0` to all t,
   in particular t = 1, and `<e, P y> = <e, y>` for `e ∈ {e_L, e_U}` converts back.
   Depends on: DM009_S6C (NlsGge.DM009Conc), DM009_S3 (NlsGge.DM009S3),
   DM009_S7 IDENT01 (NlsGge.DM009Ident, with S4). Statement avoids `diagU` (defined in S9):
   `diagU φ n w` is definitionally the left-hand side. -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.DM009Diag

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
  NlsGge.Atomic.KST012 NlsGge.Atomic.KST016
open NlsGge.DM009Conc
open Filter Topology

/-- `Ψ X = <e_L, X (V e_L)> - <e_U, X (V e_U)>` as a continuous linear functional. -/
def psiFun (n : ℤ) (φ : Potential) : EndH →L[ℂ] ℂ :=
  (innerSL ℂ (kstPnLower n)).comp
      (ContinuousLinearMap.apply ℂ KSTPairL2 (potentialOnPn φ n (kstPnLower n))) -
    (innerSL ℂ (kstPnUpper n)).comp
      (ContinuousLinearMap.apply ℂ KSTPairL2 (potentialOnPn φ n (kstPnUpper n)))

lemma psiFun_apply (n : ℤ) (φ : Potential) (X : EndH) :
    psiFun n φ X = inner ℂ (kstPnLower n) (X (potentialOnPn φ n (kstPnLower n))) -
      inner ℂ (kstPnUpper n) (X (potentialOnPn φ n (kstPnUpper n))) := by
  simp [psiFun]

lemma psiFun_pow (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential) (m : ℕ) :
    psiFun n φ (pA n z0 hz0 w φ ^ m) = 0 := by
  rw [psiFun_apply, preversal, sub_self]

lemma psi_inverse_small (n : ℤ) (z0 : ℂ) (hz0 : z0 ∈ spectralStrip n) (w : ℂ) (φ : Potential)
    (t : ℂ) (ht : ‖t • pA n z0 hz0 w φ‖ < 1) :
    psiFun n φ (Ring.inverse (1 - t • pA n z0 hz0 w φ)) = 0 := by
  have hs := hasSum_geom_series_inverse (t • pA n z0 hz0 w φ) ht
  have hs' := (psiFun n φ).hasSum hs
  have h0 : ∀ i : ℕ, psiFun n φ ((t • pA n z0 hz0 w φ) ^ i) = 0 := by
    intro i
    rw [smul_pow, map_smul, psiFun_pow, smul_zero]
  simp only [h0] at hs'
  exact hs'.unique hasSum_zero

/-- The diagonal identity S7 for every potential. -/
theorem diag_identity (n : ℤ) (φ : Potential) (w : ℂ) :
    inner ℂ (kstPnUpper n) (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
      (NlsGge.ThirdConsultation.KST.center_mem_strip n) (w, φ) (kstPnUpper n)) =
    NlsGge.ThirdConsultation.KST.a φ n w := by
  have hz0 := NlsGge.ThirdConsultation.KST.center_mem_strip n
  have hcomp : IsCompactOperator
      (pA n (NlsGge.ThirdConsultation.KST.center n) hz0 w φ) :=
    NlsGge.DM009S3.s3_localQ_center_isCompactOperator n w φ
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ),
      ‖t • pA n (NlsGge.ThirdConsultation.KST.center n) hz0 w φ‖ < 1 := by
    have hc : Continuous fun t : ℂ =>
        ‖t‖ * ‖pA n (NlsGge.ThirdConsultation.KST.center n) hz0 w φ‖ := by
      fun_prop
    have h1 : ∀ᶠ t in 𝓝 (0 : ℂ),
        ‖t‖ * ‖pA n (NlsGge.ThirdConsultation.KST.center n) hz0 w φ‖ < 1 :=
      (hc.tendsto 0).eventually (gt_mem_nhds (by simp))
    filter_upwards [h1] with t ht
    exact lt_of_le_of_lt (ContinuousLinearMap.opNorm_smul_le t _) ht
  have h0 : ∀ᶠ t in 𝓝 (0 : ℂ), t * psiFun n φ
      (Ring.inverse (1 - t • pA n (NlsGge.ThirdConsultation.KST.center n) hz0 w φ)) = 0 := by
    filter_upwards [hev] with t ht
    rw [psi_inverse_small n _ hz0 w φ t ht, mul_zero]
  have hvan := NlsGge.DM009Ident.vanish_of_near_zero
    (pA n (NlsGge.ThirdConsultation.KST.center n) hz0 w φ) hcomp (psiFun n φ) h0 1
  rw [one_smul, one_mul, psiFun_apply] at hvan
  have hU : inner ℂ (kstPnUpper n) (localCorrection n (NlsGge.ThirdConsultation.KST.center n)
      hz0 (w, φ) (kstPnUpper n)) =
      inner ℂ (kstPnUpper n) (Ring.inverse (1 - pA n (NlsGge.ThirdConsultation.KST.center n)
        hz0 w φ) (potentialOnPn φ n (kstPnUpper n))) :=
    inner_frame_Pn n true _
  have hL : NlsGge.ThirdConsultation.KST.a φ n w =
      inner ℂ (kstPnLower n) (Ring.inverse (1 - pA n (NlsGge.ThirdConsultation.KST.center n)
        hz0 w φ) (potentialOnPn φ n (kstPnLower n))) :=
    inner_frame_Pn n false _
  rw [hU, hL]
  exact (sub_eq_zero.mp hvan).symm

end NlsGge.DM009Diag

/- DM-009 head, PARTIAL (proof development, 2026-10-31): conjuncts 2 and 3 of
   `NlsGge.ThirdConsultation.DM.dm_selfAdjoint_beta_symmetry` (Pro round 9 section 4), i.e.
   `dmBetaMinus v n z = star (dmBetaPlus v n (star z))` and
   `z.im = 0 → ‖dmBetaMinus v n z‖ = ‖dmBetaPlus v n z‖`, for every `v` with `IsPiRealType v`,
   every `n`, every `z`. Conjunct 1 (`dmAlpha`, the diagonal identity S9) is NOT proved here.
   Depends on `NlsGge.DM009Psi.c_eq_conj_b` (DM009_S8, S8). Imports: production DMShared78 only.
   Head not changed; this is a supporting partial result. -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.DM

open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002

theorem dmKstPotential_realForm (v : PiPairL2) (hv : IsPiRealType v) :
    dmKstPotential v false = star (dmKstPotential v true) := by
  have h : NlsGge.Atomic.DM001.scaledPotential v false =
      star (NlsGge.Atomic.DM001.scaledPotential v true) :=
    (NlsGge.Atomic.DM002.pi_realType_iff v).mp hv
  show NlsGge.Atomic.DM002.unitPhysical (NlsGge.Atomic.DM001.scaledPotential v false) =
    star (NlsGge.Atomic.DM002.unitPhysical (NlsGge.Atomic.DM001.scaledPotential v true))
  rw [h, NlsGge.Atomic.DM002.unitPhysical_star]

theorem dm_selfAdjoint_beta_symmetry_part23 (v : PiPairL2) (hv : IsPiRealType v) (n : ℤ)
    (z : ℂ) :
    dmBetaMinus v n z = star (dmBetaPlus v n (star z)) ∧
    (z.im = 0 → ‖dmBetaMinus v n z‖ = ‖dmBetaPlus v n z‖) := by
  have hφ := dmKstPotential_realForm v hv
  have hsp : dmSpectralPoint n (star z) = star (dmSpectralPoint n z) := by
    unfold dmSpectralPoint
    simp [Complex.star_def]
  have hpi : star ((Real.pi : ℂ)⁻¹) = (Real.pi : ℂ)⁻¹ := by
    simp [Complex.star_def, map_inv₀]
  have key := NlsGge.DM009Psi.c_eq_conj_b (dmKstPotential v) hφ n (dmSpectralPoint n z)
  have conj2 : dmBetaMinus v n z = star (dmBetaPlus v n (star z)) := by
    unfold dmBetaMinus dmBetaPlus
    rw [hsp, star_mul', hpi, key]
  refine ⟨conj2, fun him => ?_⟩
  have hz : star z = z := Complex.conj_eq_iff_im.mpr him
  rw [hz] at conj2
  rw [conj2, norm_star]

end NlsGge.ThirdConsultation.DM


open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002

/- DM-009 HEAD, CONDITIONAL (proof development, 2026-10-31). The full printed head
   `NlsGge.ThirdConsultation.DM.dm_selfAdjoint_beta_symmetry` (Pro round 9 section 4; all three
   conjuncts, unchanged) is proved FROM ONE explicit hypothesis `hdiag`, the open diagonal
   identity S7 for the potential `dmKstPotential v` at label `n` (all complex `w`). Conjuncts 2
   and 3 are unconditional (DM009_S10PART). The head is NOT unconditionally proved until
   `hdiag` is discharged by S6 concrete + S7 concrete. -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.DM

theorem dm_selfAdjoint_beta_symmetry_of_diag (v : PiPairL2) (hv : IsPiRealType v) (n : ℤ)
    (z : ℂ)
    (hdiag : ∀ w : ℂ,
      NlsGge.DM009Psi.diagU (dmKstPotential v) n w =
        NlsGge.ThirdConsultation.KST.a (dmKstPotential v) n w) :
    dmAlpha v n (star z) = star (dmAlpha v n z) ∧
    dmBetaMinus v n z = star (dmBetaPlus v n (star z)) ∧
    (z.im = 0 → ‖dmBetaMinus v n z‖ = ‖dmBetaPlus v n z‖) := by
  obtain ⟨h2, h3⟩ := dm_selfAdjoint_beta_symmetry_part23 v hv n z
  refine ⟨?_, h2, h3⟩
  have hsp : dmSpectralPoint n (star z) = star (dmSpectralPoint n z) := by
    unfold dmSpectralPoint
    simp [Complex.star_def]
  have hpi : star ((Real.pi : ℂ)⁻¹) = (Real.pi : ℂ)⁻¹ := by
    simp [Complex.star_def, map_inv₀]
  have hφ := dmKstPotential_realForm v hv
  have key := NlsGge.DM009Psi.a_eq_conj_a_of_diag (dmKstPotential v) hφ n hdiag
    (dmSpectralPoint n z)
  unfold dmAlpha
  rw [hsp, star_mul', hpi, key]

end NlsGge.ThirdConsultation.DM

/- DM-009 HEAD, UNCONDITIONAL (proof development, 2026-10-31). Production wrapper of the final theorem
   (Pro round 9 section 4, text verbatim). Uses `dm_selfAdjoint_beta_symmetry_of_diag`
   (DM009_HEADCOND) and `NlsGge.DM009Diag.diag_identity` (DM009_S7C). -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.DM

open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002

theorem dm_selfAdjoint_beta_symmetry
    (v : PiPairL2) (hv : IsPiRealType v) (n : ℤ) (z : ℂ) :
    dmAlpha v n (star z) = star (dmAlpha v n z) ∧
    dmBetaMinus v n z = star (dmBetaPlus v n (star z)) ∧
    (z.im = 0 → ‖dmBetaMinus v n z‖ = ‖dmBetaPlus v n z‖) :=
  dm_selfAdjoint_beta_symmetry_of_diag v hv n z
    (fun w => NlsGge.DM009Diag.diag_identity n (dmKstPotential v) w)

end NlsGge.ThirdConsultation.DM
