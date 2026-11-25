import QuantumNLS.Prop024WMonomial
import QuantumNLS.Prop022AWeyl
import QuantumNLS.Prop022ACoherent

/-! PROP-024 operator-level Wick expansion, module 2 (Prop024WSector): sector structure of the physical creation/annihilation operators.

On single-sector vectors `inclusion L n y` of the smooth domain `physSmooth L`, `annP f` is the bounded sector map `annSec f n : HN L (n+1) →L HN L n` and `creP f` is its adjoint `creSec f n` (`annP_incl`, `creP_incl`); on the whole smooth domain the sector components of `a(f) y`, `a*(f) y` depend only on the neighbouring sector of `y` (`annP_sector`, `creP_sector_succ`, `creP_sector_zero`).  `annSec_power`: `a(f) h^{⊗(n+1)} = √(n+1) ⟨f,h⟩ h^{⊗n}` (from the frozen `ann_emb_power`).  The iterates `annB f b k : HN L (b+k) →L HN L k`, `creB f a k : HN L k →L HN L (a+k)` realize `a(f)^b`, `a*(f)^a` on sectors (`annPow_incl`, `crePow_incl`), with `inner_creB` (adjointness) and `annB_power`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop024WSector
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop022ACoherent Prop022AWeyl Prop022TensorCompressionR115
open Occupation Ext006SmoothOperatorsR34a Ext006ModeDomainR33a Ext006QuasifreeWeak Prop024WCoordinates Ext006FieldBoundsR42a
open Ext006KernelHilbertSchmidt (physicalBasis)

variable {L : ℝ} [Fact (0 < L)]

lemma Phi_inclusion (n : ℕ) (y : HN L n) : Phi (L := L) (inclusion L n y) = secEmb n y := rfl

lemma incl_mem (n : ℕ) (y : HN L n) : inclusion L n y ∈ physSmooth L := by
  rw [mem_physSmooth, Phi_inclusion]
  exact emb_smooth n y

/-- A single-sector vector as an element of the smooth domain. -/
def inclS (n : ℕ) (y : HN L n) : physSmooth L := ⟨inclusion L n y, incl_mem n y⟩

lemma inclS_val (n : ℕ) (y : HN L n) : (inclS n y).1 = inclusion L n y := rfl

lemma inclS_add (n : ℕ) (y y' : HN L n) : inclS n (y + y') = inclS n y + inclS n y' :=
  Subtype.ext (map_add (inclusion L n) y y')

lemma inclS_smul (n : ℕ) (c : ℂ) (y : HN L n) : inclS n (c • y) = c • inclS n y :=
  Subtype.ext (map_smul (inclusion L n) c y)

/-- A Fock vector is zero in the sector `j` once all its free occupation coordinates of total `j`
vanish. -/
lemma sector_zero_of_coords (x : Fock L) (j : ℕ)
    (h : ∀ m : Occ, total m = j → Ext006PhysicalVacuum.coefficient x m = 0) : x j = 0 := by
  apply (occupationCoefficient (freeBasis L j)).injective
  rw [map_zero]
  apply lp.ext
  funext ⟨m, hm⟩
  subst hm
  exact h m rfl

lemma Phi_annP_incl (f : L2T L) (n : ℕ) (y : HN L (n+1)) :
    Phi (L := L) (annP f (inclS (n+1) y)).1 = annLin (ghat f) n y := by
  rw [annP, Phi_transport]
  rfl

lemma annP_incl_support (f : L2T L) (n : ℕ) (y : HN L (n+1)) (j : ℕ) (hj : j ≠ n) :
    (annP f (inclS (n+1) y)).1 j = 0 := by
  apply sector_zero_of_coords
  intro m hm
  have hphi : Phi (L := L) (annP f (inclS (n+1) y)).1 m = 0 := by
    rw [Phi_annP]
    change inner ℂ ((physicalBasis L).repr f) (xvec (Phi (L := L) (inclusion L (n+1) y)) m) = 0
    have : xvec (Phi (L := L) (inclusion L (n+1) y)) m = 0 := by
      apply lp.ext
      funext a
      change (Real.sqrt ((m a : ℝ) + 1) : ℂ) * (Phi (L := L) (inclusion L (n+1) y)) (m + e a) = 0
      rw [Phi_inclusion, emb_apply_of_ne (n+1) y (m + e a) (by simp [total_add_e, hm]; omega)]
      simp
    rw [this]; simp
  exact hphi


/-- The `n`-th sector of `a(f)` applied to a single `(n+1)`-sector vector, as a linear map. -/
def annSecLin (f : L2T L) (n : ℕ) : HN L (n+1) →ₗ[ℂ] HN L n where
  toFun y := (annP f (inclS (n+1) y)).1 n
  map_add' y y' := by
    rw [inclS_add, map_add]
    rfl
  map_smul' c y := by
    rw [inclS_smul, map_smul]
    rfl

lemma norm_annSecLin_le (f : L2T L) (n : ℕ) (y : HN L (n+1)) :
    ‖annSecLin f n y‖ ≤ (‖f‖ * Real.sqrt ((n : ℝ) + 1)) * ‖y‖ := by
  have h1 : ‖annSecLin f n y‖ ≤ ‖(annP f (inclS (n+1) y)).1‖ :=
    lp.norm_apply_le_norm (by norm_num) _ n
  have h2 : ‖(annP f (inclS (n+1) y)).1‖ = ‖annLin (ghat f) n y‖ := by
    rw [← (Phi (L := L)).norm_map, Phi_annP_incl]
  have h3 := annLin_bound (ghat f) n y
  have h4 : ‖ghat f‖ = ‖f‖ := (QuantumNLS.Fourier.fourierL2 L).norm_map f
  rw [h4] at h3
  exact h1.trans (h2.trans_le h3)

/-- Annihilation of one particle, on the sector level. -/
def annSec (f : L2T L) (n : ℕ) : HN L (n+1) →L[ℂ] HN L n :=
  (annSecLin f n).mkContinuous _ (norm_annSecLin_le f n)

lemma annSec_apply (f : L2T L) (n : ℕ) (y : HN L (n+1)) :
    annSec f n y = (annP f (inclS (n+1) y)).1 n := rfl

/-- `a(f)` maps the sector `n+1` to the sector `n`. -/
lemma annP_incl (f : L2T L) (n : ℕ) (y : HN L (n+1)) :
    (annP f (inclS (n+1) y)).1 = inclusion L n (annSec f n y) := by
  apply lp.ext
  funext j
  by_cases hj : j = n
  · subst hj
    change _ = (lp.single 2 j (annSec f j y) : Fock L) j
    rw [lp.single_apply_self]; rfl
  · rw [annP_incl_support f n y j hj]
    change _ = (lp.single 2 n (annSec f n y) : Fock L) j
    rw [lp.single_apply_ne _ _ _ hj]

lemma annP_incl_zero (f : L2T L) (y : HN L 0) : (annP f (inclS 0 y)).1 = 0 := by
  apply (Phi (L := L)).injective
  rw [map_zero, annP, Phi_transport]
  exact ann_emb_zero _ _

/-- Adjointness of `a(f)` and `a*(f)` on the smooth domain. -/
lemma inner_creP (f : L2T L) (x y : physSmooth L) :
    ⟪x.1, (creP f y).1⟫_ℂ = ⟪(annP f x).1, y.1⟫_ℂ := by
  have h1 : ⟪x.1, (creP f y).1⟫_ℂ = ⟪Phi (L := L) x.1, Phi (L := L) (creP f y).1⟫_ℂ :=
    ((Phi (L := L)).inner_map_map _ _).symm
  have h2 : ⟪(annP f x).1, y.1⟫_ℂ = ⟪Phi (L := L) (annP f x).1, Phi (L := L) y.1⟫_ℂ :=
    ((Phi (L := L)).inner_map_map _ _).symm
  rw [h1, h2, creP, annP, Phi_transport, Phi_transport]
  exact C_adjoint _ (physToD x) (physToD y)

lemma inner_annP (f : L2T L) (x y : physSmooth L) :
    ⟪x.1, (annP f y).1⟫_ℂ = ⟪(creP f x).1, y.1⟫_ℂ := by
  have h1 : ⟪x.1, (annP f y).1⟫_ℂ = ⟪Phi (L := L) x.1, Phi (L := L) (annP f y).1⟫_ℂ :=
    ((Phi (L := L)).inner_map_map _ _).symm
  have h2 : ⟪(creP f x).1, y.1⟫_ℂ = ⟪Phi (L := L) (creP f x).1, Phi (L := L) y.1⟫_ℂ :=
    ((Phi (L := L)).inner_map_map _ _).symm
  rw [h1, h2, creP, annP, Phi_transport, Phi_transport]
  exact A_adjoint _ (physToD x) (physToD y)


/-- One-particle creation on the sector level: the adjoint of `annSec`. -/
def creSec (f : L2T L) (n : ℕ) : HN L n →L[ℂ] HN L (n+1) := (annSec f n).adjoint

lemma inner_creSec (f : L2T L) (n : ℕ) (y : HN L n) (z : HN L (n+1)) :
    ⟪z, creSec f n y⟫_ℂ = ⟪annSec f n z, y⟫_ℂ := by
  rw [creSec, ContinuousLinearMap.adjoint_inner_right]

lemma inner_incl (n : ℕ) (y : HN L n) (x : Fock L) :
    ⟪inclusion L n y, x⟫_ℂ = ⟪y, x n⟫_ℂ := by
  change ⟪(lp.single 2 n y : Fock L), x⟫_ℂ = _
  rw [lp.inner_single_left]

lemma inner_incl_incl_ne (n j : ℕ) (hj : j ≠ n) (y : HN L n) (z : HN L j) :
    ⟪inclusion L j z, inclusion L n y⟫_ℂ = 0 := by
  rw [inner_incl]
  change ⟪z, (lp.single 2 n y : Fock L) j⟫_ℂ = 0
  rw [lp.single_apply_ne _ _ _ hj]; simp

/-- A Fock vector is determined by its pairings with all single-sector vectors. -/
lemma fock_ext (x x' : Fock L) (h : ∀ (j : ℕ) (z : HN L j), ⟪z, x j⟫_ℂ = ⟪z, x' j⟫_ℂ) : x = x' := by
  apply lp.ext
  funext j
  obtain ⟨d, hd⟩ : ∃ d : HN L j, d = x j - x' j := ⟨_, rfl⟩
  have h0 : ⟪d, x j - x' j⟫_ℂ = 0 := by rw [inner_sub_right, h j d, sub_self]
  rw [← hd, inner_self_eq_zero] at h0
  rw [h0] at hd
  exact (sub_eq_zero.mp hd.symm)


lemma fock_ext' (x x' : Fock L)
    (h : ∀ (j : ℕ) (z : HN L j), ⟪inclusion L j z, x⟫_ℂ = ⟪inclusion L j z, x'⟫_ℂ) : x = x' :=
  fock_ext x x' (fun j z => by rw [← inner_incl, ← inner_incl]; exact h j z)

lemma inner_incl_incl_self (n : ℕ) (y z : HN L n) :
    ⟪inclusion L n z, inclusion L n y⟫_ℂ = ⟪z, y⟫_ℂ :=
  (inclusion L n).inner_map_map z y

/-- `a*(f)` maps the sector `n` to the sector `n+1`. -/
lemma creP_incl (f : L2T L) (n : ℕ) (y : HN L n) :
    (creP f (inclS n y)).1 = inclusion L (n+1) (creSec f n y) := by
  apply fock_ext'
  intro j z
  have h := inner_creP f (inclS j z) (inclS n y)
  change ⟪inclusion L j z, (creP f (inclS n y)).1⟫_ℂ = _ at h
  rw [h]
  cases j with
  | zero =>
    rw [annP_incl_zero, inner_zero_left]
    exact (inner_incl_incl_ne (n+1) 0 (by omega) _ _).symm
  | succ j' =>
    rw [annP_incl, inclS_val]
    by_cases hj : j' = n
    · subst hj
      rw [inner_incl_incl_self, inner_incl_incl_self, inner_creSec]
    · rw [inner_incl_incl_ne n j' hj, inner_incl_incl_ne (n+1) (j'+1) (by omega)]


lemma ext_inner_sector {n : ℕ} (u v : HN L n) (h : ∀ z : HN L n, ⟪z, u⟫_ℂ = ⟪z, v⟫_ℂ) : u = v :=
  ext_inner_left ℂ h

/-- Sector locality of `a(f)` on the whole smooth domain. -/
lemma annP_sector (f : L2T L) (y : physSmooth L) (n : ℕ) :
    (annP f y).1 n = annSec f n (y.1 (n+1)) := by
  apply ext_inner_sector
  intro z
  rw [← inner_incl]
  have h := inner_annP f (inclS n z) y
  rw [inclS_val] at h
  rw [h, creP_incl, inner_incl]
  rw [creSec, ContinuousLinearMap.adjoint_inner_left]

lemma creP_sector_succ (f : L2T L) (y : physSmooth L) (n : ℕ) :
    (creP f y).1 (n+1) = creSec f n (y.1 n) := by
  apply ext_inner_sector
  intro z
  rw [← inner_incl]
  have h := inner_creP f (inclS (n+1) z) y
  rw [inclS_val] at h
  rw [h, annP_incl, inner_incl, inner_creSec]

lemma creP_sector_zero (f : L2T L) (y : physSmooth L) : (creP f y).1 0 = 0 := by
  apply ext_inner_sector
  intro z
  rw [← inner_incl]
  have h := inner_creP f (inclS 0 z) y
  rw [inclS_val] at h
  rw [h, annP_incl_zero, inner_zero_left, inner_zero_right]

lemma secEmb_injective (n : ℕ) : Function.Injective (secEmb (L := L) n) := by
  intro x y h
  have h1 : (lp.single 2 n x : Fock L) = lp.single 2 n y := (Phi (L := L)).injective h
  have := congrArg (fun v : Fock L => v n) h1
  simpa [lp.single_apply_self] using this

/-- Action of the sector annihilation on power vectors. -/
lemma annSec_power (f : L2T L) (n : ℕ) (h : L2T L) :
    annSec f n (power (n+1) h) = ((Real.sqrt ((n : ℝ) + 1) : ℂ) * ⟪f, h⟫_ℂ) • power n h := by
  apply secEmb_injective n
  rw [emb_smul]
  have h1 : secEmb n (annSec f n (power (n+1) h)) = Phi (L := L) (annP f (inclS (n+1) (power (n+1) h))).1 := by
    rw [annP_incl]; rfl
  rw [h1, Phi_annP_incl]
  change (A (ghat f) ⟨secEmb (n + 1) (power (n + 1) h), emb_smooth _ _⟩).1 = _
  rw [ann_emb_power]
  congr 2
  unfold ghat
  rw [(QuantumNLS.Fourier.fourierL2 L).inner_map_map]


/-! ### Iterated sector operators -/

/-- Transport along an equality of particle numbers. -/
def castHN {m n : ℕ} (h : m = n) : HN L m ≃ₗᵢ[ℂ] HN L n := by
  subst h
  exact LinearIsometryEquiv.refl ℂ _

lemma castHN_rfl (m : ℕ) (y : HN L m) : castHN (rfl : m = m) y = y := rfl

lemma castHN_power {m n : ℕ} (h : m = n) (g : L2T L) : castHN h (power m g) = power n g := by
  subst h; rfl

lemma castHN_inner {m n : ℕ} (h : m = n) (x y : HN L m) :
    ⟪castHN h x, castHN h y⟫_ℂ = ⟪x, y⟫_ℂ := (castHN h).inner_map_map x y

lemma castHN_symm_inner {m n : ℕ} (h : m = n) (x : HN L n) (y : HN L m) :
    ⟪x, castHN h y⟫_ℂ = ⟪(castHN h).symm x, y⟫_ℂ := by
  subst h; rfl

lemma inclusion_cast {m n : ℕ} (h : m = n) (y : HN L m) :
    inclusion L n (castHN h y) = inclusion L m y := by
  subst h; rfl

lemma inclS_cast {m n : ℕ} (h : m = n) (y : HN L m) :
    inclS n (castHN h y) = inclS m y :=
  Subtype.ext (inclusion_cast h y)

/-- `b` successive annihilations, from sector `b+k` to sector `k`. -/
def annB (f : L2T L) : ∀ (b k : ℕ), HN L (b+k) →L[ℂ] HN L k
  | 0, k => (castHN (Nat.zero_add k)).toContinuousLinearEquiv.toContinuousLinearMap
  | b+1, k => (annB f b k).comp ((annSec f (b+k)).comp
      (castHN (Nat.succ_add b k)).toContinuousLinearEquiv.toContinuousLinearMap)

/-- `a` successive creations, from sector `k` to sector `a+k`. -/
def creB (f : L2T L) : ∀ (a k : ℕ), HN L k →L[ℂ] HN L (a+k)
  | 0, k => (castHN (Nat.zero_add k).symm).toContinuousLinearEquiv.toContinuousLinearMap
  | a+1, k => ((castHN (Nat.succ_add a k).symm).toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((creSec f (a+k)).comp (creB f a k))

lemma annB_zero (f : L2T L) (k : ℕ) (y : HN L (0+k)) : annB f 0 k y = castHN (Nat.zero_add k) y := rfl

lemma annB_succ (f : L2T L) (b k : ℕ) (y : HN L ((b+1)+k)) :
    annB f (b+1) k y = annB f b k (annSec f (b+k) (castHN (Nat.succ_add b k) y)) := rfl

lemma creB_zero (f : L2T L) (k : ℕ) (y : HN L k) : creB f 0 k y = castHN (Nat.zero_add k).symm y := rfl

lemma creB_succ (f : L2T L) (a k : ℕ) (y : HN L k) :
    creB f (a+1) k y = castHN (Nat.succ_add a k).symm (creSec f (a+k) (creB f a k y)) := rfl

lemma annP_incl_cast (f : L2T L) {m n : ℕ} (h : m = n + 1) (y : HN L m) :
    annP f (inclS m y) = inclS n (annSec f n (castHN h y)) := by
  subst h
  apply Subtype.ext
  rw [annP_incl]
  rfl

lemma annPow_incl (f : L2T L) (b k : ℕ) (y : HN L (b+k)) :
    ((annP f) ^ b) (inclS (b+k) y) = inclS k (annB f b k y) := by
  induction b with
  | zero => 
    rw [pow_zero, Module.End.one_apply, annB_zero]
    exact (inclS_cast (Nat.zero_add k) y).symm
  | succ b ih =>
    rw [pow_succ, Module.End.mul_apply, annP_incl_cast f (Nat.succ_add b k) y, ih, annB_succ]

lemma crePow_incl (f : L2T L) (a k : ℕ) (y : HN L k) :
    ((creP f) ^ a) (inclS k y) = inclS (a+k) (creB f a k y) := by
  induction a with
  | zero =>
    rw [pow_zero, Module.End.one_apply, creB_zero]
    exact (inclS_cast (Nat.zero_add k).symm y).symm
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    apply Subtype.ext
    rw [creP_incl, creB_succ, inclS_cast]
    rfl


lemma castHN_symm {m n : ℕ} (h : m = n) (x : HN L n) : (castHN h).symm x = castHN h.symm x := by
  subst h; rfl

lemma inner_cast_right {m n : ℕ} (h : m = n) (z : HN L n) (w : HN L m) :
    ⟪z, castHN h w⟫_ℂ = ⟪castHN h.symm z, w⟫_ℂ := by
  rw [castHN_symm_inner, castHN_symm]

lemma inner_creB (f : L2T L) (a k : ℕ) (z : HN L (a+k)) (w : HN L k) :
    ⟪z, creB f a k w⟫_ℂ = ⟪annB f a k z, w⟫_ℂ := by
  induction a with
  | zero =>
    rw [creB_zero, annB_zero, inner_cast_right]
  | succ a ih =>
    rw [creB_succ, inner_cast_right, inner_creSec, ih, annB_succ]

lemma sqrt_fact_succ (b k : ℕ) :
    Real.sqrt (((b+k : ℕ) : ℝ) + 1) * Real.sqrt (((b+k).factorial : ℝ) / (k.factorial : ℝ)) =
      Real.sqrt (((b+1+k).factorial : ℝ) / (k.factorial : ℝ)) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have : b + 1 + k = (b + k) + 1 := by omega
  rw [this, Nat.factorial_succ]
  push_cast
  ring

lemma annB_power (f : L2T L) (b k : ℕ) (h : L2T L) :
    annB f b k (power (b+k) h) =
      ((Real.sqrt (((b+k).factorial : ℝ) / (k.factorial : ℝ)) : ℂ) * ⟪f, h⟫_ℂ ^ b) • power k h := by
  induction b with
  | zero =>
    rw [annB_zero, castHN_power]
    have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have h1 : (((0+k).factorial : ℕ) : ℝ) / (k.factorial : ℝ) = 1 := by
      rw [Nat.zero_add]; exact div_self hk.ne'
    rw [h1]; simp
  | succ b ih =>
    rw [annB_succ, castHN_power (Nat.succ_add b k) h, annSec_power, map_smul, ih, smul_smul]
    congr 1
    rw [← sqrt_fact_succ b k]
    push_cast
    ring

end QuantumNLS.Prop024WSector

#print axioms QuantumNLS.Prop024WSector.annSec
#print axioms QuantumNLS.Prop024WSector.creSec
#print axioms QuantumNLS.Prop024WSector.annP_incl
#print axioms QuantumNLS.Prop024WSector.creP_incl
#print axioms QuantumNLS.Prop024WSector.annP_sector
#print axioms QuantumNLS.Prop024WSector.creP_sector_succ
#print axioms QuantumNLS.Prop024WSector.creP_sector_zero
#print axioms QuantumNLS.Prop024WSector.annSec_power
#print axioms QuantumNLS.Prop024WSector.annPow_incl
#print axioms QuantumNLS.Prop024WSector.crePow_incl
#print axioms QuantumNLS.Prop024WSector.annB_power
#print axioms QuantumNLS.Prop024WSector.inner_creB

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WSector." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WSector." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Prop024WSector aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
