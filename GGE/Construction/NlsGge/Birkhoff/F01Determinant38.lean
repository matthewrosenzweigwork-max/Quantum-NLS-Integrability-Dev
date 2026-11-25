import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Birkhoff.F01Determinant38b

/-! # F01 (wave A3), file a: Hilbert-scale plumbing for `lem:determinants` (B-free)

Plan and status: `NlsGge/Birkhoff/F01_PLAN.md`.  No declaration here mentions `BirkhoffInput38`.

* instances `CompleteSpace (SobolevCarrier38 r)`;
* coordinates of the real inner product of `SobolevCarrier38 r`;
* the constant complex structure `J38 r` (multiplication by `i`), a real-linear isometry of every
  `SobolevCarrier38 r` with `J² = -1`, commuting with the inclusions, and
  `stdSymplectic38 ξ η = ⟪J ξ, η⟫` on `h⁰`;
* the Fourier projections `projC38 r N` onto `|n| ≤ N` (v2 l.83), orthogonal, commuting with `J`
  and with the inclusions, strongly convergent to the identity, with finite-dimensional range;
* the instance `cp38 N : CplxProj38 (SobolevCarrier38 ((0:ℕ):ℝ))` of the abstract data of file b.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations
open scoped InnerProductSpace
open Filter Topology

instance carrierCompleteSpace38 (r : ℝ) : CompleteSpace (SobolevCarrier38 r) :=
  inferInstanceAs (CompleteSpace (SobolevHilbert r))

/-- Coordinates of the real inner product of `h^r`. -/
theorem carrier_inner_hasSum38 (r : ℝ) (x y : SobolevCarrier38 r) :
    HasSum (fun n : ℤ => sobolevModeWeight r n *
      (starRingEnd ℂ (carrierCoe38 r x n) * carrierCoe38 r y n).re) (inner ℝ x y) := by
  have h1 := carrier_hasSum_norm_sq38 r (x + y)
  have h2 := carrier_hasSum_norm_sq38 r (x - y)
  have h := (h1.sub h2).div_const 4
  have hpt : ∀ n : ℤ, (sobolevModeWeight r n * ‖carrierCoe38 r (x + y) n‖ ^ 2 -
      sobolevModeWeight r n * ‖carrierCoe38 r (x - y) n‖ ^ 2) / 4 =
      sobolevModeWeight r n * (starRingEnd ℂ (carrierCoe38 r x n) * carrierCoe38 r y n).re := by
    intro n
    have e1 : carrierCoe38 r (x + y) n = carrierCoe38 r x n + carrierCoe38 r y n := rfl
    have e2 : carrierCoe38 r (x - y) n = carrierCoe38 r x n - carrierCoe38 r y n := rfl
    rw [e1, e2, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  have hval : (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4 = inner ℝ x y := by
    rw [norm_add_sq_real, norm_sub_sq_real]; ring
  simp only [hpt, hval] at h
  exact h


/-! ## The complex structure `J` (multiplication by `i`) -/

/-- Underlying map of `J38`: `(J x)_n = i x_n`. -/
def Jmap38 (r : ℝ) (x : SobolevCarrier38 r) : SobolevCarrier38 r :=
  carrierMk38 r (fun n => Complex.I * carrierCoe38 r x n)
    (Submodule.smul_mem (weightedSubmodule (sobolevModeWeight r)) Complex.I
      (carrierCoe38_mem r x))

@[simp] theorem carrierCoe38_Jmap38 (r : ℝ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (Jmap38 r x) n = Complex.I * carrierCoe38 r x n := rfl

theorem norm_Jmap38 (r : ℝ) (x : SobolevCarrier38 r) : ‖Jmap38 r x‖ = ‖x‖ := by
  have h1 := carrier_hasSum_norm_sq38 r (Jmap38 r x)
  have h2 := carrier_hasSum_norm_sq38 r x
  have : (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r (Jmap38 r x) n‖ ^ 2) =
      fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2 := by
    funext n; simp [carrierCoe38_Jmap38]
  rw [this] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.unique h2)

/-- The constant complex structure `𝕁` on `h^r` as a real-linear isometry. -/
def J38iso (r : ℝ) : SobolevCarrier38 r →ₗᵢ[ℝ] SobolevCarrier38 r where
  toFun := Jmap38 r
  map_add' x y := carrierExt38 (funext fun n => by
    show Complex.I * (carrierCoe38 r x n + carrierCoe38 r y n) =
      Complex.I * carrierCoe38 r x n + Complex.I * carrierCoe38 r y n
    ring)
  map_smul' c x := carrierExt38 (funext fun n => by
    show Complex.I * ((c : ℂ) * carrierCoe38 r x n) = (c : ℂ) * (Complex.I * carrierCoe38 r x n)
    ring)
  norm_map' := norm_Jmap38 r

/-- `J` as a continuous real-linear map. -/
def J38 (r : ℝ) : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r :=
  (J38iso r).toContinuousLinearMap

@[simp] theorem carrierCoe38_J38 (r : ℝ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (J38 r x) n = Complex.I * carrierCoe38 r x n := rfl

theorem J38_J38 (r : ℝ) (x : SobolevCarrier38 r) : J38 r (J38 r x) = -x := by
  apply carrierExt38
  funext n
  show Complex.I * (Complex.I * carrierCoe38 r x n) = -carrierCoe38 r x n
  rw [← mul_assoc, Complex.I_mul_I]; ring

theorem J38_mul_J38 (r : ℝ) : J38 r * J38 r = -1 := by
  apply ContinuousLinearMap.ext
  intro x
  show J38 r (J38 r x) = -x
  exact J38_J38 r x

theorem norm_J38 (r : ℝ) (x : SobolevCarrier38 r) : ‖J38 r x‖ = ‖x‖ := norm_Jmap38 r x

theorem inner_J38_left (r : ℝ) (x y : SobolevCarrier38 r) :
    inner ℝ (J38 r x) y = -inner ℝ x (J38 r y) := by
  have h1 := carrier_inner_hasSum38 r (J38 r x) y
  have h2 := (carrier_inner_hasSum38 r x (J38 r y)).neg
  have : (fun n : ℤ => sobolevModeWeight r n *
      (starRingEnd ℂ (carrierCoe38 r (J38 r x) n) * carrierCoe38 r y n).re) =
      fun n => -(sobolevModeWeight r n *
        (starRingEnd ℂ (carrierCoe38 r x n) * carrierCoe38 r (J38 r y) n).re) := by
    funext n
    simp only [carrierCoe38_J38, map_mul, Complex.conj_I]
    have : (-Complex.I * (starRingEnd ℂ) (carrierCoe38 r x n) * carrierCoe38 r y n) =
        -((starRingEnd ℂ) (carrierCoe38 r x n) * (Complex.I * carrierCoe38 r y n)) := by ring
    rw [this, Complex.neg_re]; ring
  rw [this] at h1
  exact h1.unique h2

/-- On `h⁰` the standard symplectic form is `⟪J ξ, η⟫` (and the series converges). -/
theorem stdSymplectic38_eq_inner (ξ η : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    stdSymplectic38 (carrierCoe38 _ ξ) (carrierCoe38 _ η) = inner ℝ (J38 _ ξ) η := by
  have h := carrier_inner_hasSum38 ((0 : ℕ) : ℝ) (J38 _ ξ) η
  have : (fun n : ℤ => sobolevModeWeight ((0 : ℕ) : ℝ) n *
      (starRingEnd ℂ (carrierCoe38 ((0 : ℕ) : ℝ) (J38 _ ξ) n) * carrierCoe38 ((0 : ℕ) : ℝ) η n).re) =
      fun n => (starRingEnd ℂ (carrierCoe38 ((0 : ℕ) : ℝ) ξ n) * carrierCoe38 ((0 : ℕ) : ℝ) η n).im := by
    funext n
    rw [sobolevModeWeight_natCast_zero, one_mul, carrierCoe38_J38]
    simp only [map_mul, Complex.conj_I]
    have : (-Complex.I * (starRingEnd ℂ) (carrierCoe38 ((0 : ℕ) : ℝ) ξ n) *
        carrierCoe38 ((0 : ℕ) : ℝ) η n) =
        -Complex.I * ((starRingEnd ℂ) (carrierCoe38 ((0 : ℕ) : ℝ) ξ n) *
        carrierCoe38 ((0 : ℕ) : ℝ) η n) := by ring
    rw [this]
    simp [Complex.mul_re]
  rw [this] at h
  exact h.tsum_eq

/-- `J` commutes with the inclusions of the scale. -/
theorem J38_incl {r s : ℝ} (h : r ≤ s) (x : SobolevCarrier38 s) :
    J38 r (carrierIncl38 h x) = carrierIncl38 h (J38 s x) := by
  apply carrierExt38
  funext n
  rw [carrierCoe38_J38, carrierCoe38_incl38, carrierCoe38_incl38, carrierCoe38_J38]


/-! ## Fourier projections `P_N` onto `|n| ≤ N` -/

/-- `(P_N x)_n = x_n` for `|n| ≤ N` and `0` otherwise (v2 l.83), on `h^r`. -/
def Pmap38 (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) : SobolevCarrier38 r :=
  carrierMk38 r (fun n => if n ∈ symmetricModes N then carrierCoe38 r x n else 0)
    (by
      have h := (weightedProjection (sobolevModeWeight r) (symmetricModes N)
        (show WeightedHilbert (sobolevModeWeight r) from x)).2
      have e : ((weightedProjection (sobolevModeWeight r) (symmetricModes N)
          (show WeightedHilbert (sobolevModeWeight r) from x) : WeightedHilbert (sobolevModeWeight r)) :
            ℤ → ℂ) = fun n => if n ∈ symmetricModes N then carrierCoe38 r x n else 0 :=
        funext (weightedProjection_apply _ _ _)
      rw [e] at h
      exact h)

@[simp] theorem carrierCoe38_Pmap38 (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (Pmap38 r N x) n = if n ∈ symmetricModes N then carrierCoe38 r x n else 0 := rfl

theorem norm_Pmap38_le (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) : ‖Pmap38 r N x‖ ≤ ‖x‖ := by
  have h1 := carrier_hasSum_norm_sq38 r (Pmap38 r N x)
  have h2 := carrier_hasSum_norm_sq38 r x
  have hle : ‖Pmap38 r N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    refine hasSum_le (fun n => ?_) h1 h2
    rw [carrierCoe38_Pmap38]
    split_ifs
    · exact le_refl _
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact mul_nonneg (sobolevModeWeight_pos r n).le (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hle

/-- `P_N` as a real-linear map. -/
def projLin38 (r : ℝ) (N : ℕ) : SobolevCarrier38 r →ₗ[ℝ] SobolevCarrier38 r where
  toFun := Pmap38 r N
  map_add' x y := carrierExt38 (funext fun n => by
    show (if n ∈ symmetricModes N then carrierCoe38 r x n + carrierCoe38 r y n else 0) =
      (if n ∈ symmetricModes N then carrierCoe38 r x n else 0) +
        (if n ∈ symmetricModes N then carrierCoe38 r y n else 0)
    split_ifs <;> simp)
  map_smul' c x := carrierExt38 (funext fun n => by
    show (if n ∈ symmetricModes N then (c : ℂ) * carrierCoe38 r x n else 0) =
      (c : ℂ) * (if n ∈ symmetricModes N then carrierCoe38 r x n else 0)
    split_ifs <;> simp)

/-- The Fourier projection `P_N` on `h^r`, as a continuous real-linear map. -/
def projC38 (r : ℝ) (N : ℕ) : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r :=
  (projLin38 r N).mkContinuous 1 (fun x => by
    rw [one_mul]; exact norm_Pmap38_le r N x)

@[simp] theorem carrierCoe38_projC38 (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (projC38 r N x) n = if n ∈ symmetricModes N then carrierCoe38 r x n else 0 := rfl

theorem norm_projC38_le (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) : ‖projC38 r N x‖ ≤ ‖x‖ :=
  norm_Pmap38_le r N x

theorem projC38_idem (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) :
    projC38 r N (projC38 r N x) = projC38 r N x := by
  apply carrierExt38
  funext n
  simp only [carrierCoe38_projC38]
  split_ifs <;> rfl

theorem projC38_mul_self (r : ℝ) (N : ℕ) : projC38 r N * projC38 r N = projC38 r N := by
  apply ContinuousLinearMap.ext
  intro x
  exact projC38_idem r N x

theorem projC38_selfadj (r : ℝ) (N : ℕ) (x y : SobolevCarrier38 r) :
    inner ℝ (projC38 r N x) y = inner ℝ x (projC38 r N y) := by
  have h1 := carrier_inner_hasSum38 r (projC38 r N x) y
  have h2 := carrier_inner_hasSum38 r x (projC38 r N y)
  have : (fun n : ℤ => sobolevModeWeight r n *
      (starRingEnd ℂ (carrierCoe38 r (projC38 r N x) n) * carrierCoe38 r y n).re) =
      fun n => sobolevModeWeight r n *
        (starRingEnd ℂ (carrierCoe38 r x n) * carrierCoe38 r (projC38 r N y) n).re := by
    funext n
    simp only [carrierCoe38_projC38]
    split_ifs <;> simp
  rw [this] at h1
  exact h1.unique h2

theorem projC38_J38 (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) :
    projC38 r N (J38 r x) = J38 r (projC38 r N x) := by
  apply carrierExt38
  funext n
  simp only [carrierCoe38_projC38, carrierCoe38_J38]
  split_ifs <;> simp

theorem projC38_incl {r s : ℝ} (h : r ≤ s) (N : ℕ) (x : SobolevCarrier38 s) :
    carrierIncl38 h (projC38 s N x) = projC38 r N (carrierIncl38 h x) := by
  apply carrierExt38
  funext n
  rw [carrierCoe38_incl38, carrierCoe38_projC38, carrierCoe38_projC38, carrierCoe38_incl38]

theorem norm_sub_projC38_sq (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) :
    ‖x - projC38 r N x‖ ^ 2 = ‖x‖ ^ 2 - ‖projC38 r N x‖ ^ 2 := by
  have h1 : ‖projC38 r N x‖ ^ 2 = inner ℝ x (projC38 r N x) := by
    rw [← real_inner_self_eq_norm_sq, projC38_selfadj, projC38_idem]
  rw [norm_sub_sq_real, ← h1]; ring

/-- `P_N x → x` in `h^r`. -/
theorem tendsto_projC38 (r : ℝ) (x : SobolevCarrier38 r) :
    Tendsto (fun N : ℕ => projC38 r N x) atTop (𝓝 x) := by
  have hf := carrier_hasSum_norm_sq38 r x
  have hP : ∀ N : ℕ, ‖projC38 r N x‖ ^ 2 =
      ∑ n ∈ symmetricModes N, sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2 := by
    intro N
    have h1 := carrier_hasSum_norm_sq38 r (projC38 r N x)
    have h2 : HasSum (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r (projC38 r N x) n‖ ^ 2)
        (∑ n ∈ symmetricModes N, sobolevModeWeight r n * ‖carrierCoe38 r (projC38 r N x) n‖ ^ 2) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by
        rw [carrierCoe38_projC38, ite_eq_right_iff.2 (fun h => absurd h hn)]; simp)
    rw [h1.unique h2]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [carrierCoe38_projC38, ite_eq_left_iff.2 (fun h => absurd hn h)]
  have hlim : Tendsto (fun N : ℕ => ∑ n ∈ symmetricModes N,
      sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) :=
    hf.comp symmetricModes_tendsto
  have hsq : Tendsto (fun N : ℕ => ‖x - projC38 r N x‖ ^ 2) atTop (𝓝 0) := by
    have : (fun N : ℕ => ‖x - projC38 r N x‖ ^ 2) =
        fun N => ‖x‖ ^ 2 - ∑ n ∈ symmetricModes N,
          sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2 := by
      funext N; rw [norm_sub_projC38_sq, hP]
    rw [this]
    have h := (tendsto_const_nhds (x := ‖x‖ ^ 2)).sub hlim
    rwa [sub_self] at h
  have hn : Tendsto (fun N : ℕ => ‖x - projC38 r N x‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at h
    refine h.congr (fun N => ?_)
    simp [Real.sqrt_sq (norm_nonneg _)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [norm_sub_rev] using hn

/-! ## The abstract data of file b at `h⁰` -/

/-- `J`, `P_N` on `h⁰` as an instance of the abstract complex-structure/projection data. -/
def cp38 (N : ℕ) : CplxProj38 (SobolevCarrier38 ((0 : ℕ) : ℝ)) where
  J := J38 _
  P := projC38 _ N
  JJ := J38_mul_J38 _
  adjJ := by
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [neg_apply, inner_neg_left, inner_J38_left]; simp
  PP := projC38_mul_self _ N
  adjP := by
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    exact projC38_selfadj _ N x y
  PJ := by
    apply ContinuousLinearMap.ext
    intro x
    exact projC38_J38 _ N x

theorem cp38_J (N : ℕ) : (cp38 N).J = J38 ((0 : ℕ) : ℝ) := rfl
theorem cp38_P (N : ℕ) : (cp38 N).P = projC38 ((0 : ℕ) : ℝ) N := rfl

/-- `P_N h⁰` is finite-dimensional. -/
instance finiteDimensional_cp38_V (N : ℕ) : FiniteDimensional ℝ (cp38 N).V := by
  let g : SobolevCarrier38 ((0 : ℕ) : ℝ) →ₗ[ℝ] (↥(symmetricModes N) → ℂ) :=
    { toFun := fun x n => carrierCoe38 ((0 : ℕ) : ℝ) x n
      map_add' := fun x y => rfl
      map_smul' := fun c x => by
        funext n
        simp [Complex.real_smul]
        rfl }
  refine Module.Finite.of_injective (g.domRestrict (cp38 N).V) ?_
  intro x y hxy
  apply Subtype.ext
  apply carrierExt38
  funext n
  have hx := ((cp38 N).mem_V_iff x.1).1 x.2
  have hy := ((cp38 N).mem_V_iff y.1).1 y.2
  by_cases hn : n ∈ symmetricModes N
  · exact congrFun hxy ⟨n, hn⟩
  · have e1 : carrierCoe38 ((0 : ℕ) : ℝ) (projC38 ((0 : ℕ) : ℝ) N x.1) n = 0 := by
      rw [carrierCoe38_projC38, ite_eq_right_iff.2 (fun h => absurd h hn)]
    have e2 : carrierCoe38 ((0 : ℕ) : ℝ) (projC38 ((0 : ℕ) : ℝ) N y.1) n = 0 := by
      rw [carrierCoe38_projC38, ite_eq_right_iff.2 (fun h => absurd h hn)]
    have hx' : (cp38 N).P x.1 = x.1 := hx
    have hy' : (cp38 N).P y.1 = y.1 := hy
    rw [cp38_P] at hx' hy'
    rw [← hx', ← hy', e1, e2]

end NlsGge.Birkhoff
