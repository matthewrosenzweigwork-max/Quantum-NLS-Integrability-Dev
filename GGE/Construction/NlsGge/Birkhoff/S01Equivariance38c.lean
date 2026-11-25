import NlsGge.Birkhoff.S01Equivariance38
import NlsGge.Birkhoff.S01Equivariance38b

/-! # S01 (translation equivariance), part c: conditional equivariance over `B : BirkhoffTop38` with `BirkhoffAnalytic38 B {0,1}` and `BirkhoffCanonical38 B`

Route (v2 `D:eq:equivariance`, l.186-196):
1. momentum trace formula: `Σ 2πn I_n(u) = -P(u)`, `P(u) = Σ 2πn |û_n|²` (part b) with
   `action` gives `N(T x) = N(x)` for `x` with `T x` finitely supported (finite-gap fields);
2. `H¹` approximation (continuity of `T⁻¹` on `h¹`, truncations) gives `N ∘ T = N` on `h¹`;
3. differentiate `N ∘ T = N` and use `canonical` plus surjectivity of `DT`: `DT(x) X x = X (T x)`;
4. ODE uniqueness coordinatewise in `h⁰`: `θ ↦ T(S_θ x)` and `θ ↦ S_θ T x` solve the same
   linear ODE `y_n' = i n y_n`;
5. density of `h¹` in `h⁰` and continuity of `T`, `S_θ` extend the identity to all of `h⁰`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations
open scoped Topology

namespace BirkhoffTop38

variable (B : BirkhoffTop38) (hA : BirkhoffAnalytic38 B {0, 1}) (hC : BirkhoffCanonical38 B)

/-! ## Step 1: momentum is preserved on finite-gap fields -/

theorem momSeq38_eq_of_finiteSupport (z : ℤ → ℂ) (hz : {n : ℤ | z n ≠ 0}.Finite) :
    momSeq38 z = momSeq38 (B.Tinv z) := by
  have hz0 : z ∈ seqSobolev38 0 := finiteSupport_mem_seqSobolev38 0 z hz
  obtain ⟨-, hall, hΦ, hfin⟩ := B.finiteSupport_regular_finiteGaps z hz
  set u := B.Φinv z hz0 with hu
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := by simpa using hall 1
  obtain ⟨hs1, hs2, hsum⟩ := actualFirstMoment_fourier38 u hall hfin
  have hact : ∀ n : ℤ, actualGapActionAllE02_38 u n = ‖z n‖ ^ 2 := by
    intro n
    rw [← B.sq_norm_Φ_eq_action u hu1 n, hΦ]
  have hx : fourierSeq38 u = B.Tinv z := B.fourierSeq38_Φinv z hz0
  have hnorm : ∀ n : ℤ, ‖physicalFourier u n‖ = ‖B.Tinv z (-n)‖ := by
    intro n
    rw [← hx, fourierSeq38_apply, norm_neg, neg_neg]
  -- left side
  have hL : ∑' n : ℤ, 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n =
      2 * Real.pi * momSeq38 z := by
    unfold momSeq38
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [hact]; ring
  -- right side
  have hR : ∑' n : ℤ, 2 * Real.pi * (n : ℝ) * ‖physicalFourier u n‖ ^ 2 =
      -(2 * Real.pi * momSeq38 (B.Tinv z)) := by
    unfold momSeq38
    rw [← tsum_mul_left, ← tsum_neg]
    rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => -(2 * Real.pi * ((n : ℝ) * ‖B.Tinv z n‖ ^ 2)))]
    refine tsum_congr (fun n => ?_)
    simp only [Equiv.neg_apply, hnorm, Int.cast_neg]
    ring
  rw [hL, hR] at hsum
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have := neg_neg (2 * Real.pi * momSeq38 (B.Tinv z))
  have h2 : 2 * Real.pi * momSeq38 z = 2 * Real.pi * momSeq38 (B.Tinv z) := by
    rw [hsum, neg_neg]
  exact mul_left_cancel₀ hpi h2


/-! ## Step 2: `H¹` approximation, `N ∘ T = N` on all of `h¹` -/

theorem continuous_momSeq38_carrier :
    Continuous (fun y : SobolevCarrier38 ((1 : ℕ) : ℝ) => momSeq38 (carrierCoe38 _ y)) := by
  have : (fun y : SobolevCarrier38 ((1 : ℕ) : ℝ) => momSeq38 (carrierCoe38 _ y)) =
      fun y => inner ℝ y (momOp38 y) := funext fun y => (inner_self_momOp38 y).symm
  rw [this]
  exact continuous_id.inner momOp38.continuous

/-- Momentum is preserved by `T` on `h¹` (the `H¹` extension of the trace-formula identity). -/
theorem momSeq38_T (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    momSeq38 (B.T x) = momSeq38 x := by
  set y : SobolevCarrier38 ((1 : ℕ) : ℝ) := carrierMk38 _ x hx with hy
  set z := B.TC 1 y with hz
  have hcoe_z : carrierCoe38 _ z = B.T x := rfl
  have hyN : B.TinvC 1 z = y := B.TinvC_TC 1 y
  -- finite-support approximants
  have hzN : ∀ N : ℕ, momSeq38 (carrierCoe38 _ (truncC38 _ N z)) =
      momSeq38 (carrierCoe38 _ (B.TinvC 1 (truncC38 _ N z))) := by
    intro N
    have h := B.momSeq38_eq_of_finiteSupport (carrierCoe38 _ (truncC38 ((1 : ℕ) : ℝ) N z))
      (finiteSupport_truncC38 _ N z)
    exact h
  have hT1 : Filter.Tendsto (fun N : ℕ => momSeq38 (carrierCoe38 _ (truncC38 ((1 : ℕ) : ℝ) N z)))
      Filter.atTop (𝓝 (momSeq38 (carrierCoe38 _ z))) :=
    ((continuous_momSeq38_carrier).tendsto z).comp (tendsto_truncC38 _ z)
  have hT2 : Filter.Tendsto (fun N : ℕ =>
      momSeq38 (carrierCoe38 _ (B.TinvC 1 (truncC38 ((1 : ℕ) : ℝ) N z))))
      Filter.atTop (𝓝 (momSeq38 (carrierCoe38 _ y))) := by
    have h := ((B.continuous_TinvC 1).tendsto z).comp (tendsto_truncC38 _ z)
    rw [hyN] at h
    exact ((continuous_momSeq38_carrier).tendsto y).comp h
  have := tendsto_nhds_unique (hT1.congr hzN) hT2
  rw [← hcoe_z]
  exact this


/-! ## Step 3: `DT(x) X x = X (T x)` -/

include hA in
/-- `DT(x)` is onto on every carrier `h^m` (chain rule on `T ∘ T⁻¹ = id`). -/
theorem exists_fderiv_TC_preimage (m : ℕ) (hm : m ∈ ({0, 1} : Set ℕ)) (x e : SobolevCarrier38 (m : ℝ)) :
    ∃ ξ, fderiv ℝ (B.TC m) x ξ = e := by
  set D := fderiv ℝ (B.TinvC m) (B.TC m x) with hD
  have h1 : HasFDerivAt (B.TinvC m) D (B.TC m x) :=
    (hA.analyticOnNhd_TinvC hm _ trivial).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (B.TC m) (fderiv ℝ (B.TC m) x) (B.TinvC m (B.TC m x)) := by
    rw [B.TinvC_TC]
    exact (hA.analyticOnNhd_TC hm _ trivial).differentiableAt.hasFDerivAt
  have h3 := h2.comp (B.TC m x) h1
  have h4 : (B.TC m) ∘ (B.TinvC m) = id := funext (B.TC_TinvC m)
  rw [h4] at h3
  have h5 := h3.unique (hasFDerivAt_id (B.TC m x))
  refine ⟨D e, ?_⟩
  have := congrArg (fun L => L e) h5
  simpa using this

theorem momSeq38_TC (y : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    momSeq38 (carrierCoe38 _ (B.TC 1 y)) = momSeq38 (carrierCoe38 _ y) :=
  B.momSeq38_T _ (carrierCoe38_mem _ y)


theorem finiteSupport_single38 (m : ℤ) (u : ℂ) : {n : ℤ | (Pi.single m u : ℤ → ℂ) n ≠ 0}.Finite :=
  (Set.finite_singleton m).subset (fun n hn => by
    by_contra h
    exact hn (by simp [show n ≠ m from h]))

theorem carrierCoe38_mk38' (y : ℤ → ℂ) (hy : y ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    carrierCoe38 ((1 : ℕ) : ℝ) (carrierMk38 ((1 : ℕ) : ℝ) y hy) = y := carrierCoe38_mk _ y hy

theorem carrierIncl38_mk_zero (y : ℤ → ℂ) (hy : y ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    carrierIncl38 (Nat.cast_le.2 (by norm_num) : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
        (carrierMk38 ((1 : ℕ) : ℝ) y hy) = carrierZero38 y (mem_zero_of_mem_one38 hy) :=
  carrierExt38 ((carrierCoe38_incl38 _ _).trans
    ((carrierCoe38_mk38' y hy).trans (carrierCoe38_carrierZero38 y _).symm))

include hA hC in
/-- The pairing identity behind `fderiv_T_gen38`, for `ξ ∈ h¹`. -/
theorem symplectic_fderiv_gen38 (y : ℤ → ℂ) (hy : y ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (ξ : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    stdSymplectic38
        (carrierCoe38 _ (fderiv ℝ (B.TC 0) (carrierZero38 y (mem_zero_of_mem_one38 hy))
          (carrierZero38 (genSeq38 y) (genSeq38_mem_zero hy))))
        (carrierCoe38 _ (fderiv ℝ (B.TC 1) (carrierMk38 _ y hy) ξ)) =
      stdSymplectic38 (genSeq38 (B.T y))
        (carrierCoe38 _ (fderiv ℝ (B.TC 1) (carrierMk38 _ y hy) ξ)) := by
  have h01 : ((0 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) := Nat.cast_le.2 (by norm_num)
  have ha := momBil_fderiv38 (B.TC 1) (carrierMk38 _ y hy) ξ _
    ((hA.analyticOnNhd_TC (by simp) _ trivial).differentiableAt.hasFDerivAt) B.momSeq38_TC
  have hb : stdSymplectic38
      (carrierCoe38 _ (fderiv ℝ (B.TC 0) (carrierZero38 y (mem_zero_of_mem_one38 hy))
        (carrierZero38 (genSeq38 y) (genSeq38_mem_zero hy))))
      (carrierCoe38 _ (fderiv ℝ (B.TC 0) (carrierZero38 y (mem_zero_of_mem_one38 hy))
        (carrierIncl38 h01 ξ))) =
      stdSymplectic38 (carrierCoe38 _ (carrierZero38 (genSeq38 y) (genSeq38_mem_zero hy)))
        (carrierCoe38 _ (carrierIncl38 h01 ξ)) :=
    hC.canonical (carrierZero38 y (mem_zero_of_mem_one38 hy))
      (carrierZero38 (genSeq38 y) (genSeq38_mem_zero hy)) (carrierIncl38 h01 ξ)
  have hc := hA.fderiv_TC_compat_coe 0 1 (by simp) (by simp) (by norm_num) (carrierMk38 _ y hy) ξ
  rw [carrierIncl38_mk_zero] at hc
  rw [hc] at hb
  rw [carrierCoe38_incl38] at hb
  have e1 : carrierCoe38 ((0 : ℕ) : ℝ) (carrierZero38 (genSeq38 y) (genSeq38_mem_zero hy)) =
      genSeq38 y := rfl
  rw [e1] at hb
  refine hb.trans ?_
  rw [stdSymplectic38_gen_left, stdSymplectic38_gen_left]
  congr 1
  exact ha.symm


include hA hC in
/-- **`DT(x) X x = X (T x)`** for `x ∈ h¹`: the derivative of `T` in `h⁰` intertwines the
momentum generator `X` (from `N ∘ T = N`, `canonical`, and surjectivity of `DT` on `h¹`). -/
theorem fderiv_T_gen38 (y : ℤ → ℂ) (hy : y ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    carrierCoe38 ((0 : ℕ) : ℝ)
        (fderiv ℝ (B.TC 0) (carrierZero38 y (mem_zero_of_mem_one38 hy))
          (carrierZero38 (genSeq38 y) (genSeq38_mem_zero hy))) = genSeq38 (B.T y) := by
  have key2 : ∀ e : SobolevCarrier38 ((1 : ℕ) : ℝ),
      stdSymplectic38 (carrierCoe38 _ (fderiv ℝ (B.TC 0) (carrierZero38 y (mem_zero_of_mem_one38 hy))
          (carrierZero38 (genSeq38 y) (genSeq38_mem_zero hy)))) (carrierCoe38 _ e) =
        stdSymplectic38 (genSeq38 (B.T y)) (carrierCoe38 _ e) := by
    intro e
    obtain ⟨ξ, hξ⟩ := B.exists_fderiv_TC_preimage hA 1 (by simp) (carrierMk38 _ y hy) e
    rw [← hξ]
    exact B.symplectic_fderiv_gen38 hA hC y hy ξ
  have key3 : ∀ (m : ℤ) (u : ℂ),
      (starRingEnd ℂ (carrierCoe38 _ (fderiv ℝ (B.TC 0) (carrierZero38 y (mem_zero_of_mem_one38 hy))
          (carrierZero38 (genSeq38 y) (genSeq38_mem_zero hy))) m) * u).im =
        (starRingEnd ℂ (genSeq38 (B.T y) m) * u).im := by
    intro m u
    have := key2 (carrierMk38 _ (Pi.single m u)
      (finiteSupport_mem_seqSobolev38 _ _ (finiteSupport_single38 m u)))
    simpa only [carrierCoe38_mk, stdSymplectic38_single] using this
  funext m
  apply Complex.ext
  · have h1 := key3 m Complex.I
    simpa using h1
  · have h1 := key3 m 1
    simpa using h1


/-! ## Step 4: ODE uniqueness, equivariance on `h¹` -/

include hA hC in
/-- Coordinates of `θ ↦ T(S_θ x)` solve `y_n' = i n y_n` for `x ∈ h¹`. -/
theorem hasDerivAt_T_rot38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (n : ℤ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => B.T (rotSeq38 t x) n)
      (Complex.I * (n : ℂ) * B.T (rotSeq38 θ x) n) θ := by
  have hγ := hasDerivAt_rotCurve38 x hx θ
  have hT : HasFDerivAt (B.TC 0)
      (fderiv ℝ (B.TC 0) (carrierZero38 (rotSeq38 θ x) (mem_zero_of_mem_one38 (rotSeq38_mem _ θ hx))))
      (carrierZero38 (rotSeq38 θ x) (mem_zero_of_mem_one38 (rotSeq38_mem _ θ hx))) :=
    (hA.analyticOnNhd_TC (by simp) _ trivial).differentiableAt.hasFDerivAt
  have hc := hT.comp_hasDerivAt θ hγ
  have hco := (coordC38 ((0 : ℕ) : ℝ) n).hasFDerivAt.comp_hasDerivAt θ hc
  have hval := B.fderiv_T_gen38 hA hC (rotSeq38 θ x) (rotSeq38_mem _ θ hx)
  refine HasDerivAt.congr_deriv hco ?_
  simp only [coordC38_apply]
  rw [hval]
  rfl

include hA hC in
theorem rot_equivariance_h1_coord (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (n : ℤ)
    (θ : ℝ) : B.T (rotSeq38 θ x) n = rotPhase38 θ n * B.T x n := by
  set g : ℝ → ℂ := fun t => B.T (rotSeq38 t x) n with hg
  set F : ℝ → ℂ := fun t => rotPhase38 (-t) n * g t with hF
  have hderF : ∀ t, HasDerivAt F 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => rotPhase38 (-s) n)
        (Complex.I * (n : ℂ) * rotPhase38 (-t) n * (-1)) t := by
      have := (hasDerivAt_rotPhase38 n (-t)).scomp t (hasDerivAt_neg t)
      refine HasDerivAt.congr_deriv this ?_
      simp [mul_comm]
    have h2 := h1.mul (B.hasDerivAt_T_rot38 hA hC x hx n t)
    refine HasDerivAt.congr_deriv h2 ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hderF t).differentiableAt)
    (fun t => (hderF t).deriv) θ 0
  have h0 : F 0 = B.T x n := by
    simp only [hF, hg, neg_zero, rotPhase38_zero, one_mul, rotSeq38_zero]
  have hθ : rotPhase38 (-θ) n * B.T (rotSeq38 θ x) n = B.T x n := by
    have := hconst; rw [h0] at this; exact this
  have hinv : rotPhase38 θ n * rotPhase38 (-θ) n = 1 := by
    rw [← rotPhase38_add, add_neg_cancel, rotPhase38_zero]
  calc B.T (rotSeq38 θ x) n = (rotPhase38 θ n * rotPhase38 (-θ) n) * B.T (rotSeq38 θ x) n := by
        rw [hinv, one_mul]
    _ = rotPhase38 θ n * (rotPhase38 (-θ) n * B.T (rotSeq38 θ x) n) := by ring
    _ = rotPhase38 θ n * B.T x n := by rw [hθ]

include hA hC in
/-- **Translation equivariance on `h¹`** (v2 `D:eq:equivariance`, `H¹` fields):
`T S_θ x = S_θ T x` for `x ∈ h¹`. -/
theorem T_rotSeq38_h1 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (θ : ℝ) :
    B.T (rotSeq38 θ x) = rotSeq38 θ (B.T x) :=
  funext fun n => B.rot_equivariance_h1_coord hA hC x hx n θ


/-! ## Step 5: extension to `h⁰` by density and continuity -/

include hA hC in
theorem rot_T_commute_carrier38 (θ : ℝ) (y : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    B.TC 0 (rotC38 ((0 : ℕ) : ℝ) θ y) = rotC38 ((0 : ℕ) : ℝ) θ (B.TC 0 y) := by
  have hN : ∀ N : ℕ, B.TC 0 (rotC38 ((0 : ℕ) : ℝ) θ (truncC38 ((0 : ℕ) : ℝ) N y)) =
      rotC38 ((0 : ℕ) : ℝ) θ (B.TC 0 (truncC38 ((0 : ℕ) : ℝ) N y)) := by
    intro N
    have hfs := finiteSupport_truncC38 ((0 : ℕ) : ℝ) N y
    have hmem : carrierCoe38 ((0 : ℕ) : ℝ) (truncC38 ((0 : ℕ) : ℝ) N y) ∈
        seqSobolev38 ((1 : ℕ) : ℝ) := finiteSupport_mem_seqSobolev38 _ _ hfs
    apply carrierExt38
    rw [rotC38_coe, TC_coe, TC_coe, rotC38_coe]
    show B.T (rotSeq38 θ (carrierCoe38 ((0 : ℕ) : ℝ) (truncC38 ((0 : ℕ) : ℝ) N y))) =
      rotSeq38 θ (B.T (carrierCoe38 ((0 : ℕ) : ℝ) (truncC38 ((0 : ℕ) : ℝ) N y)))
    exact B.T_rotSeq38_h1 hA hC _ hmem θ
  have hy := tendsto_truncC38 ((0 : ℕ) : ℝ) y
  have h1 : Filter.Tendsto (fun N : ℕ => B.TC 0 (rotC38 ((0 : ℕ) : ℝ) θ (truncC38 ((0 : ℕ) : ℝ) N y)))
      Filter.atTop (𝓝 (B.TC 0 (rotC38 ((0 : ℕ) : ℝ) θ y))) :=
    ((B.continuous_TC 0).tendsto _).comp (((continuous_rotC38 _ θ).tendsto y).comp hy)
  have h2 : Filter.Tendsto (fun N : ℕ => rotC38 ((0 : ℕ) : ℝ) θ (B.TC 0 (truncC38 ((0 : ℕ) : ℝ) N y)))
      Filter.atTop (𝓝 (rotC38 ((0 : ℕ) : ℝ) θ (B.TC 0 y))) :=
    ((continuous_rotC38 _ θ).tendsto _).comp (((B.continuous_TC 0).tendsto y).comp hy)
  exact tendsto_nhds_unique (h1.congr hN) h2

include hA hC in
/-- **Translation equivariance of the Birkhoff transformation on `h⁰`** (v2 `D:eq:equivariance`):
`T S_θ x = S_θ T x` for every `x ∈ h⁰`, with `(S_θ x)_n = e^{inθ} x_n`. -/
theorem T_rotSeq38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) (θ : ℝ) :
    B.T (rotSeq38 θ x) = rotSeq38 θ (B.T x) := by
  have h := congrArg (carrierCoe38 ((0 : ℕ) : ℝ)) (B.rot_T_commute_carrier38 hA hC θ (carrierZero38 x hx))
  exact h

include hA hC in
/-- The same statement for the Birkhoff coordinates `Φ = T ∘ 𝓕` of a physical field
(`𝓕 u ∈ h⁰` always; for `u ∈ H¹` this is exactly v2's `H¹` statement). -/
theorem T_rotSeq38_fourier (u : PhysicalL2) (θ : ℝ) :
    B.T (rotSeq38 θ (fourierSeq38 u)) = rotSeq38 θ (B.Φ u) :=
  B.T_rotSeq38 hA hC _ (fourierSeq38_mem_zero u) θ

include hA hC in
/-- The inverse commutes with `S_θ` as well. -/
theorem Tinv_rotSeq38 (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) (θ : ℝ) :
    B.Tinv (rotSeq38 θ z) = rotSeq38 θ (B.Tinv z) := by
  have hrz : rotSeq38 θ z ∈ seqSobolev38 0 := rotSeq38_mem 0 θ hz
  have h1 := B.T_rotSeq38 hA hC (B.Tinv z) (B.Tinv_mem_zero hz) θ
  rw [B.right_inv z hz] at h1
  have h2 := congrArg B.Tinv h1
  rw [B.left_inv _ (rotSeq38_mem 0 θ (B.Tinv_mem_zero hz))] at h2
  exact h2.symm

end BirkhoffTop38

namespace BirkhoffInput38

variable (B : BirkhoffInput38)

/-! Full-input forms of the S01 headlines (all hypotheses supplied by `B.toAnalytic` and
`B.toCanonical`), keeping the pre-split names for the consumers that keep `BirkhoffInput38`. -/

theorem T_rotSeq38_h1 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (θ : ℝ) :
    B.T (rotSeq38 θ x) = rotSeq38 θ (B.T x) :=
  B.toBirkhoffTop38.T_rotSeq38_h1 (B.toAnalytic.mono (Set.subset_univ _)) B.toCanonical x hx θ

theorem T_rotSeq38 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) (θ : ℝ) :
    B.T (rotSeq38 θ x) = rotSeq38 θ (B.T x) :=
  B.toBirkhoffTop38.T_rotSeq38 (B.toAnalytic.mono (Set.subset_univ _)) B.toCanonical x hx θ

theorem T_rotSeq38_fourier (u : PhysicalL2) (θ : ℝ) :
    B.T (rotSeq38 θ (fourierSeq38 u)) = rotSeq38 θ (B.Φ u) :=
  B.toBirkhoffTop38.T_rotSeq38_fourier (B.toAnalytic.mono (Set.subset_univ _)) B.toCanonical u θ

theorem Tinv_rotSeq38 (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) (θ : ℝ) :
    B.Tinv (rotSeq38 θ z) = rotSeq38 θ (B.Tinv z) :=
  B.toBirkhoffTop38.Tinv_rotSeq38 (B.toAnalytic.mono (Set.subset_univ _)) B.toCanonical z hz θ

end BirkhoffInput38

end NlsGge.Birkhoff
