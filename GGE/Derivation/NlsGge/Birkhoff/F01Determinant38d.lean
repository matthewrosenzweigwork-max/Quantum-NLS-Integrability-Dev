import NlsGge.Birkhoff.F01Determinant38c

/-! # F01 (wave A3), file d: F01.04-F01.07 (compression, discarded block, determinants → 1, uniformity)

Plan and status: `NlsGge/Birkhoff/F01_PLAN.md`.  Conditional on `(B : BirkhoffInput38)`,
`(O : OneSmoothingInput38 B)`; E01/E04 stay open.

Notation (v2 `lem:determinants`): `x ∈ h¹`, `x_N = P_N x ∈ h¹` (`projC38 1 N x`), the base point in `h⁰` is
`ι x_N`; `L = L(ι x_N) = DT(ι x_N)`; `V_N = P_N h⁰ = (cp38 N).V`;
* `L_N = P_N L P_N |_{V_N}`  : `LNmap`,
* `C_N = (1−P_N) B(x_N) P_N` : `CNop` (an operator of `h⁰`; restricted to `V_N` it is v2's `C_N`),
* `J_N C_N^* J_{>N} C_N`      : `MNmap` (the endomorphism of `V_N` induced by `J ∘ C_N^* ∘ J ∘ C_N`).
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Analysis.RegularizedDeterminant
open scoped InnerProductSpace ENNReal
open Filter Topology

namespace NlsGge.Birkhoff

/-! ## Elementary facts about `P_N` and `1 − P_N` -/

/-- `1 − P_N`. -/
def compl38 (r : ℝ) (N : ℕ) : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r :=
  ContinuousLinearMap.id ℝ _ - projC38 r N

theorem compl38_apply (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) :
    compl38 r N x = x - projC38 r N x := rfl

theorem norm_compl38_apply_le (r : ℝ) (N : ℕ) (x : SobolevCarrier38 r) :
    ‖compl38 r N x‖ ≤ ‖x‖ := by
  rw [compl38_apply]
  have h := norm_sub_projC38_sq r N x
  have h2 : ‖x - projC38 r N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ‖projC38 r N x‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem opNorm_compl38_le (r : ℝ) (N : ℕ) : ‖compl38 r N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul]; exact norm_compl38_apply_le r N x)

theorem opNorm_projC38_le (r : ℝ) (N : ℕ) : ‖projC38 r N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul]; exact norm_projC38_le r N x)

theorem tendsto_compl38 (r : ℝ) (x : SobolevCarrier38 r) :
    Tendsto (fun N : ℕ => compl38 r N x) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := x)).sub (tendsto_projC38 r x)
  rw [sub_self] at h
  exact h


/-! ## F01.04-F01.06: the objects of `lem:determinants` and the determinant identity -/

/-- The base point `x_N = P_N x`, as an element of `h⁰` (`x ∈ h¹`). -/
def baseN38 (x : H1_38) (N : ℕ) : H0_38 := i10_38 (projC38 ((1 : ℕ) : ℝ) N x)

namespace BirkhoffInput38

variable (B : BirkhoffInput38)

/-- `L(x_N) = DT(x_N)`. -/
def LxN (x : H1_38) (N : ℕ) : H0_38 →L[ℝ] H0_38 := B.Lop (baseN38 x N)

/-- `L_N = P_N L(x_N) P_N |_{P_N h⁰}`, a real linear endomorphism of `V_N = P_N h⁰`. -/
def LNmap (x : H1_38) (N : ℕ) : (cp38 N).V →ₗ[ℝ] (cp38 N).V :=
  (cp38 N).resRange ((cp38 N).Lt (B.LxN x N)) ((cp38 N).Lt_mem _)

/-- `C_N = (1 − P_N) B(x_N) P_N`, as an operator of `h⁰`. -/
def CNop (x : H1_38) (N : ℕ) : H0_38 →L[ℝ] H0_38 :=
  (compl38 ((0 : ℕ) : ℝ) N).comp ((B.Bop (baseN38 x N)).comp (projC38 ((0 : ℕ) : ℝ) N))

theorem CNop_eq (x : H1_38) (N : ℕ) : B.CNop x N = (cp38 N).C (B.LxN x N) := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- `J_N C_N^* J_{>N} C_N`, the endomorphism of `V_N` induced by `J ∘ C_N^* ∘ J ∘ C_N`. -/
def MNmap (x : H1_38) (N : ℕ) : (cp38 N).V →ₗ[ℝ] (cp38 N).V :=
  (cp38 N).resRange ((cp38 N).M (B.LxN x N)) ((cp38 N).M_mem _)

theorem MNmap_apply (x : H1_38) (N : ℕ) (u : (cp38 N).V) :
    ((B.MNmap x N u : (cp38 N).V) : H0_38) =
      J38 _ (ContinuousLinearMap.adjoint (B.CNop x N) (J38 _ (B.CNop x N (u : H0_38)))) := by
  rw [B.CNop_eq]
  rfl

/-- `det L_N`. -/
def detLN (x : H1_38) (N : ℕ) : ℝ := LinearMap.det (B.LNmap x N)

/-- `det (Id + J_N C_N^* J_{>N} C_N)`. -/
def detMN (x : H1_38) (N : ℕ) : ℝ := LinearMap.det (1 + B.MNmap x N)

theorem LxN_form (x : H1_38) (N : ℕ) (u v : H0_38) :
    inner ℝ ((cp38 N).J (B.LxN x N u)) (B.LxN x N v) = inner ℝ ((cp38 N).J u) v :=
  B.Lop_form _ u v

/-- **F01.04 (pointwise).** Compression of the canonical form to `V_N`:
`⟪J L_N u, L_N v⟫ = ⟪J u, v⟫ − ⟪J C_N u, C_N v⟫` for `u, v ∈ V_N`. -/
theorem F01_04_compress (x : H1_38) (N : ℕ) (u v : H0_38) (hu : u ∈ (cp38 N).V)
    (hv : v ∈ (cp38 N).V) :
    inner ℝ (J38 _ (projC38 _ N (B.LxN x N u))) (projC38 _ N (B.LxN x N v)) =
      inner ℝ (J38 _ u) v - inner ℝ (J38 _ (B.CNop x N u)) (B.CNop x N v) := by
  have h := (cp38 N).compress_form (B.LxN x N) (B.LxN_form x N) u v hu hv
  rw [B.CNop_eq]
  have e1 : ∀ w ∈ (cp38 N).V, (cp38 N).Lt (B.LxN x N) w = projC38 _ N (B.LxN x N w) := by
    intro w hw
    rw [CplxProj38.Lt_apply]
    rw [((cp38 N).mem_V_iff w).1 hw]
    rfl
  rw [e1 u hu, e1 v hv] at h
  exact h

/-- **F01.04 (operator form on `V_N`).** `L_N^* J_N L_N = J_N − C_N^* J_{>N} C_N`. -/
theorem F01_04_operator (x : H1_38) (N : ℕ) :
    LinearMap.adjoint (B.LNmap x N) * (cp38 N).JV * B.LNmap x N =
      (cp38 N).JV - (cp38 N).resRange ((cp38 N).Qop (B.LxN x N)) ((cp38 N).Qop_mem _) :=
  (cp38 N).adjoint_JV_T _ (B.LxN_form x N)

/-- **F01.06 (identity part of eq. ordinarydet).**
`|det L_N|² = det (Id + J_N C_N^* J_{>N} C_N)`. -/
theorem F01_06_identity (x : H1_38) (N : ℕ) : |B.detLN x N| ^ 2 = B.detMN x N := by
  rw [sq_abs]
  exact (cp38 N).sq_det_Lt _ (B.LxN_form x N)

/-! ## F01.05: the discarded block, in Hilbert-Schmidt norm -/

variable (O : OneSmoothingInput38 B)

/-- `C_N` as a Hilbert-Schmidt operator of `h⁰` (HS-ness comes from `Bop_isHS`). -/
def cHS (x : H1_38) (N : ℕ) : HilbertSchmidt H0_38 H0_38 :=
  HilbertSchmidt.postcompose (compl38 ((0 : ℕ) : ℝ) N)
    (HilbertSchmidt.precompose (B.BHS O (projC38 ((1 : ℕ) : ℝ) N x)) (projC38 ((0 : ℕ) : ℝ) N))

theorem toCLM_cHS (x : H1_38) (N : ℕ) : HilbertSchmidt.toCLM (B.cHS O x N) = B.CNop x N := by
  simp only [cHS, HilbertSchmidt.toCLM_postcompose, HilbertSchmidt.toCLM_precompose, toCLM_BHS,
    CNop, baseN38]

theorem postcompose_sub38 {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : F →L[ℝ] G) (S T : HilbertSchmidt E F) :
    HilbertSchmidt.postcompose A (S - T) =
      HilbertSchmidt.postcompose A S - HilbertSchmidt.postcompose A T := by
  apply HilbertSchmidt.ext
  intro v
  simp

theorem precompose_sub38 {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : E →L[ℝ] F) (S T : HilbertSchmidt F G) :
    HilbertSchmidt.precompose (S - T) A =
      HilbertSchmidt.precompose S A - HilbertSchmidt.precompose T A := by
  apply HilbertSchmidt.ext
  intro v
  simp

/-- **F01.05.** `‖C_N‖_HS ≤ ‖B(x_N) − B(x)‖_HS + ‖(1 − P_N) B(x)‖_HS`. -/
theorem norm_cHS_le (x : H1_38) (N : ℕ) :
    ‖B.cHS O x N‖ ≤ ‖B.BHS O (projC38 ((1 : ℕ) : ℝ) N x) - B.BHS O x‖ +
      ‖HilbertSchmidt.postcompose (compl38 ((0 : ℕ) : ℝ) N) (B.BHS O x)‖ := by
  set P := projC38 ((0 : ℕ) : ℝ) N
  set Q := compl38 ((0 : ℕ) : ℝ) N
  have e : B.cHS O x N =
      HilbertSchmidt.postcompose Q (HilbertSchmidt.precompose
        (B.BHS O (projC38 ((1 : ℕ) : ℝ) N x) - B.BHS O x) P) +
      HilbertSchmidt.precompose (HilbertSchmidt.postcompose Q (B.BHS O x)) P := by
    apply HilbertSchmidt.ext
    intro v
    simp [cHS, P, Q]
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (HilbertSchmidt.norm_postcompose_le _ _).trans ?_
    refine (mul_le_mul (opNorm_compl38_le _ N) (HilbertSchmidt.norm_precompose_le _ _)
      (norm_nonneg _) zero_le_one).trans ?_
    rw [one_mul]
    calc _ ≤ ‖B.BHS O (projC38 ((1 : ℕ) : ℝ) N x) - B.BHS O x‖ * 1 :=
          mul_le_mul_of_nonneg_left (opNorm_projC38_le _ N) (norm_nonneg _)
      _ = _ := mul_one _
  · refine (HilbertSchmidt.norm_precompose_le _ _).trans ?_
    calc _ ≤ ‖HilbertSchmidt.postcompose Q (B.BHS O x)‖ * 1 :=
          mul_le_mul_of_nonneg_left (opNorm_projC38_le _ N) (norm_nonneg _)
      _ = _ := mul_one _

theorem tendsto_norm_postcompose_compl38 (T : HilbertSchmidt H0_38 H0_38) :
    Tendsto (fun N : ℕ => ‖HilbertSchmidt.postcompose (compl38 ((0 : ℕ) : ℝ) N) T‖) atTop (𝓝 0) := by
  have h := HilbertSchmidt.tendsto_postcompose_zero atTop
    (fun N : ℕ => compl38 ((0 : ℕ) : ℝ) N) T 1 zero_le_one
    (Eventually.of_forall (fun N => opNorm_compl38_le _ N)) (tendsto_compl38 _)
  simpa using h.norm

/-- `‖C_N‖_HS → 0` for every `x ∈ h¹`. -/
theorem tendsto_norm_cHS (x : H1_38) :
    Tendsto (fun N : ℕ => ‖B.cHS O x N‖) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ‖B.BHS O (projC38 ((1 : ℕ) : ℝ) N x) - B.BHS O x‖) atTop (𝓝 0) := by
    have := ((B.continuous_BHS O).tendsto x).comp (tendsto_projC38 ((1 : ℕ) : ℝ) x)
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => B.norm_cHS_le O x N)
    (by simpa using h1.add (tendsto_norm_postcompose_compl38 (B.BHS O x)))

/-- **F01.05, quadratic product.** `‖J C_N^*J C_N‖_HS ≤ ‖C_N‖²_HS` and `|tr| ≤ ‖C_N‖²_HS`
(replacing v2's trace-norm bound; see `F01_PLAN.md`, departure D2). -/
theorem F01_05_quadratic (x : H1_38) (N : ℕ) :
    ‖(cp38 N).Mhs (B.cHS O x N)‖ ≤ ‖B.cHS O x N‖ ^ 2 ∧
      |LinearMap.trace ℝ (cp38 N).V (B.MNmap x N)| ≤ ‖B.cHS O x N‖ ^ 2 :=
  ⟨(cp38 N).norm_Mhs_le _,
    (cp38 N).abs_trace_M_le (B.LxN x N) _ (by rw [B.toCLM_cHS O, B.CNop_eq])⟩

/-! ## F01.06: `det → 1` -/

/-- The quantitative form of eq. ordinarydet: `|det(Id + J_N C_N^*J C_N) − 1| ≤ detErr38 (‖C_N‖²)`. -/
theorem abs_detMN_sub_one_le (x : H1_38) (N : ℕ) :
    |B.detMN x N - 1| ≤ detErr38 (‖B.cHS O x N‖ ^ 2) :=
  (cp38 N).abs_det_sub_one_le (B.LxN x N) (B.cHS O x N) (by rw [B.toCLM_cHS O, B.CNop_eq])

include O in
/-- **F01.06.** `det (Id + J_N C_N^* J_{>N} C_N) → 1` as `N → ∞`, for every `x ∈ h¹`. -/
theorem tendsto_detMN (x : H1_38) : Tendsto (fun N : ℕ => B.detMN x N) atTop (𝓝 1) := by
  have h0 : Tendsto (fun N : ℕ => ‖B.cHS O x N‖ ^ 2) atTop (𝓝 0) := by
    simpa using (B.tendsto_norm_cHS O x).pow 2
  have h1 : Tendsto (fun N : ℕ => detErr38 (‖B.cHS O x N‖ ^ 2)) atTop (𝓝 0) := by
    have := (continuous_detErr38.tendsto 0).comp h0
    rw [detErr38_zero] at this
    exact this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun N => norm_nonneg _)
    (fun N => by rw [Real.norm_eq_abs]; exact B.abs_detMN_sub_one_le O x N) h1

include O in
/-- `|det L_N|² → 1` (v2 eq. ordinarydet). -/
theorem tendsto_sq_detLN (x : H1_38) :
    Tendsto (fun N : ℕ => |B.detLN x N| ^ 2) atTop (𝓝 1) := by
  have := B.tendsto_detMN O x
  refine this.congr (fun N => ?_)
  exact (B.F01_06_identity x N).symm

/-! ## F01.07: uniformity on compact subsets of `h¹` -/

theorem eventually_dist_proj_lt38 {K : Set H1_38} (hK : IsCompact K) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ K, dist (projC38 ((1 : ℕ) : ℝ) N x) x < ε := by
  intro ε hε
  have h := eventually_abs_lt_of_lipschitz38 hK
    (F := fun (N : ℕ) (x : H1_38) => ‖x - projC38 ((1 : ℕ) : ℝ) N x‖)
    (fun N x y => by
      rw [dist_eq_norm]
      refine (abs_norm_sub_norm_le _ _).trans ?_
      have e : (x - projC38 ((1 : ℕ) : ℝ) N x) - (y - projC38 ((1 : ℕ) : ℝ) N y) =
          compl38 ((1 : ℕ) : ℝ) N (x - y) := by
        rw [compl38_apply, map_sub]; abel
      rw [e]
      exact norm_compl38_apply_le _ N _)
    (fun x => by
      have := (tendsto_projC38 ((1 : ℕ) : ℝ) x)
      rw [tendsto_iff_norm_sub_tendsto_zero] at this
      simpa [norm_sub_rev] using this) ε hε
  filter_upwards [h] with N hN x hx
  have := hN x hx
  rwa [abs_of_nonneg (norm_nonneg _), ← dist_eq_norm, dist_comm] at this

theorem eventually_norm_postcompose_lt38 {K : Set (HilbertSchmidt H0_38 H0_38)} (hK : IsCompact K) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ Y ∈ K,
      ‖HilbertSchmidt.postcompose (compl38 ((0 : ℕ) : ℝ) N) Y‖ < ε := by
  intro ε hε
  have h := eventually_abs_lt_of_lipschitz38 hK
    (F := fun (N : ℕ) (Y : HilbertSchmidt H0_38 H0_38) =>
      ‖HilbertSchmidt.postcompose (compl38 ((0 : ℕ) : ℝ) N) Y‖)
    (fun N Y Z => by
      rw [dist_eq_norm]
      refine (abs_norm_sub_norm_le _ _).trans ?_
      rw [← postcompose_sub38]
      refine (HilbertSchmidt.norm_postcompose_le _ _).trans ?_
      calc _ ≤ 1 * ‖Y - Z‖ := mul_le_mul_of_nonneg_right (opNorm_compl38_le _ N) (norm_nonneg _)
        _ = _ := one_mul _)
    (fun Y => tendsto_norm_postcompose_compl38 Y) ε hε
  filter_upwards [h] with N hN Y hY
  have := hN Y hY
  rwa [abs_of_nonneg (norm_nonneg _)] at this

include O in
theorem eventually_norm_cHS_lt {K : Set H1_38} (hK : IsCompact K) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ K, ‖B.cHS O x N‖ < ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hA := eventually_dist_comp_lt38 hK (B.continuous_BHS O) (φ := fun N x => projC38 ((1 : ℕ) : ℝ) N x)
    (eventually_dist_proj_lt38 hK) (ε / 2) hε2
  have hB := eventually_norm_postcompose_lt38 (hK.image (B.continuous_BHS O)) (ε / 2) hε2
  filter_upwards [hA, hB] with N hNA hNB x hx
  have h1 := hNA x hx
  have h2 := hNB (B.BHS O x) ⟨x, hx, rfl⟩
  rw [dist_eq_norm] at h1
  have := B.norm_cHS_le O x N
  linarith

include O in
/-- **F01.07.** `|det L_N|² → 1` uniformly for base points `x` in a compact subset of `h¹`
(the quantitative form: `det(Id + J_N C_N^* J_{>N} C_N) → 1` uniformly). -/
theorem tendstoUniformlyOn_detMN {K : Set H1_38} (hK : IsCompact K) :
    TendstoUniformlyOn (fun (N : ℕ) (x : H1_38) => B.detMN x N) (fun _ => (1 : ℝ)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 continuous_detErr38.continuousAt ε hε
  set η : ℝ := min 1 (δ / 2) with hη
  have hη0 : 0 < η := lt_min one_pos (half_pos hδ)
  filter_upwards [B.eventually_norm_cHS_lt O hK η hη0] with N hN x hx
  have hc := hN x hx
  have hc0 := norm_nonneg (B.cHS O x N)
  have h1 : ‖B.cHS O x N‖ < 1 := hc.trans_le (min_le_left _ _)
  have h2 : ‖B.cHS O x N‖ < δ / 2 := hc.trans_le (min_le_right _ _)
  have hsq : ‖B.cHS O x N‖ ^ 2 < δ := by nlinarith
  have hd : dist (‖B.cHS O x N‖ ^ 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]; exact hsq
  have h3 := hcont hd
  rw [detErr38_zero, Real.dist_eq, sub_zero] at h3
  have h4 := B.abs_detMN_sub_one_le O x N
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt h4 (lt_of_le_of_lt (le_abs_self _) h3)

include O in
/-- The same statement for `|det L_N|²`, as written in v2. -/
theorem tendstoUniformlyOn_sq_detLN {K : Set H1_38} (hK : IsCompact K) :
    TendstoUniformlyOn (fun (N : ℕ) (x : H1_38) => |B.detLN x N| ^ 2) (fun _ => (1 : ℝ)) atTop K := by
  have := B.tendstoUniformlyOn_detMN O hK
  refine this.congr ?_
  exact Eventually.of_forall (fun N x _ => (B.F01_06_identity x N).symm)

/-! ## Basis independence (last sentences of the v2 proof) -/

/-- "Conjugating the same finite matrix to any positive diagonal weighted basis leaves its
determinant unchanged": the real determinant of `L_N` is the determinant of its matrix in *any*
basis of `V_N`. -/
theorem detLN_eq_matrix_det38 (x : H1_38) (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (cp38 N).V) :
    B.detLN x N = Matrix.det (LinearMap.toMatrix b b (B.LNmap x N)) :=
  (LinearMap.det_toMatrix b _).symm

theorem detMN_eq_matrix_det38 (x : H1_38) (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (cp38 N).V) :
    B.detMN x N = Matrix.det (1 + LinearMap.toMatrix b b (B.MNmap x N)) := by
  unfold detMN
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_one]

end BirkhoffInput38

/-- Conjugation of a matrix by a positive diagonal matrix does not change its determinant. -/
theorem det_diagonal_conj38 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    Matrix.det (Matrix.diagonal (fun i => (w i)⁻¹) * M * Matrix.diagonal w) = Matrix.det M := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_inv_distrib]
  have : ∏ i, w i ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => (hw i).ne')
  field_simp

end NlsGge.Birkhoff
