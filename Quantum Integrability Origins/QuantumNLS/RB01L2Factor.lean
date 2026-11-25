import Mathlib
import QuantumNLS.RB01L2Columns
import QuantumNLS.TerraMultiRound35SquareInverse

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-6: real analyticity of the high-label columns into `ℓ²`.

Source (collective_actions.tex:239-280): the columns `(P_n(u) - P_n⁰) χ_{n,j}` are obtained from
`(R_n(z) - R_{0,n}(z)) χ_{n,j} = (z - p_n)^{-1} (1 - A_n(z))^{-1} A_n(z) χ_{n,j}`, with `A_n = R_0 V` bounded uniformly in
`n`, `A_n²` small for `|n| > N`, and `A_n χ_{n,j} = R_{0,n} V χ_{n,j}` square summable (stage RB01-5); "these are bounds
for bounded linear maps into `ℓ²(L²)`".

Here, on the real slice, with `T_n(z,u) = V_u R_{0,n}(z)` (LOCAL-002 convention) and `A_n(p_n + w, u) = T_n(p_n + w̄, u)^*`:
* (i) `colS_lip`: `w ↦ (R_{0,n}(p_n+w) V_u χ_{n,j})_n ∈ ℓ²` is Lipschitz on `|w| = r`, uniformly in `n` (free resolvent
  identity and `free_res_annulus`).
* (ii) `Ainf`: `n ↦ A_n(p_n + w, u)` (masked to `|n| > N`) as one element of `ℓ∞(ℤ; B(H))`, real-linear in `u` with the
  uniform bound of `exists_T_annulus`, Lipschitz in `w`; `act` is the bounded bilinear action
  `ℓ∞(B(H)) × ℓ²(H) → ℓ²(H)`; `Gclm` packages `u ↦ (w ↦ act (Ainf w u)) ∈ C(|w| = r, B(ℓ²(H)))`; `G_sq_le`: its square is
  `≤ 1/4` wherever `T_n(·,u)²` is square-small for `|n| > N`; `inv_analyticAt`: `u ↦ (1 - G u)^{-1}` is real analytic there
  (via `TerraMultiRound35SquareInverse.analytic_inverse_of_square_small`).
* (iii) `Fmap`: the Bochner contour integral `(2πi)^{-1} ∮_{|w|=r} φ(w) · mask((1 - G u(w))^{-1} col(w,u)) dw ∈ ℓ²`;
  `Fmap_analyticAt`; `Fmap_component`: its `n`-th component, `|n| > N`, equals
  `[(2πi)^{-1} ∮_{|z-p_n|=r} ψ(z-p_n) (R_u(z) - R_0(z)) dz] χ_{n,j}` for `φ(w) = ψ(w)/w`;
* **`tail_columns_analytic`**: for every `u₀` there are `N`, `ρ > 0` and real-analytic maps `FP, FD : L² → ℓ²(ℤ; H)` on
  `B(u₀, ρ)` with `FP(u)_n = (P_n(u) - P_n⁰) χ_{n,j}` and `FD(u)_n = (D_n(u) - D_n(0)) χ_{n,j}` (`D_n` = `dressedIntegral`)
  for `|n| > N`, and `0` otherwise. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.RB01L2Factor
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local002Rank
  QuantumNLS.Local002SA QuantumNLS.Local002Basis QuantumNLS.RB01FourierAction QuantumNLS.RB01SquareSmall
  QuantumNLS.RB01Resolvent QuantumNLS.RB01Columns QuantumNLS.RB01L2Columns

variable {L κ : ℝ}

/-- `ℓ²(ℤ; L²(0,L;ℂ²))`. -/
abbrev HS (L : ℝ) := lp (fun _ : ℤ => H2 L) 2
/-- `ℓ∞(ℤ; B(L²(0,L;ℂ²)))`. -/
abbrev BS (L : ℝ) := lp (fun _ : ℤ => H2 L →L[ℂ] H2 L) ∞

/-- The standing parameters `0 < L`, `0 < r < 2π/L`. -/
structure Setup (L r : ℝ) : Prop where
  hL : 0 < L
  hr : 0 < r
  hr2 : r < 2 * Real.pi / L

/-! ### `ℓ²` comparison lemmas -/

theorem lp2_norm_le {x y : HS L} {c : ℝ} (hc : 0 ≤ c) (h : ∀ n, ‖x n‖ ≤ c * ‖y n‖) : ‖x‖ ≤ c * ‖y‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le hp (mul_nonneg hc (norm_nonneg _)) ?_
  have hy := lp.norm_rpow_eq_tsum hp y
  have hxs := (lp.memℓp x).summable hp
  have hys := (lp.memℓp y).summable hp
  rw [Real.mul_rpow hc (norm_nonneg _), hy, ← tsum_mul_left]
  refine hxs.tsum_le_tsum (fun n => ?_) (hys.mul_left _)
  rw [← Real.mul_rpow hc (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (h n) hp.le

theorem memℓp2_of_le {f : ℤ → H2 L} (y : HS L) {c : ℝ} (hc : 0 ≤ c) (h : ∀ n, ‖f n‖ ≤ c * ‖y n‖) :
    Memℓp f 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  apply memℓp_gen
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) (fun n => ?_)
    (((lp.memℓp y).summable hp).mul_left (c ^ (2 : ℝ≥0∞).toReal))
  rw [← Real.mul_rpow hc (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (h n) hp.le

/-- A bounded real-linear map is analytic (the continuous linear map is built here, with the synthesized
instances). -/
theorem lin_analytic {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
    [NormedSpace ℝ X] (F : E → X) (K : ℝ) (hadd : ∀ u v, F (u + v) = F u + F v)
    (hsmul : ∀ (a : ℝ) u, F (a • u) = a • F u) (hb : ∀ u, ‖F u‖ ≤ K * ‖u‖) (u : E) : AnalyticAt ℝ F u :=
  (LinearMap.mkContinuous { toFun := F, map_add' := hadd, map_smul' := hsmul } K hb).analyticAt u

/-- A bounded real-bilinear map is analytic. -/
theorem bilin_analytic {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E → F → G)
    (h1 : ∀ x x' y, B (x + x') y = B x y + B x' y) (h2 : ∀ (a : ℝ) x y, B (a • x) y = a • B x y)
    (h3 : ∀ x y y', B x (y + y') = B x y + B x y') (h4 : ∀ (a : ℝ) x y, B x (a • y) = a • B x y)
    (hb : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) (p : E × F) : AnalyticAt ℝ (fun q : E × F => B q.1 q.2) p :=
  (LinearMap.mkContinuous₂ (LinearMap.mk₂ ℝ B h1 h2 h3 h4) 1
    (fun x y => by rw [one_mul]; exact hb x y)).analyticAt_bilinear p

/-! ### The bounded bilinear action `ℓ∞(B(H)) × ℓ²(H) → ℓ²(H)` -/

theorem act_le (a : BS L) (x : HS L) (n : ℤ) : ‖a n (x n)‖ ≤ ‖a‖ * ‖x n‖ :=
  ((a n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero a n) (norm_nonneg _))

/-- `(a_n x_n)_n`. -/
def actVec (a : BS L) (x : HS L) : HS L :=
  ⟨fun n => a n (x n), memℓp2_of_le x (norm_nonneg a) (act_le a x)⟩

/-- **The bounded bilinear action** `ℓ∞(ℤ; B(H)) × ℓ²(ℤ; H) → ℓ²(ℤ; H)`, `(a, x) ↦ (a_n x_n)_n`. -/
def act : BS L →L[ℂ] HS L →L[ℂ] HS L :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ actVec
      (fun a b x => lp.ext (funext fun n => by
        show (a + b) n (x n) = a n (x n) + b n (x n)
        rw [lp.coeFn_add, Pi.add_apply, ContinuousLinearMap.add_apply]))
      (fun c a x => lp.ext (funext fun n => by
        show (c • a) n (x n) = c • a n (x n)
        rw [lp.coeFn_smul, Pi.smul_apply, ContinuousLinearMap.smul_apply]))
      (fun a x y => lp.ext (funext fun n => by
        show a n ((x + y) n) = a n (x n) + a n (y n)
        rw [lp.coeFn_add, Pi.add_apply, map_add]))
      (fun c a x => lp.ext (funext fun n => by
        show a n ((c • x) n) = c • a n (x n)
        rw [lp.coeFn_smul, Pi.smul_apply, map_smul])))
    1 (fun a x => by rw [one_mul]; exact lp2_norm_le (norm_nonneg a) (act_le a x))

theorem act_apply (a : BS L) (x : HS L) (n : ℤ) : (act a x : ℤ → H2 L) n = a n (x n) := rfl

theorem act_norm_le (a : BS L) : ‖act a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun x => lp2_norm_le (norm_nonneg a) (act_le a x)

theorem act_sq_le (a : BS L) {c : ℝ} (hc : 0 ≤ c) (h : ∀ n, ‖a n * a n‖ ≤ c) : ‖act a * act a‖ ≤ c :=
  ContinuousLinearMap.opNorm_le_bound _ hc fun x => lp2_norm_le hc fun n => by
    show ‖a n (a n (x n))‖ ≤ c * ‖x n‖
    exact ((a n * a n).le_opNorm (x n)).trans (mul_le_mul_of_nonneg_right (h n) (norm_nonneg _))

/-- If `(1 - act a) Y = 1`, `a_n = T'^*` and `(1 - T') S' = 1`, then `(Y x)_n = S'^* x_n`. -/
theorem inv_component {a : BS L} {Y : HS L →L[ℂ] HS L} (hY : (1 - act a) * Y = 1) {n : ℤ}
    {T' S' : H2 L →L[ℂ] H2 L} (ha : a n = ContinuousLinearMap.adjoint T') (hS1 : (1 - T') * S' = 1)
    (x : HS L) : (Y x : ℤ → H2 L) n = ContinuousLinearMap.adjoint S' (x n) := by
  have e := congrArg (fun A : HS L →L[ℂ] HS L => (A x : ℤ → H2 L) n) hY
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    lp.coeFn_sub, Pi.sub_apply] at e
  change (Y x : ℤ → H2 L) n - a n ((Y x : ℤ → H2 L) n) = x n at e
  rw [ha] at e
  have hadj : ContinuousLinearMap.adjoint S' * (1 - ContinuousLinearMap.adjoint T') = 1 := by
    have h := congrArg ContinuousLinearMap.adjoint hS1
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp, map_sub,
      show (1 : H2 L →L[ℂ] H2 L) = ContinuousLinearMap.id ℂ (H2 L) from rfl,
      ContinuousLinearMap.adjoint_id] at h
    exact h
  have h2 := congrArg (fun A : H2 L →L[ℂ] H2 L => A ((Y x : ℤ → H2 L) n)) hadj
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at h2
  rw [e] at h2
  exact h2.symm

/-! ### The free resolvent, the multiplication operators and their adjoints -/

/-- The free resolvent of parity `(-1)^n` at `z`. -/
def Rfree (L κ : ℝ) (n : ℤ) (z : ℂ) : H2 L →L[ℂ] H2 L := resolvent L κ (fun _ => 0) (parity n) z

/-- `z̄` for `z = p_n + w`. -/
def zb (L : ℝ) (n : ℤ) (w : ℂ) : ℂ := conj ((pm L n : ℂ) + w)

theorem norm_pw (n : ℤ) (w : ℂ) : ‖((pm L n : ℂ) + w) - (pm L n : ℂ)‖ = ‖w‖ := by
  rw [add_sub_cancel_left]

theorem norm_zb (n : ℤ) (w : ℂ) : ‖zb L n w - (pm L n : ℂ)‖ = ‖w‖ := by
  unfold zb; rw [conj_annulus, norm_pw]

theorem norm_sphere {r : ℝ} (w : sphere (0 : ℂ) r) : ‖(w : ℂ)‖ = r := mem_sphere_zero_iff_norm.1 w.2

theorem free_at {r : ℝ} (S : Setup L r) {n : ℤ} {z : ℂ} (hz : ‖z - (pm L n : ℂ)‖ = r) :
    IsResolvent L κ (fun _ => 0) (parity n) z (Rfree L κ n z) ∧ ‖Rfree L κ n z‖ ≤ 2 / r := by
  obtain ⟨R0, h, hn⟩ := free_res_annulus (κ := κ) S.hL S.hr S.hr2 (by rw [hz]; linarith [S.hr]) hz.le
  have e : Rfree L κ n z = R0 := resolvent_eq h
  rw [e]; exact ⟨h, hn⟩

/-- `T_n(z̄, u) = V_u R_{0,n}(z̄)`, `z = p_n + w`. -/
def Tb (L κ : ℝ) (n : ℤ) (w : ℂ) (u : Lp ℂ 2 (μI L)) : H2 L →L[ℂ] H2 L := Mop κ (Rfree L κ n (zb L n w)) u

theorem Tb_spec {r : ℝ} (S : Setup L r) {n : ℤ} {w : ℂ} (hw : ‖w‖ = r) (u : Lp ℂ 2 (μI L)) :
    QuantumNLS.Local002.IsMulOp κ (Rfree L κ n (zb L n w)) (u : ℝ → ℂ) (Tb L κ n w u) ∧
      ‖Tb L κ n w u‖ ≤ Mr L κ r * ‖u‖ := by
  have hz : ‖zb L n w - (pm L n : ℂ)‖ = r := by rw [norm_zb, hw]
  obtain ⟨T, hT, hTn⟩ := exists_T_annulus S.hL S.hr S.hr2 (by rw [hz]; linarith [S.hr]) hz.le
    (free_at (κ := κ) S hz).1 u
  rw [Tb, Mop_eq hT]; exact ⟨hT, hTn⟩

theorem Tb_lip {r : ℝ} (S : Setup L r) {n : ℤ} {w w' : ℂ} (hw : ‖w‖ = r) (hw' : ‖w'‖ = r)
    (u : Lp ℂ 2 (μI L)) :
    ‖Tb L κ n w u - Tb L κ n w' u‖ ≤ ‖w - w'‖ * (2 / r) * (Mr L κ r * ‖u‖) := by
  have hz : ‖zb L n w - (pm L n : ℂ)‖ = r := by rw [norm_zb, hw]
  have hz' : ‖zb L n w' - (pm L n : ℂ)‖ = r := by rw [norm_zb, hw']
  obtain ⟨hT, hTn⟩ := Tb_spec (κ := κ) S hw u
  obtain ⟨hT', -⟩ := Tb_spec (κ := κ) S hw' u
  have hf' := free_at (κ := κ) S hz'
  rw [mulop_sub (free_at (κ := κ) S hz).1 hf'.1 hT hT', norm_smul]
  have hd : ‖zb L n w' - zb L n w‖ = ‖w - w'‖ := by
    unfold zb
    rw [← map_sub, Complex.norm_conj, add_sub_add_left_eq_sub, norm_sub_rev]
  rw [hd]
  have h1 : ‖Tb L κ n w u * Rfree L κ n (zb L n w')‖ ≤ Mr L κ r * ‖u‖ * (2 / r) :=
    (norm_mul_le _ _).trans (mul_le_mul hTn hf'.2 (norm_nonneg _)
      (mul_nonneg (Mr_nonneg L κ r) (norm_nonneg _)))
  calc ‖w - w'‖ * ‖Tb L κ n w u * Rfree L κ n (zb L n w')‖ ≤ ‖w - w'‖ * (Mr L κ r * ‖u‖ * (2 / r)) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖w - w'‖ * (2 / r) * (Mr L κ r * ‖u‖) := by ring

/-- `A_n(p_n + w, u) = T_n(p_n + w̄, u)^*` (the source's `A_n = R_0 V`). -/
def Ab (L κ : ℝ) (n : ℤ) (w : ℂ) (u : Lp ℂ 2 (μI L)) : H2 L →L[ℂ] H2 L :=
  ContinuousLinearMap.adjoint (Tb L κ n w u)

/-- `A_n` masked to the high labels `|n| > N`. -/
def Am (L κ : ℝ) (N : ℕ) (n : ℤ) (w : ℂ) (u : Lp ℂ 2 (μI L)) : H2 L →L[ℂ] H2 L :=
  if (N : ℝ) < |(n : ℝ)| then Ab L κ n w u else 0

theorem Am_le {r : ℝ} (S : Setup L r) (N : ℕ) (n : ℤ) {w : ℂ} (hw : ‖w‖ = r) (u : Lp ℂ 2 (μI L)) :
    ‖Am L κ N n w u‖ ≤ Mr L κ r * ‖u‖ := by
  unfold Am; split_ifs
  · rw [Ab, LinearIsometryEquiv.norm_map]; exact (Tb_spec S hw u).2
  · rw [norm_zero]; exact mul_nonneg (Mr_nonneg _ _ _) (norm_nonneg _)

theorem Am_lip {r : ℝ} (S : Setup L r) (N : ℕ) (n : ℤ) {w w' : ℂ} (hw : ‖w‖ = r) (hw' : ‖w'‖ = r)
    (u : Lp ℂ 2 (μI L)) :
    ‖Am L κ N n w u - Am L κ N n w' u‖ ≤ ‖w - w'‖ * (2 / r) * (Mr L κ r * ‖u‖) := by
  unfold Am; split_ifs
  · rw [Ab, Ab, ← map_sub, LinearIsometryEquiv.norm_map]; exact Tb_lip S hw hw' u
  · rw [sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (div_nonneg zero_le_two S.hr.le))
      (mul_nonneg (Mr_nonneg _ _ _) (norm_nonneg _))

theorem Am_add {r : ℝ} (S : Setup L r) (N : ℕ) (n : ℤ) {w : ℂ} (hw : ‖w‖ = r) (u v : Lp ℂ 2 (μI L)) :
    Am L κ N n w (u + v) = Am L κ N n w u + Am L κ N n w v := by
  unfold Am; split_ifs
  · unfold Ab Tb
    rw [Mop_add ⟨_, (Tb_spec (κ := κ) S hw u).1⟩ ⟨_, (Tb_spec (κ := κ) S hw v).1⟩, map_add]
  · rw [add_zero]

theorem Am_smul {r : ℝ} (S : Setup L r) (N : ℕ) (n : ℤ) {w : ℂ} (hw : ‖w‖ = r) (a : ℝ)
    (u : Lp ℂ 2 (μI L)) : Am L κ N n w (a • u) = (a : ℂ) • Am L κ N n w u := by
  unfold Am; split_ifs
  · unfold Ab Tb
    rw [Mop_eq ((Mop_spec ⟨_, (Tb_spec (κ := κ) S hw u).1⟩).real_smul a), LinearIsometryEquiv.map_smulₛₗ,
      Complex.conj_ofReal]
  · exact (ContinuousLinearMap.ext fun x => by simp : ((a : ℂ) • (0 : H2 L →L[ℂ] H2 L)) = 0).symm

/-- **The `ℓ∞(ℤ; B(H))` family** `n ↦ A_n(p_n + w, u)` (`|n| > N`, else `0`) for `|w| = r`. -/
def Ainf (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (w : sphere (0 : ℂ) r) (u : Lp ℂ 2 (μI L)) : BS L :=
  ⟨fun n => Am L κ N n w u, memℓp_infty_iff.2 ⟨Mr L κ r * ‖u‖, by
    rintro _ ⟨n, rfl⟩
    exact Am_le S N n (norm_sphere w) u⟩⟩

theorem Ainf_apply (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (w : sphere (0 : ℂ) r) (u : Lp ℂ 2 (μI L))
    (n : ℤ) : (Ainf κ S N w u : ℤ → H2 L →L[ℂ] H2 L) n = Am L κ N n w u := rfl

theorem Ainf_le (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (w : sphere (0 : ℂ) r) (u : Lp ℂ 2 (μI L)) :
    ‖Ainf κ S N w u‖ ≤ Mr L κ r * ‖u‖ :=
  lp.norm_le_of_forall_le (mul_nonneg (Mr_nonneg L κ r) (norm_nonneg u))
    fun n => Am_le S N n (norm_sphere w) u

theorem Ainf_lip (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (w w' : sphere (0 : ℂ) r) (u : Lp ℂ 2 (μI L)) :
    ‖Ainf κ S N w u - Ainf κ S N w' u‖ ≤ ‖(w : ℂ) - w'‖ * (2 / r) * (Mr L κ r * ‖u‖) := by
  refine lp.norm_le_of_forall_le (mul_nonneg (mul_nonneg (norm_nonneg _) (div_nonneg zero_le_two S.hr.le))
    (mul_nonneg (Mr_nonneg _ _ _) (norm_nonneg _))) fun n => ?_
  rw [lp.coeFn_sub, Pi.sub_apply]
  exact Am_lip S N n (norm_sphere w) (norm_sphere w') u

theorem Ainf_add (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (w : sphere (0 : ℂ) r) (u v : Lp ℂ 2 (μI L)) :
    Ainf κ S N w (u + v) = Ainf κ S N w u + Ainf κ S N w v :=
  lp.ext (funext fun n => by
    rw [lp.coeFn_add, Pi.add_apply]
    exact Am_add S N n (norm_sphere w) u v)

theorem Ainf_smul (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (w : sphere (0 : ℂ) r) (a : ℝ)
    (u : Lp ℂ 2 (μI L)) : Ainf κ S N w (a • u) = (a : ℂ) • Ainf κ S N w u :=
  lp.ext (funext fun n => by
    rw [lp.coeFn_smul, Pi.smul_apply]
    exact Am_smul S N n (norm_sphere w) a u)

/-! ### Packaging into `C(|w| = r, ·)` -/

theorem cont_of_lip {X : Type*} [NormedAddCommGroup X] {r : ℝ} (f : sphere (0 : ℂ) r → X) {K : ℝ}
    (hK : 0 ≤ K) (h : ∀ w w', ‖f w - f w'‖ ≤ ‖(w : ℂ) - w'‖ * K) : Continuous f :=
  (LipschitzWith.of_dist_le_mul (K := K.toNNReal) fun w w' => by
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hK, mul_comm]
    exact h w w').continuous

/-- `w ↦ act (Ainf w u)`. -/
def Gfun (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (u : Lp ℂ 2 (μI L)) :
    C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L) :=
  ⟨fun w => act (Ainf κ S N w u), cont_of_lip _ (K := 2 / r * (Mr L κ r * ‖u‖))
    (mul_nonneg (div_nonneg zero_le_two S.hr.le) (mul_nonneg (Mr_nonneg L κ r) (norm_nonneg u)))
    fun w w' => by
      rw [← ContinuousLinearMap.map_sub]
      refine (act_norm_le _).trans ((Ainf_lip κ S N w w' u).trans (le_of_eq (by ring)))⟩

/-- **The operator family** `u ↦ (w ↦ diag(A_n(p_n+w,u))_{|n|>N}) ∈ C(|w| = r, B(ℓ²(H)))`, bounded real-linear. -/
def Gclm (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) :
    Lp ℂ 2 (μI L) →L[ℝ] C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L) :=
  LinearMap.mkContinuous
    { toFun := Gfun κ S N
      map_add' := fun u v => ContinuousMap.ext fun w => by
        show act (Ainf κ S N w (u + v)) = act (Ainf κ S N w u) + act (Ainf κ S N w v)
        rw [Ainf_add, ContinuousLinearMap.map_add]
      map_smul' := fun a u => ContinuousMap.ext fun w => by
        show act (Ainf κ S N w (a • u)) = a • act (Ainf κ S N w u)
        rw [Ainf_smul, ContinuousLinearMap.map_smul]
        exact Complex.coe_smul a _ }
    (Mr L κ r) fun u => (ContinuousMap.norm_le _ (mul_nonneg (Mr_nonneg L κ r) (norm_nonneg u))).2 fun w =>
      (act_norm_le _).trans (Ainf_le κ S N w u)

theorem Gclm_apply (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (u : Lp ℂ 2 (μI L)) (w : sphere (0 : ℂ) r) :
    Gclm κ S N u w = act (Ainf κ S N w u) := rfl

theorem Ab_sq_le {r : ℝ} (S : Setup L r) {n : ℤ} {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u) {w : ℂ}
    (hw : ‖w‖ = r) : ‖Ab L κ n w u * Ab L κ n w u‖ ≤ 1 / 4 := by
  have hzc : ‖zb L n w - (pm L n : ℂ)‖ = r := by rw [norm_zb, hw]
  have h := hu (zb L n w) (by rw [hzc]; linarith [S.hr]) hzc.le _ _ (free_at (κ := κ) S hzc).1
    (Tb_spec S hw u).1
  unfold Ab
  rw [show ContinuousLinearMap.adjoint (Tb L κ n w u) * ContinuousLinearMap.adjoint (Tb L κ n w u) =
      ContinuousLinearMap.adjoint (Tb L κ n w u * Tb L κ n w u) from
      (ContinuousLinearMap.adjoint_comp _ _).symm, LinearIsometryEquiv.norm_map]
  exact h

/-- Square-smallness of the packaged family. -/
theorem G_sq_le (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) {u : Lp ℂ 2 (μI L)}
    (hu : ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → SqSmall L κ r n u) :
    ‖Gclm κ S N u * Gclm κ S N u‖ ≤ 1 / 4 := by
  refine (ContinuousMap.norm_le _ (by norm_num)).2 fun w => ?_
  rw [ContinuousMap.mul_apply, Gclm_apply]
  refine act_sq_le _ (by norm_num) fun n => ?_
  rw [Ainf_apply]
  unfold Am; split_ifs with h
  · exact Ab_sq_le S (hu n h) (norm_sphere w)
  · simp

theorem one_le_C {r : ℝ} : ‖(1 : C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L))‖ ≤ 1 :=
  (ContinuousMap.norm_le _ zero_le_one).2 fun _ => ContinuousLinearMap.norm_id_le

/-- **The inverse family is real analytic** wherever the square is small (R35 SquareInverse). -/
theorem inv_analyticAt (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) {u : Lp ℂ 2 (μI L)}
    (hs : ‖Gclm κ S N u * Gclm κ S N u‖ < 1) :
    AnalyticAt ℝ (fun v => Ring.inverse (1 - Gclm κ S N v)) u := by
  have hinvC : AnalyticAt ℂ (fun y : C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L) => Ring.inverse (1 - y))
      (Gclm κ S N u) :=
    QuantumNLS.TerraMultiRound35SquareInverse.analytic_inverse_of_square_small
      (E := C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L)) (A := C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L)) one_le_C
      (F := fun y => y) (x := Gclm κ S N u) analyticAt_id hs
  have hinv : AnalyticAt ℝ (fun y : C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L) => Ring.inverse (1 - y))
      (Gclm κ S N u) := hinvC.restrictScalars
  have hG : AnalyticAt ℝ (fun v => Gclm κ S N v) u :=
    lin_analytic _ (Mr L κ r)
      (fun v v' => ContinuousMap.ext fun w => by
        show act (Ainf κ S N w (v + v')) = act (Ainf κ S N w v) + act (Ainf κ S N w v')
        rw [Ainf_add, ContinuousLinearMap.map_add])
      (fun a v => ContinuousMap.ext fun w => by
        show act (Ainf κ S N w (a • v)) = a • act (Ainf κ S N w v)
        rw [Ainf_smul, ContinuousLinearMap.map_smul]
        exact Complex.coe_smul a _)
      (fun v => (ContinuousMap.norm_le _ (mul_nonneg (Mr_nonneg L κ r) (norm_nonneg v))).2 fun w =>
        (act_norm_le _).trans (Ainf_le κ S N w v)) u
  exact AnalyticAt.comp (g := fun y : C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L) => Ring.inverse (1 - y))
    (f := fun v => Gclm κ S N v) hinv hG

/-! ### (i) The columns, continuously in `w` -/

theorem h1_of {r : ℝ} (S : Setup L r) {w : ℂ} (hw : ‖w‖ = r) : r / 2 ≤ ‖w‖ := by
  rw [hw]; linarith [S.hr]

/-- `colCLM` at `|w| = r`. -/
def colS (κ : ℝ) {r : ℝ} (S : Setup L r) (j : Fin 2) (w : sphere (0 : ℂ) r) :
    Lp ℂ 2 (μI L) →L[ℝ] HS L :=
  haveI : Fact (0 < L) := ⟨S.hL⟩
  colCLM (κ := κ) S.hL S.hr S.hr2 (h1_of S (norm_sphere w)) (norm_sphere w).le j

theorem colS_apply (κ : ℝ) {r : ℝ} (S : Setup L r) (j : Fin 2) (w : sphere (0 : ℂ) r) (u : Lp ℂ 2 (μI L))
    (n : ℤ) : (colS κ S j w u : ℤ → H2 L) n = Rfree L κ n ((pm L n : ℂ) + w) (Vchi κ u n j) := rfl

/-- The norm constant `2√κ L^{-1/2} √G` of `colCLM`. -/
def Kc (L κ r : ℝ) : ℝ :=
  2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * Real.sqrt (∑' m, gmaj r (2 * Real.pi / L - r) m)

theorem Kc_nonneg (L κ r : ℝ) : 0 ≤ Kc L κ r := by unfold Kc; positivity

theorem colS_le (κ : ℝ) {r : ℝ} (S : Setup L r) (j : Fin 2) (w : sphere (0 : ℂ) r) (u : Lp ℂ 2 (μI L)) :
    ‖colS κ S j w u‖ ≤ Kc L κ r * ‖u‖ := by
  haveI : Fact (0 < L) := ⟨S.hL⟩
  unfold colS colCLM
  exact ContinuousLinearMap.le_of_opNorm_le _ (LinearMap.mkContinuous_norm_le _ (Kc_nonneg L κ r) _) u

/-- **(i) `w`-continuity of the column map, uniformly in `n`**: `‖col(w) - col(w')‖_{ℓ²} ≤ |w - w'| (2/r) K ‖u‖`. -/
theorem colS_lip (κ : ℝ) {r : ℝ} (S : Setup L r) (j : Fin 2) (w w' : sphere (0 : ℂ) r)
    (u : Lp ℂ 2 (μI L)) :
    ‖colS κ S j w u - colS κ S j w' u‖ ≤ ‖(w : ℂ) - w'‖ * (2 / r) * (Kc L κ r * ‖u‖) := by
  have hc : 0 ≤ ‖(w : ℂ) - w'‖ * (2 / r) := mul_nonneg (norm_nonneg _) (div_nonneg zero_le_two S.hr.le)
  have key : ‖colS κ S j w u - colS κ S j w' u‖ ≤ (‖(w : ℂ) - w'‖ * (2 / r)) * ‖colS κ S j w' u‖ := by
    refine lp2_norm_le hc fun n => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, colS_apply, colS_apply]
    have hz := free_at (κ := κ) S (n := n) (z := (pm L n : ℂ) + w) (by rw [norm_pw, norm_sphere w])
    have hz' := free_at (κ := κ) S (n := n) (z := (pm L n : ℂ) + w') (by rw [norm_pw, norm_sphere w'])
    have hid := congrArg (fun A : H2 L →L[ℂ] H2 L => A (Vchi κ u n j)) (resolvent_identity hz.1 hz'.1)
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply] at hid
    rw [hid, norm_smul]
    have e : ‖((pm L n : ℂ) + w') - ((pm L n : ℂ) + w)‖ = ‖(w : ℂ) - w'‖ := by
      rw [add_sub_add_left_eq_sub, norm_sub_rev]
    rw [e]
    calc ‖(w : ℂ) - w'‖ * ‖Rfree L κ n ((pm L n : ℂ) + w) (Rfree L κ n ((pm L n : ℂ) + w') (Vchi κ u n j))‖
        ≤ ‖(w : ℂ) - w'‖ * ((2 / r) * ‖Rfree L κ n ((pm L n : ℂ) + w') (Vchi κ u n j)‖) :=
          mul_le_mul_of_nonneg_left (((Rfree L κ n _).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hz.2 (norm_nonneg _))) (norm_nonneg _)
      _ = ‖(w : ℂ) - w'‖ * (2 / r) * ‖(colS κ S j w' u : ℤ → H2 L) n‖ := by
          rw [colS_apply]; ring
  calc ‖colS κ S j w u - colS κ S j w' u‖ ≤ (‖(w : ℂ) - w'‖ * (2 / r)) * (Kc L κ r * ‖u‖) :=
        key.trans (mul_le_mul_of_nonneg_left (colS_le κ S j w' u) hc)
    _ = ‖(w : ℂ) - w'‖ * (2 / r) * (Kc L κ r * ‖u‖) := rfl

def Cfun (κ : ℝ) {r : ℝ} (S : Setup L r) (j : Fin 2) (u : Lp ℂ 2 (μI L)) : C(sphere (0 : ℂ) r, HS L) :=
  ⟨fun w => colS κ S j w u, cont_of_lip _ (K := 2 / r * (Kc L κ r * ‖u‖))
    (mul_nonneg (div_nonneg zero_le_two S.hr.le) (mul_nonneg (Kc_nonneg L κ r) (norm_nonneg u)))
    fun w w' => (colS_lip κ S j w w' u).trans (le_of_eq (by ring))⟩

/-- The column map `u ↦ (w ↦ (R_{0,n}(p_n+w) V_u χ_{n,j})_n) ∈ C(|w| = r, ℓ²(H))`, bounded real-linear. -/
def Cclm (κ : ℝ) {r : ℝ} (S : Setup L r) (j : Fin 2) : Lp ℂ 2 (μI L) →L[ℝ] C(sphere (0 : ℂ) r, HS L) :=
  LinearMap.mkContinuous
    { toFun := Cfun κ S j
      map_add' := fun u v => ContinuousMap.ext fun w => map_add (colS κ S j w) u v
      map_smul' := fun a u => ContinuousMap.ext fun w => map_smul (colS κ S j w) a u }
    (Kc L κ r) fun u => (ContinuousMap.norm_le _ (mul_nonneg (Kc_nonneg L κ r) (norm_nonneg u))).2
      fun w => colS_le κ S j w u

/-! ### (iii) Pointwise action and the contour integral -/

def appFun {r : ℝ} (F : C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L)) (g : C(sphere (0 : ℂ) r, HS L)) :
    C(sphere (0 : ℂ) r, HS L) :=
  ⟨fun w => F w (g w), F.continuous.clm_apply g.continuous⟩

theorem appFun_apply {r : ℝ} (F : C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L)) (g : C(sphere (0 : ℂ) r, HS L))
    (w : sphere (0 : ℂ) r) : appFun F g w = F w (g w) := rfl

/-- The pointwise action is a bounded real-bilinear map, hence analytic. -/
theorem appFun_analytic {r : ℝ} (p : C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L) × C(sphere (0 : ℂ) r, HS L)) :
    AnalyticAt ℝ (fun q : C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L) × C(sphere (0 : ℂ) r, HS L) =>
      appFun q.1 q.2) p :=
  bilin_analytic appFun
    (fun F F' g => ContinuousMap.ext fun w => by
      show (F + F') w (g w) = F w (g w) + F' w (g w)
      rw [ContinuousMap.add_apply, ContinuousLinearMap.add_apply])
    (fun a F g => ContinuousMap.ext fun w => by
      show (a • F) w (g w) = a • F w (g w)
      rw [ContinuousMap.smul_apply, ContinuousLinearMap.smul_apply])
    (fun F g g' => ContinuousMap.ext fun w => by
      show F w ((g + g') w) = F w (g w) + F w (g' w)
      rw [ContinuousMap.add_apply, map_add])
    (fun a F g => ContinuousMap.ext fun w => by
      show F w ((a • g) w) = a • F w (g w)
      rw [ContinuousMap.smul_apply]
      exact (F w).map_smul_of_tower a (g w))
    (fun F g => (ContinuousMap.norm_le _ (by positivity)).2 fun w =>
      ((F w).le_opNorm _).trans (mul_le_mul (F.norm_coe_le_norm w) (g.norm_coe_le_norm w) (norm_nonneg (g w))
        (norm_nonneg F))) p

open Classical in
/-- The weighted integrand on `ℂ` (extension by zero off the circle). -/
def ig {r : ℝ} (φ : C(sphere (0 : ℂ) r, ℂ)) (g : C(sphere (0 : ℂ) r, HS L)) (z : ℂ) : HS L :=
  if h : z ∈ sphere (0 : ℂ) r then φ ⟨z, h⟩ • g ⟨z, h⟩ else 0

theorem ig_pos {r : ℝ} (φ : C(sphere (0 : ℂ) r, ℂ)) (g : C(sphere (0 : ℂ) r, HS L)) {z : ℂ}
    (h : z ∈ sphere (0 : ℂ) r) : ig φ g z = φ ⟨z, h⟩ • g ⟨z, h⟩ := by
  unfold ig; rw [dif_pos h]

theorem ig_cont {r : ℝ} (φ : C(sphere (0 : ℂ) r, ℂ)) (g : C(sphere (0 : ℂ) r, HS L)) :
    ContinuousOn (ig φ g) (sphere (0 : ℂ) r) := by
  rw [continuousOn_iff_continuous_restrict]
  have : (sphere (0 : ℂ) r).domRestrict (ig φ g) = fun w => φ w • g w := by
    funext w; exact ig_pos φ g w.2
  rw [this]; exact φ.continuous.smul g.continuous

/-- `g ↦ (2πi)⁻¹ ∮_{|w|=r} φ(w) g(w) dw`, a bounded `ℂ`-linear map `C(Γ, ℓ²(H)) → ℓ²(H)`. -/
def Jw {r : ℝ} (hr : 0 < r) (φ : C(sphere (0 : ℂ) r, ℂ)) : C(sphere (0 : ℂ) r, HS L) →L[ℂ] HS L :=
  LinearMap.mkContinuous
    { toFun := fun g => ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • ∮ z in C(0, r), ig φ g z
      map_add' := fun g g' => by
        have e : ig φ (g + g') = fun z => ig φ g z + ig φ g' z := by
          funext z
          by_cases h : z ∈ sphere (0 : ℂ) r
          · rw [ig_pos _ _ h, ig_pos _ _ h, ig_pos _ _ h, ContinuousMap.add_apply, smul_add]
          · unfold ig; rw [dif_neg h, dif_neg h, dif_neg h, add_zero]
        rw [e, circleIntegral.integral_add ((ig_cont φ g).circleIntegrable hr.le)
          ((ig_cont φ g').circleIntegrable hr.le), smul_add]
      map_smul' := fun a g => by
        have e : ig φ (a • g) = fun z => a • ig φ g z := by
          funext z
          by_cases h : z ∈ sphere (0 : ℂ) r
          · rw [ig_pos _ _ h, ig_pos _ _ h, ContinuousMap.smul_apply, smul_comm]
          · unfold ig; rw [dif_neg h, dif_neg h, smul_zero]
        simp only [RingHom.id_apply]
        rw [e, circleIntegral.integral_smul, smul_comm] }
    (r * ‖φ‖) fun g => by
      have := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (c := (0 : ℂ)) (R := r)
        (C := ‖φ‖ * ‖g‖) (f := ig φ g) hr.le (fun z hz => by
          rw [ig_pos φ g hz, norm_smul]
          exact mul_le_mul (φ.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _))
      exact this.trans (le_of_eq (by ring))

theorem Jw_apply {r : ℝ} (hr : 0 < r) (φ : C(sphere (0 : ℂ) r, ℂ)) (g : C(sphere (0 : ℂ) r, HS L)) :
    Jw hr φ g = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • ∮ z in C(0, r), ig φ g z := rfl

/-- The `n`-th coordinate `ℓ²(H) → H`. -/
def ev (n : ℤ) : HS L →L[ℂ] H2 L :=
  LinearMap.mkContinuous
    { toFun := fun x => x n
      map_add' := fun x y => by rw [lp.coeFn_add, Pi.add_apply]
      map_smul' := fun c x => by rw [lp.coeFn_smul, Pi.smul_apply]; rfl }
    1 fun x => by rw [one_mul]; exact lp.norm_apply_le_norm two_ne_zero x n

theorem ev_apply (n : ℤ) (x : HS L) : ev n x = x n := rfl

theorem clm_circleIntegral {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] (Λ : X →L[ℂ] Y) {f : ℂ → X} {c : ℂ}
    {R : ℝ} (hf : CircleIntegrable f c R) : Λ (∮ z in C(c, R), f z) = ∮ z in C(c, R), Λ (f z) := by
  unfold circleIntegral
  rw [← Λ.intervalIntegral_comp_comm hf.out]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  exact map_smul Λ _ _

theorem circleIntegral_shift {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (f : ℂ → X) (c : ℂ)
    (R : ℝ) : (∮ z in C(c, R), f z) = ∮ w in C(0, R), f (c + w) := by
  unfold circleIntegral
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [deriv_circleMap, circleMap, zero_add]

/-- The mask `(1_{|n| > N})_n ∈ ℓ∞(B(H))`. -/
def maskInf (N : ℕ) : BS L :=
  ⟨fun n => if (N : ℝ) < |(n : ℝ)| then 1 else 0, memℓp_infty_iff.2 ⟨1, by
    rintro _ ⟨n, rfl⟩
    dsimp only
    split_ifs
    · exact ContinuousLinearMap.norm_id_le
    · simp⟩⟩

theorem act_mask_apply (N : ℕ) (y : HS L) (n : ℤ) :
    (act (maskInf (L := L) N) y : ℤ → H2 L) n = if (N : ℝ) < |(n : ℝ)| then y n else 0 := by
  show (if (N : ℝ) < |(n : ℝ)| then (1 : H2 L →L[ℂ] H2 L) else 0) (y n) = _
  split_ifs <;> rfl

/-- **The analytic column map**: `u ↦ (2πi)⁻¹ ∮_{|w|=r} φ(w) mask((1 - G u(w))⁻¹ col(w, u)) dw ∈ ℓ²(ℤ; H)`. -/
def Fmap (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (j : Fin 2) (φ : C(sphere (0 : ℂ) r, ℂ))
    (u : Lp ℂ 2 (μI L)) : HS L :=
  Jw S.hr φ (appFun (ContinuousMap.const (sphere (0 : ℂ) r) (act (maskInf (L := L) N)) *
    Ring.inverse (1 - Gclm κ S N u)) (Cclm κ S j u))

theorem Fmap_analyticAt (κ : ℝ) {r : ℝ} (S : Setup L r) (N : ℕ) (j : Fin 2) (φ : C(sphere (0 : ℂ) r, ℂ))
    {u : Lp ℂ 2 (μI L)} (hs : ‖Gclm κ S N u * Gclm κ S N u‖ < 1) :
    AnalyticAt ℝ (Fmap κ S N j φ) u := by
  have h3 := inv_analyticAt κ S N hs
  have h4 : AnalyticAt ℝ (fun v => ContinuousMap.const (sphere (0 : ℂ) r) (act (maskInf (L := L) N)) *
      Ring.inverse (1 - Gclm κ S N v)) u :=
    AnalyticAt.mul (𝕜 := ℝ) (A := C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L)) analyticAt_const h3
  have h5 : AnalyticAt ℝ (fun v => appFun (ContinuousMap.const (sphere (0 : ℂ) r) (act (maskInf (L := L) N)) *
      Ring.inverse (1 - Gclm κ S N v)) (Cclm κ S j v)) u :=
    (appFun_analytic _).comp
      (f := fun v => (ContinuousMap.const (sphere (0 : ℂ) r) (act (maskInf (L := L) N)) *
        Ring.inverse (1 - Gclm κ S N v), Cclm κ S j v)) (h4.prod ((Cclm κ S j).analyticAt u))
  have hJ : AnalyticAt ℝ (fun g => Jw S.hr φ g) (appFun (ContinuousMap.const (sphere (0 : ℂ) r)
      (act (maskInf (L := L) N)) * Ring.inverse (1 - Gclm κ S N u)) (Cclm κ S j u)) :=
    lin_analytic _ ‖Jw S.hr φ‖ (fun g g' => (Jw S.hr φ).map_add g g')
      (fun a g => (Jw S.hr φ).map_smul_of_tower a g) (fun g => (Jw S.hr φ).le_opNorm g) _
  exact AnalyticAt.comp (g := fun g => Jw S.hr φ g)
    (f := fun v => appFun (ContinuousMap.const (sphere (0 : ℂ) r) (act (maskInf (L := L) N)) *
      Ring.inverse (1 - Gclm κ S N v)) (Cclm κ S j v)) hJ h5

/-! ### Identification of the components -/

/-- The resolvent difference on a high-label column (equality form of `RB01Columns.resolvent_sub_chi`). -/
theorem res_sub_chi_eq {r : ℝ} (S : Setup L r) {n : ℤ} {u : Lp ℂ 2 (μI L)} (hu : SqSmall L κ r n u)
    {w : ℂ} (hw : ‖w‖ = r) (j : Fin 2) {S' : H2 L →L[ℂ] H2 L}
    (hS1 : (1 - Tb L κ n w u) * S' = 1) (hS2 : S' * (1 - Tb L κ n w u) = 1) :
    (resolvent L κ (u : ℝ → ℂ) (parity n) ((pm L n : ℂ) + w) - Rfree L κ n ((pm L n : ℂ) + w)) (chi L n j) =
      w⁻¹ • ContinuousLinearMap.adjoint S' (Rfree L κ n ((pm L n : ℂ) + w) (Vchi κ u n j)) := by
  set z : ℂ := (pm L n : ℂ) + w with hzdef
  have hz : ‖z - (pm L n : ℂ)‖ = r := by rw [hzdef, norm_pw, hw]
  have hzc : ‖zb L n w - (pm L n : ℂ)‖ = r := by rw [norm_zb, hw]
  have hR0 := (free_at (κ := κ) S hz).1
  have hR0' := (free_at (κ := κ) S hzc).1
  have hzb : zb L n w = conj z := rfl
  rw [hzb] at hR0'
  have hadj := free_adjoint S.hL hR0 hR0'
  have hT' := (Tb_spec (κ := κ) (n := n) S hw u).1
  rw [hzb] at hT'
  have hR' : IsResolvent L κ (u : ℝ → ℂ) (parity n) (conj z) (Rfree L κ n (conj z) * S') :=
    resolvent_of_inverse hR0' hT' hS1 hS2
  obtain ⟨R, hR, -⟩ := resolvent_exists S.hL S.hr S.hr2 hu (by rw [hz]; linarith [S.hr]) hz.le
  have hRadj : ContinuousLinearMap.adjoint (Rfree L κ n (conj z) * S') = R := by
    refine resolvent_adjoint (graph_symm S.hL n (u : ℝ → ℂ)) hR' ?_
    rwa [Complex.conj_conj]
  have hS' : S' - 1 = Tb L κ n w u * S' := by
    have : S' - Tb L κ n w u * S' = 1 := by rw [← hS1, sub_mul, one_mul]
    rw [← this]; abel
  have hdiff : R - Rfree L κ n z = ContinuousLinearMap.adjoint S' *
      ContinuousLinearMap.adjoint (Tb L κ n w u) * ContinuousLinearMap.adjoint (Rfree L κ n (conj z)) := by
    rw [← hRadj, ← hadj, ← map_sub]
    have e : Rfree L κ n (conj z) * S' - Rfree L κ n (conj z) =
        Rfree L κ n (conj z) * (Tb L κ n w u * S') := by
      rw [← hS', mul_sub, mul_one]
    rw [e]
    change ContinuousLinearMap.adjoint (Rfree L κ n (conj z) ∘L (Tb L κ n w u ∘L S')) = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
    rfl
  have hne : z ≠ (pm L n : ℂ) := fun h => by
    rw [h, sub_self, norm_zero] at hz; exact S.hr.ne' hz.symm
  have hzw : z - (pm L n : ℂ) = w := by rw [hzdef]; ring
  rw [resolvent_eq hR, hdiff, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hadj,
    res_chi S.hL j hR0 rfl hne, map_smul, map_smul, adjT_chi hT' hadj n j, hzw]

/-- The weight `φ(w) = ψ(w)/w` on `|w| = r`. -/
def phi {r : ℝ} (S : Setup L r) (ψ : ℂ → ℂ) (hψ : Continuous ψ) : C(sphere (0 : ℂ) r, ℂ) :=
  ⟨fun w => ψ w * (w : ℂ)⁻¹, (hψ.comp continuous_subtype_val).mul
    (continuous_subtype_val.inv₀ fun w h => by
      have := norm_sphere w
      rw [h, norm_zero] at this
      exact S.hr.ne' this.symm)⟩

theorem Fmap_zero (κ : ℝ) {r : ℝ} (S : Setup L r) {N : ℕ} (j : Fin 2) (φ : C(sphere (0 : ℂ) r, ℂ))
    (u : Lp ℂ 2 (μI L)) {n : ℤ} (hn : ¬ (N : ℝ) < |(n : ℝ)|) : (Fmap κ S N j φ u : ℤ → H2 L) n = 0 := by
  set X := appFun (ContinuousMap.const (sphere (0 : ℂ) r) (act (maskInf (L := L) N)) *
    Ring.inverse (1 - Gclm κ S N u)) (Cclm κ S j u) with hXdef
  show ev n (Jw S.hr φ X) = 0
  rw [Jw_apply, map_smul, clm_circleIntegral _ ((ig_cont φ X).circleIntegrable S.hr.le)]
  have h0 : (∮ z in C(0, r), ev n (ig φ X z)) = ∮ z in C(0, r), (0 : H2 L) :=
    circleIntegral.integral_congr S.hr.le fun w hw => by
      show ev n (ig φ X w) = 0
      rw [ig_pos φ X hw, map_smul, hXdef, appFun_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply,
        ContinuousLinearMap.mul_apply, ev_apply, act_mask_apply, if_neg hn, smul_zero]
  rw [h0]
  simp [circleIntegral]

theorem Fmap_component (κ : ℝ) {r : ℝ} (S : Setup L r) {N : ℕ} (j : Fin 2) (ψ : ℂ → ℂ) (hψ : Continuous ψ)
    {u : Lp ℂ 2 (μI L)} (hu : ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → SqSmall L κ r n u) {n : ℤ}
    (hn : (N : ℝ) < |(n : ℝ)|) :
    (Fmap κ S N j (phi S ψ hψ) u : ℤ → H2 L) n =
      (((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C((pm L n : ℂ), r),
          ψ (z - (pm L n : ℂ)) • resolvent L κ (u : ℝ → ℂ) (parity n) z) -
        ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C((pm L n : ℂ), r),
          ψ (z - (pm L n : ℂ)) • resolvent L κ (fun _ => 0) (parity n) z)) (chi L n j) := by
  have hs : ‖Gclm κ S N u * Gclm κ S N u‖ < 1 := lt_of_le_of_lt (G_sq_le κ S N hu) (by norm_num)
  obtain ⟨Sinv, hS1C, hS2C, -⟩ :=
    QuantumNLS.TerraMultiRound35SquareInverse.square_small_inverse one_le_C (Gclm κ S N u) hs
  have hY : Ring.inverse (1 - Gclm κ S N u) = Sinv := by
    have := Ring.inverse_unit (M₀ := C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L))
      (⟨1 - Gclm κ S N u, Sinv, hS1C, hS2C⟩ : (C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L))ˣ)
    exact this
  set X := appFun (ContinuousMap.const (sphere (0 : ℂ) r) (act (maskInf (L := L) N)) *
    Ring.inverse (1 - Gclm κ S N u)) (Cclm κ S j u) with hXdef
  set φ := phi S ψ hψ with hφ
  have hA : (Fmap κ S N j φ u : ℤ → H2 L) n =
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • ∮ z in C(0, r), ev n (ig φ X z) := by
    show ev n (Jw S.hr φ X) = _
    rw [Jw_apply, map_smul, clm_circleIntegral _ ((ig_cont φ X).circleIntegrable S.hr.le)]
  have hp : ∀ w ∈ sphere (0 : ℂ) r, ev n (ig φ X w) = ψ w •
      ((resolvent L κ (u : ℝ → ℂ) (parity n) ((pm L n : ℂ) + w) - Rfree L κ n ((pm L n : ℂ) + w))
        (chi L n j)) := by
    intro w hw
    have hw' : ‖w‖ = r := mem_sphere_zero_iff_norm.1 hw
    have hzc : ‖zb L n w - (pm L n : ℂ)‖ = r := by rw [norm_zb, hw']
    obtain ⟨S', hS1, hS2, -⟩ := inverse_bound (hu n hn (zb L n w) (by rw [hzc]; linarith [S.hr]) hzc.le _ _
      (free_at (κ := κ) S hzc).1 (Tb_spec S hw' u).1)
    have hW1 : (1 - act (Ainf κ S N ⟨w, hw⟩ u)) * Sinv ⟨w, hw⟩ = 1 := by
      have := congrArg (fun F : C(sphere (0 : ℂ) r, HS L →L[ℂ] HS L) => F ⟨w, hw⟩) hS1C
      simpa only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        Gclm_apply] using this
    have ha : (Ainf κ S N ⟨w, hw⟩ u : ℤ → H2 L →L[ℂ] H2 L) n =
        ContinuousLinearMap.adjoint (Tb L κ n w u) := by
      rw [Ainf_apply, Am, if_pos hn]; rfl
    rw [ig_pos φ X hw, map_smul, hXdef, appFun_apply, hY, ContinuousMap.mul_apply, ContinuousMap.const_apply,
      ContinuousLinearMap.mul_apply, ev_apply, act_mask_apply, if_pos hn, inv_component hW1 ha hS1]
    show φ ⟨w, hw⟩ • ContinuousLinearMap.adjoint S' (Rfree L κ n ((pm L n : ℂ) + w) (Vchi κ u n j)) = _
    rw [res_sub_chi_eq S (hu n hn) hw' j hS1 hS2, smul_smul]
    rfl
  have hsph : ∀ z ∈ sphere (pm L n : ℂ) r, ‖z - (pm L n : ℂ)‖ = r := fun z hz => by
    simpa [mem_sphere_iff_norm] using hz
  have hψc : Continuous fun z : ℂ => ψ (z - (pm L n : ℂ)) := hψ.comp (continuous_id.sub continuous_const)
  have hcu : ContinuousOn (fun z => ψ (z - (pm L n : ℂ)) • resolvent L κ (u : ℝ → ℂ) (parity n) z)
      (sphere (pm L n : ℂ) r) :=
    hψc.continuousOn.smul (continuousOn_resolvent _ (Rb_nonneg L κ S.hr u) (fun z hz =>
      resolvent_exists S.hL S.hr S.hr2 (hu n hn) (by rw [hsph z hz]; linarith [S.hr]) (hsph z hz).le))
  have hc0 : ContinuousOn (fun z => ψ (z - (pm L n : ℂ)) • resolvent L κ (fun _ => 0) (parity n) z)
      (sphere (pm L n : ℂ) r) :=
    hψc.continuousOn.smul (continuousOn_resolvent _ (M := 2 / r) (div_nonneg zero_le_two S.hr.le)
      (fun z hz => free_res_annulus (κ := κ) S.hL S.hr S.hr2 (by rw [hsph z hz]; linarith [S.hr])
        (hsph z hz).le))
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    circleIntegral_apply _ (hcu.circleIntegrable S.hr.le), circleIntegral_apply _ (hc0.circleIntegrable S.hr.le),
    ← smul_sub, ← circleIntegral.integral_sub ((hcu.clm_apply continuousOn_const).circleIntegrable S.hr.le)
      ((hc0.clm_apply continuousOn_const).circleIntegrable S.hr.le), circleIntegral_shift, hA]
  congr 1
  refine circleIntegral.integral_congr S.hr.le fun w hw => ?_
  rw [hp w hw]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, add_sub_cancel_left]
  rw [← smul_sub]
  rfl

/-! ### The packaged statement -/

/-- **Real analyticity of the high-label projection and dressed columns into `ℓ²`.**  For every interval field
`u₀` there are a field-dependent cutoff `N`, a radius `ρ > 0` and maps `FP, FD : L²(0,L) → ℓ²(ℤ; L²(0,L;ℂ²))`,
real analytic on `B(u₀, ρ)`, with `FP(u)_n = (P_n(u) - P_n⁰) χ_{n,j}` and
`FD(u)_n = (D_n(u) - D_n(0)) χ_{n,j}` (`D_n = (2πi)⁻¹ ∮ (z - p_n)(z - 𝓛_u)⁻¹ dz`) for `|n| > N`, and `0` for `|n| ≤ N`. -/
theorem tail_columns_analytic [Fact (0 < L)] (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (u₀ : Lp ℂ 2 (μI L)) (j : Fin 2) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ FP FD : Lp ℂ 2 (μI L) → lp (fun _ : ℤ => H2 L) 2,
      AnalyticOnNhd ℝ FP (ball u₀ ρ) ∧ AnalyticOnNhd ℝ FD (ball u₀ ρ) ∧
      ∀ u ∈ ball u₀ ρ, ∀ n : ℤ,
        (FP u : ℤ → H2 L) n = (if (N : ℝ) < |(n : ℝ)| then
          (perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r) (chi L n j) else 0) ∧
        (FD u : ℤ → H2 L) n = (if (N : ℝ) < |(n : ℝ)| then
          (dressedIntegral L κ (u : ℝ → ℂ) n r - dressedIntegral L κ (fun _ => 0) n r) (chi L n j) else 0) := by
  have S : Setup L r := ⟨hL, hr, hr2⟩
  obtain ⟨N, ρ, hρ, h⟩ := square_small (κ := κ) hL hr hr2 u₀
  have hsq : ∀ u ∈ ball u₀ ρ, ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → SqSmall L κ r n u :=
    fun u hu n hn z h1 h2 R0 T hR0 hT =>
      h n hn u (by simpa [dist_eq_norm] using hu) z h1 h2 R0 T hR0 hT
  have hs : ∀ u ∈ ball u₀ ρ, ‖Gclm κ S N u * Gclm κ S N u‖ < 1 := fun u hu =>
    lt_of_le_of_lt (G_sq_le κ S N (hsq u hu)) (by norm_num)
  refine ⟨N, ρ, hρ, Fmap κ S N j (phi S (fun _ => 1) continuous_const),
    Fmap κ S N j (phi S (fun w => w) continuous_id), fun u hu => Fmap_analyticAt κ S N j _ (hs u hu),
    fun u hu => Fmap_analyticAt κ S N j _ (hs u hu), fun u hu n => ?_⟩
  split_ifs with hn
  · refine ⟨?_, ?_⟩
    · rw [Fmap_component κ S j _ continuous_const (hsq u hu) hn]
      simp only [one_smul]
      rfl
    · rw [Fmap_component κ S j (fun w => w) continuous_id (hsq u hu) hn]
      rfl
  · exact ⟨Fmap_zero κ S j _ u hn, Fmap_zero κ S j _ u hn⟩

end QuantumNLS.RB01L2Factor
#print axioms QuantumNLS.RB01L2Factor.act
#print axioms QuantumNLS.RB01L2Factor.inv_component
#print axioms QuantumNLS.RB01L2Factor.Ainf_lip
#print axioms QuantumNLS.RB01L2Factor.G_sq_le
#print axioms QuantumNLS.RB01L2Factor.inv_analyticAt
#print axioms QuantumNLS.RB01L2Factor.colS_lip
#print axioms QuantumNLS.RB01L2Factor.Fmap_analyticAt
#print axioms QuantumNLS.RB01L2Factor.res_sub_chi_eq
#print axioms QuantumNLS.RB01L2Factor.Fmap_component
#print axioms QuantumNLS.RB01L2Factor.tail_columns_analytic
