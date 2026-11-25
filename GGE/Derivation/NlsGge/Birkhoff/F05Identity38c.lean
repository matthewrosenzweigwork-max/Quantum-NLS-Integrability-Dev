import NlsGge.Birkhoff.F05Identity38b

/-! # F05, file c: the continuous difference `D_m` and the finite energy identity (F05.02, F05.03)

v2 `B:eq:D`: `D_m(x) = V_m(𝓕⁻¹x) - R_m(𝓕⁻¹x)` on `E = h^{m-1}`, and for `x ∈ H`
`D_m(x) = A_m(Tx) - A_m(x)` with `A_m(x) = Σ a_{m,n}|x_n|²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.Ramer.General Filter Topology
open scoped ENNReal

theorem finiteHierarchyRate38_neg (m : ℕ) (β : ℕ → ℝ) (n : ℤ) :
    finiteHierarchyRate38 m β (-n) = finiteHierarchyRate38 m β n := by
  unfold finiteHierarchyRate38 finiteHierarchyW38
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [mul_neg, Even.neg_pow (even_two_mul j)]

theorem physical_ext38 {u v : PhysicalL2} (h : ∀ n, physicalFourier u n = physicalFourier v n) :
    u = v := by
  apply fourierSeq38_injective
  funext n
  rw [fourierSeq38_apply, fourierSeq38_apply, h]

section D

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

/-- `𝓕⁻¹ : E → H^{m-1}` (isometric). -/
def physE05 (x : (S05 m β hm hβ).E) : Hm1 m :=
  FinvH38 m (ofCarrier38 _ ((Eq05 m β hm hβ).symm x))

theorem continuous_physE05 : Continuous (physE05 (m := m) (β := β) hm hβ) :=
  (continuous_FinvH38 m).comp ((continuous_ofCarrier38 _).comp (Eq05 m β hm hβ).symm.continuous)

/-- **`D_m`** (v2 `B:eq:D`). -/
def D05 (x : (S05 m β hm hβ).E) : ℝ := Vm38 m β (physE05 hm hβ x) - Rm38 m β (physE05 hm hβ x)

theorem continuous_D05 : Continuous (D05 (m := m) (β := β) hm hβ) :=
  ((continuous_Vm38 hm hβ).comp (continuous_physE05 hm hβ)).sub
    ((continuous_Rm38 hm hβ).comp (continuous_physE05 hm hβ))


theorem hcoord_incl_eq05 (v : (S05 m β hm hβ).H) (n : ℤ) :
    carrierCoe38 _ ((Eq05 m β hm hβ).symm ((S05 m β hm hβ).incl v)) n =
      (S05 m β hm hβ).hcoord v n := by
  have := coord_Eq05 m β hm hβ ((Eq05 m β hm hβ).symm ((S05 m β hm hβ).incl v)) n
  rw [LinearIsometryEquiv.apply_symm_apply, (S05 m β hm hβ).coord_incl] at this
  exact this.symm

/-- **F05.03.** On a finitely supported `v ∈ H`:
`D_m(v) = (‖v + K v‖²_H - ‖v‖²_H)/2 = A_m(Tv) - A_m(v)`. -/
theorem D05_finite (v : (S05 m β hm hβ).H) (N : ℕ)
    (hv : ∀ n ∉ symmetricModes N, (S05 m β hm hβ).hcoord v n = 0) :
    D05 hm hβ ((S05 m β hm hβ).incl v) =
      (‖v + K05 B O hm hβ ((S05 m β hm hβ).incl v)‖ ^ 2 - ‖v‖ ^ 2) / 2 := by
  set a := (Eq05 m β hm hβ).symm ((S05 m β hm hβ).incl v) with ha
  have hac : ∀ n, carrierCoe38 _ a n = (S05 m β hm hβ).hcoord v n := hcoord_incl_eq05 hm hβ v
  have hfin : {n : ℤ | (S05 m β hm hβ).hcoord v n ≠ 0}.Finite :=
    (symmetricModes N).finite_toSet.subset fun n hn => by
      by_contra h; exact hn (hv n h)
  -- the physical field of Fourier coefficients `û(n) = -a(-n)`, in `H^m`
  have hfin' : {n : ℤ | -(S05 m β hm hβ).hcoord v (-n) ≠ 0}.Finite := by
    have := hfin.preimage (Equiv.neg ℤ).injective.injOn
    refine this.subset fun n hn => ?_
    simpa using hn
  set y : SobolevHilbert (m : ℝ) :=
    ofCarrier38 _ (carrierMk38 (m : ℝ) (fun n => -(S05 m β hm hβ).hcoord v (-n))
      (finiteSupport_mem_seqSobolev38 _ _ hfin')) with hy
  set y' : Hm1 m := physE05 hm hβ ((S05 m β hm hβ).incl v) with hy'
  have hyc : ∀ n, (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n =
      -(S05 m β hm hβ).hcoord v (-n) := fun n => rfl
  have hy'c : ∀ n, (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n =
      -(S05 m β hm hβ).hcoord v (-n) := fun n => by
    show -(carrierCoe38 _ a (-n)) = _
    rw [hac]
  have hyy : ∀ n, (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y') n := fun n => by
    rw [hyc, hy'c]
  obtain ⟨hs1, hs2, hE, hs4, -, hV⟩ := (F04_spectral_lemma38 m hm β hβ).2.2 y
  have hV' := hV y' hyy
  have hu : sobolevToL2_38 m y = sobolevToL2_38 (m - 1) y' := by
    apply physical_ext38
    intro n
    rw [sobolevToL2_38_fourier, sobolevToL2_38_fourier, hyy]
  -- Birkhoff coordinates of `u`
  have hF : fourierSeq38 (sobolevToL2_38 m y) = carrierCoe38 _ a := by
    funext n
    rw [fourierSeq38_apply, sobolevToL2_38_fourier, hyc, hac]; simp
  have hH1 : SobolevSquareSummable 1 (physicalFourier (sobolevToL2_38 m y)) := by
    have := sobolevSquareSummable_restrict 1 (m : ℝ) (by exact_mod_cast (by omega : 1 ≤ m)) _
      (sobolevToL2_38_sobolev m y)
    exact this
  have hI : ∀ n, actualGapActionAllE02_38 (sobolevToL2_38 m y) n =
      ‖B.T (carrierCoe38 _ a) n‖ ^ 2 := fun n => by
    rw [← B.action _ hH1 n, hF]
  have hR : Rm38 m β y' = ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β)
      ((sobolevToL2_38 m) y) n := by
    unfold Rm38; rw [hu]
  have hVV : Vm38 m β y' = localRemainderSobolev38 m β (toCarrier38 _ y') := rfl
  -- reindex the Fourier-side sum
  have hrate : ∀ n, finiteHierarchyRate38 m β (-n) = finiteHierarchyRate38 m β n :=
    finiteHierarchyRate38_neg m β
  have hA : ∑' n : ℤ, finiteHierarchyRate38 m β n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n‖ ^ 2 =
      ∑' n : ℤ, finiteHierarchyRate38 m β n * ‖(S05 m β hm hβ).hcoord v n‖ ^ 2 := by
    rw [← (Equiv.neg ℤ).tsum_eq (fun n => finiteHierarchyRate38 m β n * ‖(S05 m β hm hβ).hcoord v n‖ ^ 2)]
    refine tsum_congr fun n => ?_
    simp only [Equiv.neg_apply, hyc, hrate, norm_neg]
  have hT : ∀ n, (S05 m β hm hβ).hcoord (v + K05 B O hm hβ ((S05 m β hm hβ).incl v)) n = B.T (carrierCoe38 _ a) n := by
    intro n
    have h1 : (S05 m β hm hβ).incl v = (Eq05 m β hm hβ) a := by rw [ha]; simp
    rw [(S05 m β hm hβ).hcoord_add, h1, hcoord_K05, hac n]
    ring
  have hn1 : ∀ w : (S05 m β hm hβ).H, ‖w‖ ^ 2 =
      2 * ∑' n : ℤ, finiteHierarchyRate38 m β n * ‖(S05 m β hm hβ).hcoord w n‖ ^ 2 := by
    intro w
    rw [(S05 m β hm hβ).hnorm_sq, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    show 2 * finiteHierarchyRate38 m β n * _ = _
    ring
  have hIs : ∑' n : ℤ, finiteHierarchyRate38 m β n * actualGapActionAllE02_38 (sobolevToL2_38 m y) n =
      ∑' n : ℤ, finiteHierarchyRate38 m β n * ‖(S05 m β hm hβ).hcoord (v + K05 B O hm hβ ((S05 m β hm hβ).incl v)) n‖ ^ 2 := by
    refine tsum_congr fun n => ?_
    rw [hI, hT]
  have hE' : energySobolev38 m β y = ∑' n : ℤ, finiteHierarchyRate38 m β n *
      actualGapActionAllE02_38 (sobolevToL2_38 m y) n + Rm38 m β y' := by
    rw [hE, hR]
    rfl
  unfold D05
  rw [hn1 (v + K05 B O hm hβ ((S05 m β hm hβ).incl v)), hn1 v, ← hIs]
  have := hV'
  rw [hA] at this
  rw [← hVV] at this
  linarith


end D

/-- Orthogonality in `H`: for `v` supported in `|n| ≤ N`, `‖v+w‖² = ‖v + P_N w‖² + ‖w - P_N w‖²`. -/
theorem norm_sq_add_trunc05 (S : RamerSetting) (N : ℕ) (v w : S.H)
    (hv : ∀ n ∉ symmetricModes N, S.hcoord v n = 0) :
    ‖v + w‖ ^ 2 = ‖v + ((S.cmTrunc N w : S.head N) : S.H)‖ ^ 2 +
      ‖w - ((S.cmTrunc N w : S.head N) : S.H)‖ ^ 2 := by
  set Pw : S.H := ((S.cmTrunc N w : S.head N) : S.H) with hPw
  have h1 := S.hasSum_H (v + w)
  have h2 := S.hasSum_H (v + Pw)
  have h3 := S.hasSum_H (w - Pw)
  have h4 := h2.add h3
  have hpt : ∀ n, S.cmWeight n * ‖S.hcoord (v + w) n‖ ^ 2 =
      S.cmWeight n * ‖S.hcoord (v + Pw) n‖ ^ 2 + S.cmWeight n * ‖S.hcoord (w - Pw) n‖ ^ 2 := by
    intro n
    have hP : S.hcoord Pw n = if n ∈ symmetricModes N then S.hcoord w n else 0 :=
      S.hcoord_cmTrunc N w n
    have e1 : S.hcoord (v + w) n = S.hcoord v n + S.hcoord w n := S.hcoord_add _ _ _
    have e2 : S.hcoord (v + Pw) n = S.hcoord v n + S.hcoord Pw n := S.hcoord_add _ _ _
    have e3 : S.hcoord (w - Pw) n = S.hcoord w n - S.hcoord Pw n := rfl
    by_cases hn : n ∈ symmetricModes N
    · simp only [hn, ↓reduceIte] at hP
      rw [e1, e2, e3, hP]
      simp
    · have hv0 := hv n hn
      simp only [hn, ↓reduceIte] at hP
      rw [e1, e2, e3, hP, hv0]
      simp
  have h5 : HasSum (fun n => S.cmWeight n * ‖S.hcoord (v + w) n‖ ^ 2)
      (‖v + Pw‖ ^ 2 + ‖w - Pw‖ ^ 2) := by
    simp only [hpt]; exact h4
  exact h1.unique h5


section Tendsto

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

theorem continuous_K05 : Continuous (K05 B O hm hβ) :=
  continuousOn_univ.1 (analytic_K05 B O hm hβ).continuousOn

/-- **F05.04.** The finite quadratic-energy difference of the truncated map converges to `D_m`:
`(‖ψ_N(x_N)‖²_H - ‖x_N‖²_H)/2 → D_m(x)`, with `ψ_N = P_N T P_N` and `x_N = P_N x`
(deterministic, for every sample whose realization has coordinates `z`). -/
theorem tendsto_energy05 (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, (S05 m β hm hβ).coord n ((S05 m β hm hβ).R z) = z n) :
    Tendsto (fun N : ℕ =>
      (‖((S05 m β hm hβ).headPt N z : (S05 m β hm hβ).head N) +
          (S05 m β hm hβ).truncField (K05 B O hm hβ) N ((S05 m β hm hβ).headPt N z)‖ ^ 2 -
        ‖((S05 m β hm hβ).headPt N z : (S05 m β hm hβ).head N)‖ ^ 2) / 2)
      atTop (𝓝 (D05 hm hβ ((S05 m β hm hβ).R z))) := by
  set S := S05 m β hm hβ with hS
  set K := K05 B O hm hβ with hK
  set xN : ℕ → S.E := fun N => S.headToE N (S.headPt N z) with hxN
  have hx : Tendsto xN atTop (𝓝 (S.R z)) := S.tendsto_headToE_headPt z hz
  have hD := ((continuous_D05 hm hβ).tendsto _).comp hx
  have hKt : Tendsto (fun N => K (xN N)) atTop (𝓝 (K (S.R z))) :=
    ((continuous_K05 B O hm hβ).tendsto _).comp hx
  have hP := S.tendsto_cmTrunc_comp K (continuous_K05 B O hm hβ) xN (S.R z) hx
  have hdiff : Tendsto (fun N => ‖K (xN N) -
      ((S.cmTrunc N (K (xN N)) : S.head N) : S.H)‖ ^ 2 / 2) atTop (𝓝 0) := by
    have h1 := hKt.sub hP
    rw [sub_self] at h1
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 h1)
    simp only [sub_zero] at h2
    have h3 := (h2.pow 2).div_const 2
    simpa using h3
  have key : ∀ N : ℕ, (‖((S.headPt N z : S.head N) +
          S.truncField K N (S.headPt N z) : S.head N)‖ ^ 2 -
        ‖((S.headPt N z : S.head N))‖ ^ 2) / 2 =
      D05 hm hβ (xN N) - ‖K (xN N) - ((S.cmTrunc N (K (xN N)) : S.head N) : S.H)‖ ^ 2 / 2 := by
    intro N
    set v := S.headPt N z with hv
    have hv0 : ∀ n ∉ symmetricModes N, S.hcoord (v : S.H) n = 0 := fun n hn => v.2 n hn
    have hD1 := D05_finite B O hm hβ (v : S.H) N hv0
    have hinc : S.incl (v : S.H) = xN N := rfl
    rw [hinc] at hD1
    have hort := norm_sq_add_trunc05 S N (v : S.H) (K (xN N)) hv0
    rw [← hinc] at hort
    have hnorm : ‖((v : S.head N) + S.truncField K N v : S.head N)‖ =
        ‖(v : S.H) + ((S.cmTrunc N (K (xN N)) : S.head N) : S.H)‖ := rfl
    rw [hnorm, hD1]
    rw [hinc] at hort
    have : ‖(v : S.head N)‖ = ‖(v : S.H)‖ := rfl
    rw [this]
    linarith
  refine Tendsto.congr (fun N => (key N).symm) ?_
  simpa using hD.sub hdiff

end Tendsto

end NlsGge.Birkhoff
