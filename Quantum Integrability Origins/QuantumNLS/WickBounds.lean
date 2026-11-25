import QuantumNLS.WickSymbols
import QuantumNLS.OccupationHilbert
import QuantumNLS.SpectralUpperBound

/-!
# `eq:full-product-bound` and `eq:full-Dirac-bound` (finite-support form)

Source: `chapters/core/wick_calculus.tex` (`thm:full-wick`): with
`C(f,g) = ∑_{|γ|≥2} (1/γ!) ‖(∂_z^γ f)(∂_{z̄}^γ g)‖_coeff`,
`‖W_N(f)W_N(g) − W_N(fg) − N⁻¹ W_N(S_1(f,g) + i{f,g}/2)‖ ≤ C(f,g) N⁻²`,
`‖−iN[W_N(f), W_N(g)] − W_N({f,g})‖ ≤ (C(f,g) + C(g,f)) N⁻¹`,
bracket convention `{w_a, w̄_b} = −iδ_ab` (`coordinate_conventions.tex`, `eq:birkhoff`).
Imports the frozen `WickSymbols.lean` (`ed97e53a`).  Here the bounds are proved as bounds of
`nrm` on finitely supported vectors of the `N`-sector for the ungauged algebraic Wick map.
No actual Bethe gauge and no physical identification is asserted.
-/

namespace QuantumNLS.WickBounds

open QuantumNLS.Occupation QuantumNLS.WickSymbols

noncomputable section

/-- Labels occurring in the `z`-exponents of `f`. -/
def labelsOf (f : Sym) : Finset ℤ := f.coeff.support.biUnion (fun p => p.1.support)

/-- All multi-indices `γ` of degree `≥ 2` below some `α` occurring in `f`. -/
def Rset (f : Sym) : Finset (ℤ →₀ ℕ) :=
  (f.coeff.support.biUnion (fun p => Finset.Iic p.1)).filter (fun γ => 2 ≤ γ.degree)

/-- `C(f,g) = ∑_{|γ|≥2} (1/γ!) ‖(∂_z^γ f)(∂_{z̄}^γ g)‖_coeff` (`eq:full-Cfg`); terms with
`γ ≰ α` vanish, so the sum over `Rset f` is the full sum. -/
def Cfg (f g : Sym) : ℝ :=
  ∑ γ ∈ Rset f, ((mfac γ : ℕ) : ℝ)⁻¹ * coeffNorm (dz γ f * dzb γ g)

lemma Cfg_nonneg (f g : Sym) : 0 ≤ Cfg f g :=
  Finset.sum_nonneg (fun γ _ => mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

lemma split_hyp_S (f : Sym) {S : Finset ℤ} (hS : labelsOf f ⊆ S) :
    ∀ p ∈ f.coeff.support, ∀ a, Finsupp.single a 1 ≤ p.1 → a ∈ S := by
  intro p hp a ha
  apply hS
  unfold labelsOf
  rw [Finset.mem_biUnion]
  refine ⟨p, hp, ?_⟩
  rw [Finsupp.mem_support_iff]
  have := ha a
  simp at this
  omega

lemma split_hyp_R (f : Sym) :
    ∀ p ∈ f.coeff.support, ∀ γ ∈ Finset.Iic p.1, 2 ≤ γ.degree → γ ∈ Rset f := by
  intro p hp γ hγ hd
  unfold Rset
  rw [Finset.mem_filter, Finset.mem_biUnion]
  exact ⟨⟨p, hp, hγ⟩, hd⟩

lemma split_hyp_R2 (f : Sym) : ∀ γ ∈ Rset f, 2 ≤ γ.degree := by
  intro γ hγ
  exact (Finset.mem_filter.mp hγ).2

/-- The remainder of `wick_product_split`, applied to a vector. -/
theorem remainder_eq (N : ℕ) (f g : Sym) {S : Finset ℤ} (hS : labelsOf f ⊆ S) (v : FS) :
    (WN N f * WN N g) v = WN N (f * g) v + (N : ℂ)⁻¹ • WN N (S1 S f g + (Complex.I / 2) • pb S f g) v
      + ∑ γ ∈ Rset f, wickWeight N γ • WN N (dz γ f * dzb γ g) v := by
  have h := wick_product_split N f g S (Rset f) (split_hyp_S f hS) (split_hyp_R f) (split_hyp_R2 f)
  rw [← C1_eq_S1_add_pb] at *
  have := LinearMap.congr_fun h v
  simpa only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply] using this

lemma norm_wickWeight (N : ℕ) (γ : ℤ →₀ ℕ) :
    ‖wickWeight N γ‖ = ((N : ℝ)⁻¹) ^ γ.degree * ((mfac γ : ℕ) : ℝ)⁻¹ := by
  simp [wickWeight, norm_pow, norm_inv]

/-- Norm of the remainder: `≤ C(f,g) N⁻² ‖v‖` for `N ≥ 1` (constants exactly as in the source). -/
theorem remainder_nrm_le {N : ℕ} (hN : 0 < N) {f g : Sym} (hf : Balanced f) (hg : Balanced g)
    {v : FS} (hv : InSector N v) :
    nrm (∑ γ ∈ Rset f, wickWeight N γ • WN N (dz γ f * dzb γ g) v)
      ≤ Cfg f g * ((N : ℝ)⁻¹) ^ 2 * nrm v := by
  refine (nrm_sum_le _ _).trans ?_
  unfold Cfg
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum (fun γ hγ => ?_)
  rw [nrm_smul, norm_wickWeight]
  have hb := (hf.dz_mul_dzb hg γ)
  have h1 := WN_norm_le hN hb hv
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hinv : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNr
  have hpow : ((N : ℝ)⁻¹) ^ γ.degree ≤ ((N : ℝ)⁻¹) ^ 2 :=
    pow_le_pow_of_le_one (by positivity) hinv (split_hyp_R2 f γ hγ)
  have hm : 0 ≤ ((mfac γ : ℕ) : ℝ)⁻¹ := by positivity
  calc ((N : ℝ)⁻¹ ^ γ.degree * ((mfac γ : ℕ) : ℝ)⁻¹) * nrm (WN N (dz γ f * dzb γ g) v)
      ≤ ((N : ℝ)⁻¹ ^ γ.degree * ((mfac γ : ℕ) : ℝ)⁻¹) * (coeffNorm (dz γ f * dzb γ g) * nrm v) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (((N : ℝ)⁻¹) ^ 2 * ((mfac γ : ℕ) : ℝ)⁻¹) * (coeffNorm (dz γ f * dzb γ g) * nrm v) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hpow hm
        · exact mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (nrm_nonneg v)
    _ = ((mfac γ : ℕ) : ℝ)⁻¹ * coeffNorm (dz γ f * dzb γ g) * ((N : ℝ)⁻¹) ^ 2 * nrm v := by ring

/-- **`eq:full-product-bound`** (finite-support, ungauged): for balanced `f,g`, `N ≥ 1` and a vector
`v` supported on arrays of total `N`,
`‖(W_N(f)W_N(g) − W_N(fg) − N⁻¹ W_N(S_1(f,g) + i{f,g}/2)) v‖ ≤ C(f,g) N⁻² ‖v‖`. -/
theorem full_product_bound {N : ℕ} (hN : 0 < N) {f g : Sym} (hf : Balanced f) (hg : Balanced g)
    {S : Finset ℤ} (hS : labelsOf f ⊆ S) {v : FS} (hv : InSector N v) :
    nrm ((WN N f * WN N g) v - WN N (f * g) v
        - (N : ℂ)⁻¹ • WN N (S1 S f g + (Complex.I / 2) • pb S f g) v)
      ≤ Cfg f g * ((N : ℝ)⁻¹) ^ 2 * nrm v := by
  have e := remainder_eq N f g hS v
  have : (WN N f * WN N g) v - WN N (f * g) v
        - (N : ℂ)⁻¹ • WN N (S1 S f g + (Complex.I / 2) • pb S f g) v
      = ∑ γ ∈ Rset f, wickWeight N γ • WN N (dz γ f * dzb γ g) v := by
    rw [e]; abel
  rw [this]
  exact remainder_nrm_le hN hf hg hv

lemma S1_comm (S : Finset ℤ) (f g : Sym) : S1 S g f = S1 S f g := by
  unfold S1; rw [add_comm]

lemma pb_swap (S : Finset ℤ) (f g : Sym) : pb S g f = -pb S f g := by
  unfold pb
  rw [← smul_neg, neg_sub]

/-- **`eq:full-Dirac-bound`** (finite-support, ungauged), bracket convention `{w_a, w̄_b} = −iδ_ab`:
`‖(−iN[W_N(f), W_N(g)] − W_N({f,g})) v‖ ≤ (C(f,g) + C(g,f)) N⁻¹ ‖v‖` for balanced `f,g`,
`N ≥ 1`, `v` of sector `N` (`S` any label set containing the labels of both). -/
theorem full_Dirac_bound {N : ℕ} (hN : 0 < N) {f g : Sym} (hf : Balanced f) (hg : Balanced g)
    {S : Finset ℤ} (hSf : labelsOf f ⊆ S) (hSg : labelsOf g ⊆ S) {v : FS} (hv : InSector N v) :
    nrm ((-(Complex.I) * (N : ℂ)) • ((WN N f * WN N g) v - (WN N g * WN N f) v)
        - WN N (pb S f g) v)
      ≤ (Cfg f g + Cfg g f) * (N : ℝ)⁻¹ * nrm v := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have e1 := remainder_eq N f g hSf v
  have e2 := remainder_eq N g f hSg v
  rw [mul_comm g f, S1_comm S f g, pb_swap] at e2
  rw [e1, e2]
  -- the first-order terms recombine to `W_N({f,g})`
  have hI : (Complex.I / 2) • pb S f g - (Complex.I / 2) • (-pb S f g) = Complex.I • pb S f g := by
    rw [smul_neg, sub_neg_eq_add, ← add_smul]; congr 1; ring
  set A := WN N (f * g) v with hA
  set X := WN N (S1 S f g + (Complex.I / 2) • pb S f g) v with hX
  set Y := WN N (S1 S f g + (Complex.I / 2) • -pb S f g) v with hY
  set P := WN N (pb S f g) v with hP
  set R1 := ∑ γ ∈ Rset f, wickWeight N γ • WN N (dz γ f * dzb γ g) v with hR1
  set R2 := ∑ γ ∈ Rset g, wickWeight N γ • WN N (dz γ g * dzb γ f) v with hR2
  have hXY : X - Y = Complex.I • P := by
    have h : WN N ((S1 S f g + (Complex.I / 2) • pb S f g) - (S1 S f g + (Complex.I / 2) • -pb S f g)) v
        = X - Y := by rw [map_sub]; rfl
    rw [← h, add_sub_add_left_eq_sub, hI, map_smul]
    rfl
  have hc : -(Complex.I) * (N : ℂ) * (N : ℂ)⁻¹ * Complex.I = 1 := by
    calc -(Complex.I) * (N : ℂ) * (N : ℂ)⁻¹ * Complex.I
        = -(Complex.I * Complex.I) * ((N : ℂ) * (N : ℂ)⁻¹) := by ring
      _ = 1 := by rw [Complex.I_mul_I, mul_inv_cancel₀ hN0]; norm_num
  have h1 : (A + (N : ℂ)⁻¹ • X + R1) - (A + (N : ℂ)⁻¹ • Y + R2)
      = (N : ℂ)⁻¹ • (X - Y) + (R1 - R2) := by module
  have key : (-(Complex.I) * (N : ℂ)) • ((A + (N : ℂ)⁻¹ • X + R1) - (A + (N : ℂ)⁻¹ • Y + R2)) - P
      = (-(Complex.I) * (N : ℂ)) • (R1 - R2) := by
    rw [h1, hXY, smul_add, smul_smul, smul_smul, hc, one_smul]
    abel
  rw [key]
  -- bound
  have b1 := remainder_nrm_le hN hf hg hv
  have b2 := remainder_nrm_le hN hg hf hv
  have hsub : nrm (R1 - R2) ≤ nrm R1 + nrm R2 := by
    have := nrm_add_le R1 ((-1 : ℂ) • R2)
    rw [nrm_smul] at this
    simpa [sub_eq_add_neg] using this
  rw [nrm_smul]
  have hnorm : ‖-(Complex.I) * (N : ℂ)‖ = (N : ℝ) := by simp
  rw [hnorm]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc (N : ℝ) * nrm (R1 - R2) ≤ (N : ℝ) * (nrm R1 + nrm R2) :=
        mul_le_mul_of_nonneg_left hsub hNr.le
    _ ≤ (N : ℝ) * (Cfg f g * ((N : ℝ)⁻¹) ^ 2 * nrm v + Cfg g f * ((N : ℝ)⁻¹) ^ 2 * nrm v) :=
        mul_le_mul_of_nonneg_left (add_le_add b1 b2) hNr.le
    _ = (Cfg f g + Cfg g f) * (N : ℝ)⁻¹ * nrm v := by field_simp

/-! ### Closure properties and sector invariance -/

theorem balanced_add {f g : Sym} (hf : Balanced f) (hg : Balanced g) : Balanced (f + g) := by
  intro p hp
  have : p ∈ f.coeff.support ∪ g.coeff.support := by
    have := Finsupp.support_add (g₁ := f.coeff) (g₂ := g.coeff)
    exact this (by simpa [AddMonoidAlgebra.coeff_add] using hp)
  rcases Finset.mem_union.mp this with h | h
  · exact hf p h
  · exact hg p h

theorem balanced_smul (c : ℂ) {f : Sym} (hf : Balanced f) : Balanced (c • f) := by
  intro p hp
  apply hf p
  have := Finsupp.support_smul (b := c) (g := f.coeff)
  exact this (by simpa [AddMonoidAlgebra.coeff_smul] using hp)

theorem balanced_zero : Balanced (0 : Sym) := by
  intro p hp; simp at hp

theorem balanced_sum {ι : Type*} (s : Finset ι) (F : ι → Sym) (h : ∀ i ∈ s, Balanced (F i)) :
    Balanced (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using balanced_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact balanced_add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem balanced_neg {f : Sym} (hf : Balanced f) : Balanced (-f) := by
  have := balanced_smul (-1 : ℂ) hf
  simpa using this

theorem balanced_sub {f g : Sym} (hf : Balanced f) (hg : Balanced g) : Balanced (f - g) := by
  rw [sub_eq_add_neg]; exact balanced_add hf (balanced_neg hg)

theorem balanced_C1 (S : Finset ℤ) {f g : Sym} (hf : Balanced f) (hg : Balanced g) :
    Balanced (C1 S f g) :=
  balanced_sum _ _ (fun a _ => hf.dz_mul_dzb hg (Finsupp.single a 1))

theorem balanced_S1 (S : Finset ℤ) {f g : Sym} (hf : Balanced f) (hg : Balanced g) :
    Balanced (S1 S f g) :=
  balanced_smul _ (balanced_add (balanced_C1 S hf hg) (balanced_C1 S hg hf))

theorem balanced_pb (S : Finset ℤ) {f g : Sym} (hf : Balanced f) (hg : Balanced g) :
    Balanced (pb S f g) :=
  balanced_smul _ (balanced_sub (balanced_C1 S hf hg) (balanced_C1 S hg hf))

lemma eq_zero_of_ip_self_re {u : FS} (h : (ip u u).re = 0) : u = 0 := by
  rw [ip_self_re] at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp h
  ext m
  by_cases hm : m ∈ u.support
  · have := h0 m hm
    simpa using this
  · simpa using Finsupp.notMem_support_iff.mp hm

/-- Balanced Wick monomials preserve the `N`-sector (for `d > N` they vanish). -/
theorem WMono_inSector {N : ℕ} {α β : ℤ →₀ ℕ} (hαβ : β.degree = α.degree) {v : FS}
    (hv : InSector N v) : InSector N (WMono N α β v) := by
  unfold WMono AnnMono CreMono
  rw [LinearMap.smul_apply, Module.End.mul_apply]
  have hlen : (labels β).length = (labels α).length := by
    rw [labels_length, labels_length, hαβ]
  obtain ⟨hA1, hA2⟩ := AnnProd_bound (labels α) hv
  obtain ⟨hC1, _⟩ := CreProd_bound (labels β) hA1
  by_cases hd : α.degree ≤ N
  · intro m hm
    have hsup := Finsupp.support_smul hm
    have := hC1 m hsup
    rw [hlen, labels_length] at this
    omega
  · have hz : fall N (labels α).length = 0 := by
      rw [labels_length]; exact fall_eq_zero (by omega)
    have h0 : AnnProd (labels α) v = 0 := by
      apply eq_zero_of_ip_self_re
      have := hA2
      rw [hz] at this
      have hnn : 0 ≤ (ip (AnnProd (labels α) v) (AnnProd (labels α) v)).re := by
        rw [ip_self_re]; exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
      simp at this
      linarith
    rw [h0]
    simp [map_zero]
    intro m hm; simp at hm

lemma inSector_add {k : ℕ} {u v : FS} (hu : InSector k u) (hv : InSector k v) :
    InSector k (u + v) := by
  intro m hm
  have := Finsupp.support_add hm
  rcases Finset.mem_union.mp this with h | h
  · exact hu m h
  · exact hv m h

lemma inSector_smul {k : ℕ} (c : ℂ) {u : FS} (hu : InSector k u) : InSector k (c • u) := by
  intro m hm
  exact hu m (Finsupp.support_smul hm)

lemma inSector_zero (k : ℕ) : InSector k (0 : FS) := by
  intro m hm; simp at hm

lemma inSector_sum {ι : Type*} (s : Finset ι) (F : ι → FS) {k : ℕ}
    (h : ∀ i ∈ s, InSector k (F i)) : InSector k (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inSector_zero k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inSector_add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Balanced Wick operators preserve the `N`-sector. -/
theorem WN_inSector {N : ℕ} {h : Sym} (hb : Balanced h) {v : FS} (hv : InSector N v) :
    InSector N (WN N h v) := by
  have e : WN N h v = ∑ p ∈ h.coeff.support, h.coeff p • WMono N p.1 p.2 v := by
    have : WN N h = ∑ p ∈ h.coeff.support, h.coeff p • WMono N p.1 p.2 := symLin_expand _ h
    rw [this, LinearMap.sum_apply]; rfl
  rw [e]
  exact inSector_sum _ _ (fun p hp => inSector_smul _
    (WMono_inSector (hb p hp).symm hv))

/-! ### The Wick operators on the sector and on `ℓ²(𝓜_N)` -/

open QuantumNLS.OccupationHilbert

/-- `W_N(h)` on finitely supported functions on `𝓜_N` (restriction of `WN` along `emb`). -/
def WS (N : ℕ) (h : Sym) : Sector N →ₗ[ℂ] Sector N :=
  (Finsupp.lcomapDomain (Subtype.val : Arr N → Occ) Subtype.val_injective).comp
    ((WN N h).comp (emb N))

lemma WS_apply (N : ℕ) (h : Sym) (v : Sector N) (m : Arr N) :
    WS N h v m = WN N h (emb N v) m.1 := by
  simp [WS]

theorem emb_WS {N : ℕ} {h : Sym} (hb : Balanced h) (v : Sector N) :
    emb N (WS N h v) = WN N h (emb N v) := by
  have hs : InSector N (WN N h (emb N v)) := by
    apply WN_inSector hb
    intro m hm
    obtain ⟨m', _, rfl⟩ := emb_support v hm
    exact m'.2
  ext m
  by_cases hm : ∃ m' : Arr N, m'.1 = m
  · obtain ⟨m', rfl⟩ := hm
    rw [emb_apply N (WS N h v) m', WS_apply]
  · have h1 : emb N (WS N h v) m = 0 := by
      simp only [emb, Finsupp.lmapDomain_apply]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨m', hm'⟩
      exact hm ⟨m', hm'⟩
    rw [h1]
    by_contra hne
    have := hs m (Finsupp.mem_support_iff.mpr (Ne.symm hne))
    exact hm ⟨⟨m, this⟩, rfl⟩

/-- `‖core v‖ = ‖v‖_{ℓ²}` computed on the embedded vector. -/
lemma norm_core_eq (N : ℕ) (u : Sector N) : ‖core N u‖ = nrm (emb N u) := by
  have h2 : ‖core N u‖ ^ 2 = (ip (emb N u) (emb N u)).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rw [inner_core]
    rfl
  rw [← nrm_sq] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (nrm_nonneg _)).mp h2

lemma inSector_emb {N : ℕ} (v : Sector N) : InSector N (emb N v) := by
  intro m hm
  obtain ⟨m', _, rfl⟩ := emb_support v hm
  exact m'.2

lemma core_WS_bound {N : ℕ} (hN : 0 < N) {h : Sym} (hb : Balanced h) (v : Sector N) :
    ‖core N (WS N h v)‖ ≤ coeffNorm h * ‖core N v‖ := by
  rw [norm_core_eq, norm_core_eq, emb_WS hb]
  exact WN_norm_le hN hb (inSector_emb v)

/-- The bounded realisation of `W_N(h)` on `ℓ²(𝓜_N)`: the density extension of the algebraic
Wick operator on the finite-occupation core (defined for every `h`; boundedness needs `h`
balanced and `N > 0`, see `WHil_core`, `WHil_norm_le`). -/
def WHil (N : ℕ) (h : Sym) : H N →L[ℂ] H N :=
  ((core N).comp (WS N h)).extendOfNorm (core N)

theorem WHil_core {N : ℕ} (hN : 0 < N) {h : Sym} (hb : Balanced h) (v : Sector N) :
    WHil N h (core N v) = core N (WS N h v) :=
  LinearMap.extendOfNorm_eq (core_dense N) ⟨coeffNorm h, fun x => core_WS_bound hN hb x⟩ v

theorem WHil_norm_le {N : ℕ} (hN : 0 < N) {h : Sym} (hb : Balanced h) :
    ‖WHil N h‖ ≤ coeffNorm h :=
  LinearMap.opNorm_extendOfNorm_le (core_dense N)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (fun x => core_WS_bound hN hb x)

/-- A bounded operator is bounded by `c` as soon as it is on the dense finite core. -/
lemma opNorm_le_of_core {N : ℕ} (D : H N →L[ℂ] H N) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : Sector N, ‖D (core N v)‖ ≤ c * ‖core N v‖) : ‖D‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound D hc
  intro x
  exact (core_dense N).induction_on (p := fun x => ‖D x‖ ≤ c * ‖x‖) x
    (isClosed_le (by fun_prop) (by fun_prop)) h

/-- **`eq:full-product-bound` on `ℓ²(𝓜_N)`** (operator norm, ungauged, `N ≥ 1`, balanced `f,g`):
`‖W_N(f)W_N(g) − W_N(fg) − N⁻¹ W_N(S_1(f,g) + i{f,g}/2)‖ ≤ C(f,g) N⁻²`. -/
theorem hilbert_product_bound {N : ℕ} (hN : 0 < N) {f g : Sym} (hf : Balanced f) (hg : Balanced g)
    {S : Finset ℤ} (hS : labelsOf f ⊆ S) :
    ‖WHil N f * WHil N g - WHil N (f * g)
        - (N : ℂ)⁻¹ • WHil N (S1 S f g + (Complex.I / 2) • pb S f g)‖
      ≤ Cfg f g * ((N : ℝ)⁻¹) ^ 2 := by
  apply opNorm_le_of_core _ (mul_nonneg (Cfg_nonneg _ _) (by positivity))
  intro v
  have hfg := hf.mul hg
  have hq : Balanced (S1 S f g + (Complex.I / 2) • pb S f g) :=
    balanced_add (balanced_S1 S hf hg) (balanced_smul _ (balanced_pb S hf hg))
  have e : (WHil N f * WHil N g - WHil N (f * g)
        - (N : ℂ)⁻¹ • WHil N (S1 S f g + (Complex.I / 2) • pb S f g)) (core N v)
      = core N (WS N f (WS N g v) - WS N (f * g) v
        - (N : ℂ)⁻¹ • WS N (S1 S f g + (Complex.I / 2) • pb S f g) v) := by
    simp only [sub_apply, mul_apply_eq_comp,
      smul_apply, WHil_core hN hf, WHil_core hN hg, WHil_core hN hfg,
      WHil_core hN hq, map_sub, map_smul]
  rw [e, norm_core_eq, norm_core_eq]
  have h2 : emb N (WS N f (WS N g v) - WS N (f * g) v
        - (N : ℂ)⁻¹ • WS N (S1 S f g + (Complex.I / 2) • pb S f g) v)
      = (WN N f * WN N g) (emb N v) - WN N (f * g) (emb N v)
        - (N : ℂ)⁻¹ • WN N (S1 S f g + (Complex.I / 2) • pb S f g) (emb N v) := by
    simp only [map_sub, map_smul, emb_WS hf, emb_WS hg, emb_WS hfg, emb_WS hq,
      Module.End.mul_apply]
  rw [h2]
  exact full_product_bound hN hf hg hS (inSector_emb v)

/-- **`eq:full-Dirac-bound` on `ℓ²(𝓜_N)`** (operator norm, ungauged, bracket convention
`{w_a, w̄_b} = −iδ_ab`): `‖−iN[W_N(f), W_N(g)] − W_N({f,g})‖ ≤ (C(f,g) + C(g,f)) N⁻¹`. -/
theorem hilbert_Dirac_bound {N : ℕ} (hN : 0 < N) {f g : Sym} (hf : Balanced f) (hg : Balanced g)
    {S : Finset ℤ} (hSf : labelsOf f ⊆ S) (hSg : labelsOf g ⊆ S) :
    ‖(-(Complex.I) * (N : ℂ)) • (WHil N f * WHil N g - WHil N g * WHil N f) - WHil N (pb S f g)‖
      ≤ (Cfg f g + Cfg g f) * (N : ℝ)⁻¹ := by
  apply opNorm_le_of_core _ (mul_nonneg (add_nonneg (Cfg_nonneg _ _) (Cfg_nonneg _ _)) (by positivity))
  intro v
  have hp := balanced_pb S hf hg
  have e : ((-(Complex.I) * (N : ℂ)) • (WHil N f * WHil N g - WHil N g * WHil N f)
        - WHil N (pb S f g)) (core N v)
      = core N ((-(Complex.I) * (N : ℂ)) • (WS N f (WS N g v) - WS N g (WS N f v))
        - WS N (pb S f g) v) := by
    simp only [sub_apply, mul_apply_eq_comp,
      smul_apply, WHil_core hN hf, WHil_core hN hg, WHil_core hN hp,
      map_sub, map_smul]
  rw [e, norm_core_eq, norm_core_eq]
  have h2 : emb N ((-(Complex.I) * (N : ℂ)) • (WS N f (WS N g v) - WS N g (WS N f v))
        - WS N (pb S f g) v)
      = (-(Complex.I) * (N : ℂ)) • ((WN N f * WN N g) (emb N v) - (WN N g * WN N f) (emb N v))
        - WN N (pb S f g) (emb N v) := by
    simp only [map_sub, map_smul, emb_WS hf, emb_WS hg, emb_WS hp, Module.End.mul_apply]
  rw [h2]
  exact full_Dirac_bound hN hf hg hSf hSg (inSector_emb v)

/-! ### Identification with the transfer operators `E_{N,ab}` -/

lemma balanced_zm_ab (a b : ℤ) : Balanced (zm (Finsupp.single a 1) (Finsupp.single b 1)) := by
  have := balanced_of_sum ({0} : Finset ℕ) (fun _ => (1 : ℂ)) (fun _ => Finsupp.single a 1)
    (fun _ => Finsupp.single b 1) (by intro i _ _; simp)
  simpa using this

/-- `W_N(z_a z̄_b) = N⁻¹ b_b^* b_a = E_{N,ab}` on the algebraic core (DEF-026). -/
theorem WN_zm_EOp (N : ℕ) (a b : ℤ) :
    WN N (zm (Finsupp.single a 1) (Finsupp.single b 1)) = EOp N a b := by
  rw [WN_zm]
  unfold WMono
  rw [Finsupp.degree_single, pow_one]
  rw [CreMono_single, AnnMono_single, pow_one, pow_one, ← Top_eq_Cre_Ann]
  rfl

theorem WS_zm_EN (N : ℕ) (a b : ℤ) (v : Sector N) :
    WS N (zm (Finsupp.single a 1) (Finsupp.single b 1)) v = EN N a b v := by
  apply emb_injective N
  rw [emb_WS (balanced_zm_ab a b), emb_EN, WN_zm_EOp]

/-- **`W_N(z_a z̄_b) = E_{N,ab}`** as bounded operators on `ℓ²(𝓜_N)`: the Hilbert Wick operator of
the Cartesian coordinate monomial is the bounded transfer operator of `OccupationHilbert`. -/
theorem WHil_zm_E {N : ℕ} (hN : 0 < N) (a b : ℤ) :
    WHil N (zm (Finsupp.single a 1) (Finsupp.single b 1)) = E N a b := by
  apply ext_core N
  intro v
  rw [WHil_core hN (balanced_zm_ab a b), WS_zm_EN, E_core]

/-! ### Gauged Wick operators and the ordered-word comparison -/

/-- Gauged Wick operator `W^q_N(h) = G_{q̄} W_N(h) G_q` for a supplied unit-modulus gauge
(as for `OccupationHilbert.Eq`; no Bethe gauge is selected). -/
def WHilq (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) (h : Sym) : H N →L[ℂ] H N :=
  gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) * WHil N h * gauge N q hq

lemma gauge_mul_conj (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) :
    gauge N q hq * gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) = 1 := by
  ext1 v
  apply lp.ext
  funext m
  simp only [mul_apply_eq_comp, gauge_apply, one_apply_eq_self]
  rw [← mul_assoc, unit_mul_conj hq m.1, one_mul]

lemma gauge_conj_mul (N : ℕ) (q : Occ → ℂ) (hq : UnitGauge q) :
    gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) * gauge N q hq = 1 := by
  ext1 v
  apply lp.ext
  funext m
  simp only [mul_apply_eq_comp, gauge_apply, one_apply_eq_self]
  rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (q m.1)) (q m.1), unit_mul_conj hq m.1, one_mul]

theorem WHilq_norm_le {N : ℕ} (hN : 0 < N) (q : Occ → ℂ) (hq : UnitGauge q) {h : Sym}
    (hb : Balanced h) : ‖WHilq N q hq h‖ ≤ coeffNorm h := by
  unfold WHilq
  calc ‖gauge N _ (unitGauge_conj hq) * WHil N h * gauge N q hq‖
      ≤ ‖gauge N _ (unitGauge_conj hq) * WHil N h‖ * ‖gauge N q hq‖ := norm_mul_le _ _
    _ ≤ (‖gauge N _ (unitGauge_conj hq)‖ * ‖WHil N h‖) * ‖gauge N q hq‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * coeffNorm h) * 1 := by
        apply mul_le_mul _ (gauge_norm_le _ _ _) (norm_nonneg _) (by
          exact mul_nonneg zero_le_one (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
        exact mul_le_mul (gauge_norm_le _ _ _) (WHil_norm_le hN hb) (norm_nonneg _) zero_le_one
    _ = coeffNorm h := by ring

/-- The gauged generator `W^q_N(z_a z̄_b)` is `OccupationHilbert.Eq` (eq:W, eq:E). -/
theorem WHilq_zm_Eq {N : ℕ} (hN : 0 < N) (q : Occ → ℂ) (hq : UnitGauge q) (a b : ℤ) :
    WHilq N q hq (zm (Finsupp.single a 1) (Finsupp.single b 1)) = OccupationHilbert.Eq N q hq a b := by
  unfold WHilq OccupationHilbert.Eq
  rw [WHil_zm_E hN]

/-- Gauged `eq:full-product-bound` (operator norm): conjugation by the unitary gauge. -/
theorem hilbert_product_bound_q {N : ℕ} (hN : 0 < N) (q : Occ → ℂ) (hq : UnitGauge q)
    {f g : Sym} (hf : Balanced f) (hg : Balanced g) {S : Finset ℤ} (hS : labelsOf f ⊆ S) :
    ‖WHilq N q hq f * WHilq N q hq g - WHilq N q hq (f * g)
        - (N : ℂ)⁻¹ • WHilq N q hq (S1 S f g + (Complex.I / 2) • pb S f g)‖
      ≤ Cfg f g * ((N : ℝ)⁻¹) ^ 2 := by
  have hD := hilbert_product_bound hN hf hg hS
  have e : WHilq N q hq f * WHilq N q hq g - WHilq N q hq (f * g)
        - (N : ℂ)⁻¹ • WHilq N q hq (S1 S f g + (Complex.I / 2) • pb S f g)
      = gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) *
        (WHil N f * WHil N g - WHil N (f * g)
          - (N : ℂ)⁻¹ • WHil N (S1 S f g + (Complex.I / 2) • pb S f g)) * gauge N q hq := by
    unfold WHilq
    have key : gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) * WHil N f * gauge N q hq
        * (gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) * WHil N g * gauge N q hq)
        = gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) * (WHil N f * WHil N g)
          * gauge N q hq := by
      calc _ = gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq) * WHil N f
            * (gauge N q hq * gauge N (fun m => (starRingEnd ℂ) (q m)) (unitGauge_conj hq))
            * WHil N g * gauge N q hq := by simp only [mul_assoc]
        _ = _ := by rw [gauge_mul_conj, mul_one]; simp only [mul_assoc]
    rw [key]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  rw [e]
  calc _ ≤ ‖gauge N _ (unitGauge_conj hq)‖ * ‖WHil N f * WHil N g - WHil N (f * g)
          - (N : ℂ)⁻¹ • WHil N (S1 S f g + (Complex.I / 2) • pb S f g)‖ * ‖gauge N q hq‖ := by
        refine (norm_mul_le _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ 1 * (Cfg f g * ((N : ℝ)⁻¹) ^ 2) * 1 :=
        mul_le_mul (mul_le_mul (gauge_norm_le _ _ _) hD (norm_nonneg _) zero_le_one)
          (gauge_norm_le _ _ _) (norm_nonneg _)
          (mul_nonneg zero_le_one (mul_nonneg (Cfg_nonneg _ _) (by positivity)))
    _ = _ := by ring

/-- The Cartesian generator `z_a z̄_b` as a symbol. -/
def gensym (a b : ℤ) : Sym := zm (Finsupp.single a 1) (Finsupp.single b 1)

/-- The ordered word `∏_j z_{a_j} z̄_{b_j}` (commutative product of generators). -/
def wordSym : List (ℤ × ℤ) → Sym
  | [] => 1
  | p :: w => gensym p.1 p.2 * wordSym w

lemma balanced_one : Balanced (1 : Sym) := by
  rw [← zm_zero_zero]
  have := balanced_of_sum ({0} : Finset ℕ) (fun _ => (1 : ℂ)) (fun _ => (0 : ℤ →₀ ℕ))
    (fun _ => (0 : ℤ →₀ ℕ)) (by intro i _ _; simp)
  simpa using this

theorem balanced_wordSym (w : List (ℤ × ℤ)) : Balanced (wordSym w) := by
  induction w with
  | nil => exact balanced_one
  | cons p w ih => exact (balanced_zm_ab p.1 p.2).mul ih

lemma labelsOf_gensym (a b : ℤ) : labelsOf (gensym a b) ⊆ {a} := by
  intro x hx
  unfold labelsOf gensym zm at hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨p, hp, hx⟩ := hx
  have hp' : p ∈ (AddMonoidAlgebra.single (Finsupp.single a 1, Finsupp.single b 1) (1 : ℂ)).coeff.support := hp
  rw [AddMonoidAlgebra.coeff_single, Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hp'
  subst hp'
  exact Finsupp.support_single_subset hx

/-- **Ordered-word comparison** (source: "any fixed ordered product of the `E^q_{N,ab}` differs from
its Wick monomial by `O(N⁻¹)` in operator norm", `wick_calculus.tex`, proof of `thm:full-wick`).
For every word there is a constant `C` such that for all `N ≥ 1`
`‖∏_j E^q_{N,a_j b_j} − W^q_N(∏_j z_{a_j} z̄_{b_j})‖ ≤ C/N`. -/
lemma WHil_one {N : ℕ} (hN : 0 < N) : WHil N (1 : Sym) = 1 := by
  apply ext_core N
  intro v
  rw [WHil_core hN balanced_one]
  have : WS N (1 : Sym) v = v := by
    apply emb_injective N
    rw [emb_WS balanced_one, WN_one]; rfl
  rw [this]; rfl

theorem word_comparison (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (w : List (ℤ × ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ‖(w.map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod
          - WHilq N (q N) (hq N) (wordSym w)‖ ≤ C * (N : ℝ)⁻¹ := by
  induction w with
  | nil =>
    refine ⟨0, le_refl _, fun N hN => ?_⟩
    have h1 : WHilq N (q N) (hq N) (wordSym []) = 1 := by
      show WHilq N (q N) (hq N) (1 : Sym) = 1
      unfold WHilq
      rw [WHil_one hN, mul_one, gauge_conj_mul]
    simp [h1]
  | cons p w ih =>
    obtain ⟨C, hC, hw⟩ := ih
    set f := gensym p.1 p.2 with hf
    set g := wordSym w with hg
    have hfb : Balanced f := balanced_zm_ab p.1 p.2
    have hgb : Balanced g := balanced_wordSym w
    have hS : labelsOf f ⊆ ({p.1} : Finset ℤ) := labelsOf_gensym p.1 p.2
    set q' : Sym := S1 {p.1} f g + (Complex.I / 2) • pb {p.1} f g with hq'
    have hq'b : Balanced q' :=
      balanced_add (balanced_S1 _ hfb hgb) (balanced_smul _ (balanced_pb _ hfb hgb))
    refine ⟨C + Cfg f g + coeffNorm q', add_nonneg (add_nonneg hC (Cfg_nonneg _ _))
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)), fun N hN => ?_⟩
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNp : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
    have hinv : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNr
    set W := WHilq N (q N) (hq N) with hW
    have hEp : OccupationHilbert.Eq N (q N) (hq N) p.1 p.2 = W f := (WHilq_zm_Eq hN _ _ _ _).symm
    have hprod : (((p :: w).map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod)
        = W f * ((w.map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod) := by
      simp [hEp]
    have hws : wordSym (p :: w) = f * g := rfl
    rw [hprod, hws]
    have hsplit : W f * ((w.map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod) - W (f * g)
        = W f * (((w.map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod) - W g)
          + ((W f * W g - W (f * g) - (N : ℂ)⁻¹ • W q') + (N : ℂ)⁻¹ • W q') := by
      rw [mul_sub]; abel
    rw [hsplit]
    have b1 : ‖W f * (((w.map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod) - W g)‖
        ≤ C * (N : ℝ)⁻¹ := by
      calc _ ≤ ‖W f‖ * ‖((w.map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod) - W g‖ :=
            norm_mul_le _ _
        _ ≤ 1 * (C * (N : ℝ)⁻¹) := by
            apply mul_le_mul _ (hw N hN) (norm_nonneg _) zero_le_one
            rw [← hEp]; exact Eq_norm_le N (q N) (hq N) p.1 p.2
        _ = _ := one_mul _
    have b2 : ‖W f * W g - W (f * g) - (N : ℂ)⁻¹ • W q'‖ ≤ Cfg f g * (N : ℝ)⁻¹ := by
      have := hilbert_product_bound_q hN (q N) (hq N) hfb hgb hS
      calc _ ≤ Cfg f g * ((N : ℝ)⁻¹) ^ 2 := this
        _ ≤ Cfg f g * (N : ℝ)⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ (Cfg_nonneg _ _)
            nlinarith
    have b3 : ‖(N : ℂ)⁻¹ • W q'‖ ≤ coeffNorm q' * (N : ℝ)⁻¹ := by
      rw [norm_smul]
      have : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by simp
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_right (WHilq_norm_le hN (q N) (hq N) hq'b) hNp.le
    calc _ ≤ ‖W f * (((w.map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod) - W g)‖
          + ‖(W f * W g - W (f * g) - (N : ℂ)⁻¹ • W q') + (N : ℂ)⁻¹ • W q'‖ := norm_add_le _ _
      _ ≤ C * (N : ℝ)⁻¹ + (‖W f * W g - W (f * g) - (N : ℂ)⁻¹ • W q'‖ + ‖(N : ℂ)⁻¹ • W q'‖) :=
          add_le_add b1 (norm_add_le _ _)
      _ ≤ C * (N : ℝ)⁻¹ + (Cfg f g * (N : ℝ)⁻¹ + coeffNorm q' * (N : ℝ)⁻¹) :=
          add_le_add_right (add_le_add b2 b3) _
      _ = (C + Cfg f g + coeffNorm q') * (N : ℝ)⁻¹ := by ring

/-! ### Closing the Wick comparison interface of `SpectralUpperBound` -/

open Filter in
/-- The gauged Wick realisation of an ordered Cartesian word, as a bounded operator sequence. -/
@[irreducible] def wickWordSequence (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (w : List (ℤ × ℤ)) :
    Gelfand.BoundedSequence OccupationHilbert.Fiber :=
  ⟨fun N => WHilq N (q N) (hq N) (wordSym w), by
    apply memℓp_infty
    refine ⟨max ‖WHilq 0 (q 0) (hq 0) (wordSym w)‖ (coeffNorm (wordSym w)), ?_⟩
    rintro _ ⟨N, rfl⟩
    by_cases hN : N = 0
    · subst hN; exact le_max_left _ _
    · exact (WHilq_norm_le (Nat.pos_of_ne_zero hN) (q N) (hq N) (balanced_wordSym w)).trans
        (le_max_right _ _)⟩

open Filter in
lemma wickWordSequence_apply (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (w : List (ℤ × ℤ))
    (N : ℕ) : wickWordSequence q hq w N = WHilq N (q N) (hq N) (wordSym w) := by
  unfold wickWordSequence; rfl

open Filter in
lemma limsup_assembly (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    (w : List (I × I)) (x : Gelfand.BoundedSequence OccupationHilbert.Fiber) (C : ℝ)
    (hcomp : ∀ᶠ N in atTop,
      ‖x N - (SpectralUpperBound.polynomialSequence q hq I ({0} : Finset ℕ) (fun _ => (1 : ℂ))
            (fun _ => w)) N‖ ≤ (N : ℝ)⁻¹ * C) :
    limsup (fun N => ‖x N‖) atTop
      ≤ SpectralUpperBound.unitBallSup I (SpectralUpperBound.wordSymbol I w) := by
  have := SpectralUpperBound.limsup_le_sup_of_inv_nat_comparison q hq I x ({0} : Finset ℕ)
    (fun _ => (1 : ℂ)) (fun _ => w) C hcomp
  have hsym : SpectralUpperBound.polynomialSymbol I ({0} : Finset ℕ) (fun _ => (1 : ℂ)) (fun _ => w)
      = SpectralUpperBound.wordSymbol I w := by
    funext z; simp [SpectralUpperBound.polynomialSymbol]
  rw [hsym] at this
  exact this

open Filter in
lemma comp_eventually (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    (w : List (I × I)) (X : ∀ N, OccupationHilbert.Fiber N) (C : ℝ)
    (hC : ∀ N : ℕ, 0 < N →
      ‖((w.map fun p => ((p.1 : ℤ), (p.2 : ℤ))).map
          fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2).prod - X N‖ ≤ C * (N : ℝ)⁻¹) :
    ∀ᶠ N in atTop,
      ‖X N - (SpectralUpperBound.polynomialSequence q hq I ({0} : Finset ℕ) (fun _ => (1 : ℂ))
            (fun _ => w)) N‖ ≤ (N : ℝ)⁻¹ * C := by
  rw [Filter.eventually_atTop]
  refine ⟨1, fun N hN => ?_⟩
  have h1 := hC N hN
  have hmap : ((w.map fun p => ((p.1 : ℤ), (p.2 : ℤ))).map
      fun p => OccupationHilbert.Eq N (q N) (hq N) p.1 p.2)
      = w.map fun p => OccupationHilbert.Eq N (q N) (hq N) p.1.1 p.2.1 := by
    rw [List.map_map]; rfl
  rw [hmap] at h1
  rw [SpectralUpperBound.polynomialSequence_apply, Finset.sum_singleton, one_smul, norm_sub_rev,
    mul_comm]
  exact h1

open Filter in
/-- **Upper bound for Wick monomials by the classical unit-ball supremum**: for an ordered word in
the generators `z_a z̄_b`, `a, b ∈ I`,
`limsup_N ‖W^q_N(z-word)‖ ≤ sup_{‖z‖≤1} |∏ z_a conj z_b|` (the upper half of `eq:full-norm-limit`
for monomials; the Wick comparison hypothesis of
`SpectralUpperBound.limsup_le_sup_of_inv_nat_comparison` is discharged by `word_comparison`). -/
theorem wick_word_limsup_le (q : ℕ → Occ → ℂ) (hq : ∀ N, UnitGauge (q N)) (I : Finset ℤ)
    (w : List (I × I)) :
    limsup (fun N => ‖wickWordSequence q hq (w.map fun p => ((p.1 : ℤ), (p.2 : ℤ))) N‖) atTop
      ≤ SpectralUpperBound.unitBallSup I (SpectralUpperBound.wordSymbol I w) := by
  obtain ⟨C, _, hC⟩ := word_comparison q hq (w.map fun p => ((p.1 : ℤ), (p.2 : ℤ)))
  refine limsup_assembly q hq I w _ C (comp_eventually q hq I w _ C ?_)
  intro N hN
  rw [wickWordSequence_apply]
  exact hC N hN

/-! Axiom audit (printed at compile time). -/
#print axioms remainder_eq
#print axioms remainder_nrm_le
#print axioms full_product_bound
#print axioms full_Dirac_bound
#print axioms balanced_pb
#print axioms WMono_inSector
#print axioms WN_inSector
#print axioms emb_WS
#print axioms norm_core_eq
#print axioms WHil_core
#print axioms WHil_norm_le
#print axioms opNorm_le_of_core
#print axioms hilbert_product_bound
#print axioms hilbert_Dirac_bound
#print axioms WN_zm_EOp
#print axioms WHil_zm_E
#print axioms gauge_mul_conj
#print axioms hilbert_product_bound_q
#print axioms word_comparison
#print axioms WHil_one
#print axioms WHilq_zm_Eq
#print axioms WHilq_norm_le
#print axioms wick_word_limsup_le

end

end QuantumNLS.WickBounds
