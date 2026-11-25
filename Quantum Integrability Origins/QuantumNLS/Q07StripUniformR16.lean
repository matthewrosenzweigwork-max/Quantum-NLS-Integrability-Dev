import QuantumNLS.Q07StripInteractionR16
import QuantumNLS.Q07SobolevCutsR16
import QuantumNLS.RootProductSymbolAnalytic

/-! Strip-uniform high-energy decay for the actual physical transfer on
compact L2 classes, hence on the printed Sobolev class. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer
  QuantumNLS.RootInteractionL1 QuantumNLS.RootDiscriminantBound
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance Q07StripUniformR16Pseudo : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance Q07StripUniformR16ENorm : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
namespace QuantumNLS.Q07StripUniformR16
open Q07RealCutsR15 (Profile integrable_profile integral_norm_profile integral_norm_sub_profile)
open Q07StripInteractionR16
variable {L κ : ℝ}

/-- Finite nets upgrade pointwise decay when a proved common Lipschitz
constant is available. -/
theorem uniform_of_lipschitz {X F : Type*} [PseudoMetricSpace X]
    [SeminormedAddCommGroup F] {K : Set X} (hK : IsCompact K)
    {f : ℝ → X → F} {b : F} {C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ t x, x ∈ K → ∀ y, y ∈ K → ‖f t x-f t y‖ ≤ C*dist x y)
    (hlim : ∀ x ∈ K, Tendsto (fun t => f t x) (cocompact ℝ) (𝓝 b))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∀ x ∈ K, ‖f t x-b‖ < ε := by
  classical
  let η := ε/(2*(C+1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨S, hSK, hS, hcover⟩ := hK.finite_cover_balls hη
  have hfin : ∀ x ∈ S, ∀ᶠ t in cocompact ℝ, ‖f t x-b‖ < ε/2 := by
    intro x hx
    simpa only [mem_ball, dist_eq_norm] using
      (hlim x (hSK hx)).eventually (ball_mem_nhds b (half_pos hε))
  filter_upwards [hS.eventually_all.2 hfin] with t ht x hx
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hd : dist x v < η := hxv
  have hs : C*dist x v < ε/2 := by
    have h1 := mul_le_mul_of_nonneg_left hd.le hC
    have h2 : C*η < ε/2 := by
      dsimp [η]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2*(C+1))]
      nlinarith
    exact h1.trans_lt h2
  have hn := norm_add_le (f t x-f t v) (f t v-b)
  rw [sub_add_sub_cancel] at hn
  exact hn.trans_lt (by linarith [hlip t x hx v (hSK hv), ht v hv])

/-- Imaginary translates are equicontinuous by the Cauchy derivative estimate
for the actual transfer, so the fixed-imaginary-part limit is uniform. -/
theorem uniform_imaginary (hL : 0 ≤ L) (u : Profile L) (h : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∀ y : ℝ, |y| ≤ h →
      ‖interaction κ u (spectral t y)-1‖ < ε := by
  have hh := uniform_of_lipschitz (K := Icc (-h) h) isCompact_Icc
    (f := fun t y => interaction κ u (spectral t y))
    (C := 2*Real.exp (control κ (h+1) u)) (by positivity)
    (fun t y hy y' hy' => by
      simpa only [Real.dist_eq] using spectral_sub_le hL u t (abs_le.mpr hy) (abs_le.mpr hy'))
    (fun y _ => interaction_tendsto hL u y) hε
  filter_upwards [hh] with t ht y hy
  exact ht y (abs_le.mp hy)

/-- Profile stability on the strip, derived from Volterra stability. -/
theorem profile_sub_le (hL : 0 ≤ L) {h B : ℝ} (u v : Profile L)
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) {z : ℂ} (hz : |z.im| ≤ h) :
    ‖interaction κ u z-interaction κ v z‖ ≤
      (Real.sqrt κ * Real.exp (h*L) *
        (Real.exp (Real.sqrt κ*Real.exp (h*L)*B) *
          Real.exp (Real.sqrt κ*Real.exp (h*L)*B))) * ‖u-v‖ := by
  have hb := norm_transfer_Bc_sub_le hL (integrable_profile hL u)
    (integrable_profile hL v) κ z (x := L) ⟨hL, le_rfl⟩
  simp only [integral_norm_profile hL, integral_norm_sub_profile hL] at hb
  refine hb.trans ?_
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz hL)
  calc
    _ ≤ (Real.sqrt κ * Real.exp (h*L) * ‖u-v‖) *
        (Real.exp (Real.sqrt κ * Real.exp (h*L) * B) *
          Real.exp (Real.sqrt κ * Real.exp (h*L) * B)) := by
      gcongr
    _ = _ := by ring

/-- Full strip interaction limit, uniform over compact interval-L1 classes. -/
theorem uniform_interaction (hL : 0 ≤ L) {K : Set (Profile L)} (hK : IsCompact K)
    (h : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∀ u ∈ K, ∀ y : ℝ, |y| ≤ h →
      ‖interaction κ u (spectral t y)-1‖ < ε := by
  classical
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (f := fun u : Profile L => u) continuousOn_id
  let C := Real.sqrt κ*Real.exp (h*L)*
    (Real.exp (Real.sqrt κ*Real.exp (h*L)*B)*Real.exp (Real.sqrt κ*Real.exp (h*L)*B))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let η := ε/(2*(C+1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨S, hSK, hS, hcover⟩ := hK.finite_cover_balls hη
  have hfin : ∀ v ∈ S, ∀ᶠ t in cocompact ℝ, ∀ y, |y| ≤ h →
      ‖interaction κ v (spectral t y)-1‖ < ε/2 :=
    fun v _ => uniform_imaginary hL v h (half_pos hε)
  filter_upwards [hS.eventually_all.2 hfin] with t ht u hu y hy
  obtain ⟨v, hv, huv⟩ := Set.mem_iUnion₂.mp (hcover hu)
  have hs := profile_sub_le (κ := κ) hL u v (hB u hu) (hB v (hSK hv))
    (z := spectral t y) (by simpa using hy)
  have hd : ‖u-v‖ < η := by simpa only [mem_ball, dist_eq_norm] using huv
  have hsmall : C*‖u-v‖ < ε/2 := by
    have h1 := mul_le_mul_of_nonneg_left hd.le hC
    have h2 : C*η < ε/2 := by
      dsimp [η]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2*(C+1))]
      nlinarith
    exact h1.trans_lt h2
  have hn := norm_add_le (interaction κ u (spectral t y)-interaction κ v (spectral t y))
    (interaction κ v (spectral t y)-1)
  rw [sub_add_sub_cancel] at hn
  exact hn.trans_lt (by linarith [ht v hv y hy])


/-- Balanced trace written in the interaction picture. -/
theorem trace_interaction (hL : 0 < L) (u : Profile L) (z : ℂ) :
    E1c z L * RootDiscriminantL1.discL1 L κ (fun x => u x) z =
      interaction κ u z 0 0 + (E1c z L * E1c z L) * interaction κ u z 1 1 := by
  have hc := Nc_eq_transfer hL (integrable_profile hL.le u) κ z (x := L) ⟨hL.le, le_rfl⟩
  have h00 : interaction κ u z 0 0 = E1c z L * RootDiscriminantL1.TT κ (fun x => u x) z L 0 0 := by
    rw [interaction, ← hc]
    simp [Dc, P1, P2, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : interaction κ u z 1 1 = E2c z L * RootDiscriminantL1.TT κ (fun x => u x) z L 1 1 := by
    rw [interaction, ← hc]
    simp [Dc, P1, P2, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h00, h11]
  unfold RootDiscriminantL1.discL1
  rw [Matrix.trace_fin_two]
  have he := E1c_mul_E2c z L
  calc
    _ = E1c z L * RootDiscriminantL1.TT κ (fun x => u x) z L 0 0 +
        E1c z L * RootDiscriminantL1.TT κ (fun x => u x) z L 1 1 := by ring
    _ = _ := by rw [mul_assoc (E1c z L), ← mul_assoc (E1c z L) (E2c z L), he, one_mul]

theorem E1_sq (z : ℂ) : E1c z L * E1c z L = Complex.exp (Complex.I*z*L) := by
  rw [E1c, ← Complex.exp_add]
  congr 1
  unfold a1c
  ring

/-- The physical representative binding at every complex spectral point. -/
theorem physical_discriminant_eq [Fact (0 < L)] (u : PhysicalTensor.L2T L) (z : ℂ) :
    RootDiscriminantL1.discL1 L κ (fun x => Q07PhysicalProfilesR15.toProfile u x) z =
      L2SpatialTransfer.discriminant κ u z := by
  have hae : (fun x : ℝ => Q07PhysicalProfilesR15.toProfile u x) =ᵐ[volume.restrict (Icc 0 L)]
      L2SpatialTransfer.profile u := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact Q07PhysicalProfilesR15.toProfile_ae u
  have hA : balCoef κ (fun x => Q07PhysicalProfilesR15.toProfile u x) z =ᵐ[volume.restrict (Icc 0 L)]
      balCoef κ (L2SpatialTransfer.profile u) z := by
    filter_upwards [hae] with x hx
    simp only [balCoef, coef, hx]
  have hT := transfer_eq_of_ae (Fact.out : 0 < L).le hA (x := L) ⟨(Fact.out : 0 < L).le, le_rfl⟩
  unfold RootDiscriminantL1.discL1 RootDiscriminantL1.TT
  rw [hT]
  rfl

theorem physical_symbol_interaction [Fact (0 < L)] (hκ : 0 ≤ κ)
    (u : PhysicalTensor.L2T L) (z : ℂ) :
    NormalizedTransfer.productSymbol L κ u z =
      interaction κ (Q07PhysicalProfilesR15.toProfile u) z 0 0 +
        Complex.exp (Complex.I*z*L) * interaction κ (Q07PhysicalProfilesR15.toProfile u) z 1 1 := by
  rw [RootProductSymbolAnalytic.productSymbol_eq_exp_mul_discriminant L κ hκ,
    ← physical_discriminant_eq u z]
  have he : Complex.exp (Complex.I*z*L/2) = E1c z L := by
    unfold E1c a1c
    congr 1
    ring
  rw [he, trace_interaction (Fact.out : 0 < L), E1_sq]

/-- The interaction error controls the physical symbol error uniformly in the
real part of the spectral parameter. -/
theorem symbol_error_le [Fact (0 < L)] (hκ : 0 ≤ κ) (u : PhysicalTensor.L2T L)
    {z : ℂ} {h : ℝ} (hz : |z.im| ≤ h) :
    ‖NormalizedTransfer.productSymbol L κ u z-1-Complex.exp (Complex.I*z*L)‖ ≤
      (1+Real.exp (h*L)) * ‖interaction κ (Q07PhysicalProfilesR15.toProfile u) z-1‖ := by
  let N := interaction κ (Q07PhysicalProfilesR15.toProfile u) z
  have h00 : ‖N 0 0-1‖ ≤ ‖N-1‖ := by
    have hh := row_sum_le_norm (N-1) 0
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), sub_zero] at hh
    linarith [norm_nonneg (N 0 1)]
  have h11 : ‖N 1 1-1‖ ≤ ‖N-1‖ := by
    have hh := row_sum_le_norm (N-1) 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hh
    linarith [norm_nonneg (N 1 0)]
  have he : ‖Complex.exp (Complex.I*z*L)‖ ≤ Real.exp (h*L) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hh : -z.im ≤ h := (neg_le_abs _).trans hz
    have hL : 0 ≤ L := (Fact.out : 0 < L).le
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_sub, mul_zero, sub_zero]
    nlinarith
  rw [physical_symbol_interaction hκ]
  change ‖N 0 0 + Complex.exp (Complex.I*z*L)*N 1 1-1-Complex.exp (Complex.I*z*L)‖ ≤ _
  rw [show N 0 0 + Complex.exp (Complex.I*z*L)*N 1 1-1-Complex.exp (Complex.I*z*L) =
    (N 0 0-1)+Complex.exp (Complex.I*z*L)*(N 1 1-1) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hh := mul_le_mul he h11 (norm_nonneg _) (Real.exp_pos _).le
  nlinarith

/-- The printed strip limit on any compact physical L2 class. -/
theorem uniform_physical_strip [Fact (0 < L)] (hκ : 0 ≤ κ)
    {K : Set (PhysicalTensor.L2T L)} (hK : IsCompact K) (h : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∀ u ∈ K, ∀ y : ℝ, |y| ≤ h →
      ‖NormalizedTransfer.productSymbol L κ u (spectral t y)-1-
        Complex.exp (Complex.I*spectral t y*L)‖ < ε := by
  let C := 1+Real.exp (h*L)
  have hC : 0 < C := by dsimp [C]; positivity
  have hh := uniform_interaction (κ := κ) (Fact.out : 0 < L).le
    (hK.image Q07PhysicalProfilesR15.toProfile.continuous) h (div_pos hε hC)
  filter_upwards [hh] with t ht u hu y hy
  have hi := ht (Q07PhysicalProfilesR15.toProfile u) (mem_image_of_mem _ hu) y hy
  exact (symbol_error_le hκ u (z := spectral t y) (by simpa using hy)).trans_lt
    ((mul_lt_mul_of_pos_left hi hC).trans_eq (mul_div_cancel₀ ε hC.ne'))

/-- Uniform horizontal-strip high-energy decay for every bounded DEF-002
Sobolev class with s>0, in particular the printed integer s≥1 class. -/
theorem uniform_sobolev_strip [Fact (0 < L)] (hκ : 0 ≤ κ) {s : ℝ} (hs : 0 < s)
    (B h : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∀ u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B,
      ∀ y : ℝ, |y| ≤ h → ‖NormalizedTransfer.productSymbol L κ u (spectral t y)-1-
        Complex.exp (Complex.I*spectral t y*L)‖ < ε := by
  filter_upwards [uniform_physical_strip hκ (Q07SobolevCutsR16.compact_closure (L := L) hs B) h hε]
    with t ht u hu
  exact ht u (subset_closure hu)

end QuantumNLS.Q07StripUniformR16
