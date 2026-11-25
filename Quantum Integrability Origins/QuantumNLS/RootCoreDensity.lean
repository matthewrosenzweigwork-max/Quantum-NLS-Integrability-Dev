import Mathlib
import QuantumNLS.RootGapLevelSets
import QuantumNLS.BulkResponseForm
import QuantumNLS.RootSpectralDensityFinal

/-!
# R-1602B09D `CC:F03:core` (`F03.tex:26`), last sentence: the density hypotheses hold for the quantum limiting measure

"The quantum limiting measure of every unit `H¹` input has these properties."  We prove `BulkResponseForm.CoreDensity (measure hκ u)` (the literal predicate of the
repository for the hypotheses of the lemma) for every `κ > 0` and every nonzero `u` with a continuous `L`-periodic representative `uf` (every `H¹` input has one):

* `ρ = dens κ u` is continuous, nonnegative, bounded by `‖uf‖_{L¹}/(π√κ)`, and `measure hκ u = ρ dx` (R-7E0532E7, `RootDensityIdentification`);
* `{ρ > 0} = {|Re Δ| > 2}` is the disjoint union of its connected components, bounded open intervals `(a_i,b_i)` with `|Δ(a_i)| = |Δ(b_i)| = 2` (R-7E0532E7);
  the endpoint set is locally finite;
* `ρ = (πκ)⁻¹ arcosh(|Re Δ|/2)` is smooth on every component (`Δ` is entire and real on `ℝ`, `arcosh` smooth on `(1,∞)`);
* at every endpoint (indeed at every real zero of `Δ² - 4`) one side carries `ρ = 0` near the point (R-0908DFDE, `RootGapLevelSets`/`RootGapLocal`: a simple zero has a gap on one side
  and a band on the other, a double zero has bands on both), and `ρ(x) ≤ C |x - e|^{1/2}` (Lipschitz bound `|Re Δ(x)| - 2 ≤ M|x - e|` and `arcosh(1+s) ≤ 3√s`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped Real ENNReal ContDiff

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootCoreDensity

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.RootGapMultiplicity (Dl hD hreal sgn_cases zero_data ray_of_boundary order_cases')
open QuantumNLS.RootGapLevelSets (dens_pos_iff continuous_re_Delta)
open QuantumNLS.RootGapLocal (simple_sides double_strict)
open QuantumNLS.RootDensityIdentification (dens continuous_dens dens_nonneg disc_eq_rep root_density root_density_structure)
open QuantumNLS.RootDiscriminant (discReal)
open QuantumNLS.BulkResponseActual (IsPeriodicRepresentative)
open QuantumNLS.BulkResponseForm (CoreDensity)

variable {L κ : ℝ} [Fact (0 < L)]

theorem arcosh_le_sqrt {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : Real.arcosh (1 + s) ≤ 3 * Real.sqrt s := by
  unfold Real.arcosh
  have hpos : 0 < (1 + s) + √((1 + s) ^ 2 - 1) := by positivity
  have h2 := Real.log_le_sub_one_of_pos hpos
  have hsq : √((1 + s) ^ 2 - 1) ≤ 2 * √s := by
    have h4 : (1 + s) ^ 2 - 1 ≤ (2 * √s) ^ 2 := by
      have : (2 * √s) ^ 2 = 4 * s := by rw [mul_pow, Real.sq_sqrt h0]; ring
      rw [this]; nlinarith
    calc √((1 + s) ^ 2 - 1) ≤ √((2 * √s) ^ 2) := Real.sqrt_le_sqrt h4
      _ = 2 * √s := Real.sqrt_sq (by positivity)
  have hs : s ≤ √s := by
    calc s = √(s ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ √s := Real.sqrt_le_sqrt (by nlinarith)
  linarith

theorem contDiff_re_Delta (κ : ℝ) (u : L2T L) : ContDiff ℝ ∞ (fun x : ℝ => (Dl κ u (x : ℂ)).re) := by
  have h1 : ContDiff ℂ ∞ (Dl κ u) := (hD κ u).contDiff
  have h2 : ContDiff ℝ ∞ (Dl κ u) := h1.restrict_scalars ℝ
  exact Complex.reCLM.contDiff.comp (h2.comp Complex.ofRealCLM.contDiff)

theorem contDiffAt_dens (hκ : 0 < κ) (u : L2T L) {x : ℝ} (hx : 2 < |(Dl κ u (x : ℂ)).re|) :
    ContDiffAt ℝ ∞ (dens κ u) x := by
  have hf := (contDiff_re_Delta κ u).contDiffAt (x := x)
  have hne : (Dl κ u (x : ℂ)).re ≠ 0 := by
    intro h0; rw [h0] at hx; simp at hx; linarith
  have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => |(Dl κ u (y : ℂ)).re|) x := hf.abs hne
  have hmem : |(Dl κ u (x : ℂ)).re| / 2 ∈ Ioi (1 : ℝ) := by
    show 1 < |(Dl κ u (x : ℂ)).re| / 2
    linarith
  have h2 : ContDiffAt ℝ ∞ (fun y : ℝ => Real.arcosh (|(Dl κ u (y : ℂ)).re| / 2)) x :=
    ContDiffAt.comp (f := fun y : ℝ => |(Dl κ u (y : ℂ)).re| / 2) (g := Real.arcosh) x
      (Real.contDiffAt_arcosh hmem) (h1.div_const 2)
  have h3 : dens κ u =ᶠ[𝓝 x] fun y => (Real.pi * κ)⁻¹ * Real.arcosh (|(Dl κ u (y : ℂ)).re| / 2) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_re_Delta κ u).abs).mem_nhds hx] with y hy
    unfold dens QuantumNLS.RootDensity.hfun
    rw [if_pos hy]
  exact (contDiffAt_const.mul h2).congr_of_eventuallyEq h3

theorem band_zero' (hκ : 0 < κ) (u : L2T L) {x : ℝ} (hx : |(Dl κ u (x : ℂ)).re| ≤ 2) : dens κ u x = 0 :=
  le_antisymm (not_lt.1 (fun h => by have := (dens_pos_iff hκ u x).1 h; linarith)) (dens_nonneg hκ u x)

theorem band_zero (hκ : 0 < κ) (u : L2T L) {x : ℝ} (hx : |(Dl κ u (x : ℂ)).re| < 2) : dens κ u x = 0 :=
  le_antisymm (not_lt.1 (fun h => by have := (dens_pos_iff hκ u x).1 h; linarith)) (dens_nonneg hκ u x)

theorem sq_zero_of_abs (u : L2T L) {e : ℝ} (he : |(Dl κ u (e : ℂ)).re| = 2) :
    Dl κ u (e : ℂ) ^ 2 - 4 = 0 := by
  have hr : Dl κ u (e : ℂ) = ((Dl κ u (e : ℂ)).re : ℂ) :=
    Complex.ext (by simp) (by simp [hreal κ u e])
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 2)).1 he with h | h
  · rw [hr, h]; norm_num
  · rw [hr, h]; norm_num

theorem one_side (hκ : 0 < κ) (u : L2T L) {e : ℝ} (hz : Dl κ u (e : ℂ) ^ 2 - 4 = 0) :
    (∀ᶠ x : ℝ in 𝓝[<] e, dens κ u x = 0) ∨ (∀ᶠ x : ℝ in 𝓝[>] e, dens κ u x = 0) := by
  obtain ⟨n, hn⟩ := zero_data hκ u e hz
  obtain ⟨hDx, hray⟩ := ray_of_boundary hκ u e n hn
  rcases order_cases' hκ u e n hn with h1 | h2
  · rcases simple_sides (hD κ u) (hreal κ u) (sgn_cases n) hDx h1 with ⟨-, hb⟩ | ⟨-, hb⟩
    · left; exact hb.mono fun x hx => band_zero hκ u hx
    · right; exact hb.mono fun x hx => band_zero hκ u hx
  · have hd := double_strict (hD κ u) (hreal κ u) (sgn_cases n) Fact.out hray hDx h2
    left
    exact (hd.filter_mono (nhdsWithin_mono _ (fun t ht => ne_of_lt ht))).mono fun x hx => band_zero hκ u hx

theorem sqrt_bound (hκ : 0 < κ) (u : L2T L) {e : ℝ} (he : |(Dl κ u (e : ℂ)).re| = 2) :
    ∃ U ∈ 𝓝 e, ∃ C : ℝ, ∀ x ∈ U, dens κ u x ≤ C * |x - e| ^ (1 / 2 : ℝ) := by
  set f : ℝ → ℝ := fun x => (Dl κ u (x : ℂ)).re with hf
  have hfd : DifferentiableAt ℝ f e :=
    ((contDiff_re_Delta κ u).differentiable (by simp)).differentiableAt
  obtain ⟨M, hMpos, hM⟩ := (hfd.hasDerivAt.isBigO_sub).exists_pos
  have hev : ∀ᶠ x in 𝓝 e, ‖f x - f e‖ ≤ M * ‖x - e‖ := hM.bound
  have hsmall : ∀ᶠ x : ℝ in 𝓝 e, M * |x - e| / 2 < 1 := by
    have : Tendsto (fun x : ℝ => M * |x - e| / 2) (𝓝 e) (𝓝 (M * |e - e| / 2)) :=
      ((continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).div_const 2).tendsto e
    simp only [sub_self, abs_zero, mul_zero, zero_div] at this
    exact this.eventually (gt_mem_nhds one_pos)
  refine ⟨_, hev.and hsmall, (Real.pi * κ)⁻¹ * (3 * Real.sqrt (M / 2)), fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hpk : 0 ≤ (Real.pi * κ)⁻¹ := by positivity
  have hrpow : |x - e| ^ (1 / 2 : ℝ) = Real.sqrt |x - e| := (Real.sqrt_eq_rpow _).symm
  rw [hrpow]
  have hnn : 0 ≤ (Real.pi * κ)⁻¹ * (3 * Real.sqrt (M / 2)) * Real.sqrt |x - e| := by positivity
  by_cases hband : |f x| ≤ 2
  · have h0 : dens κ u x = 0 := band_zero' hκ u hband
    rw [h0]; exact hnn
  · push Not at hband
    have hfe : |f e| = 2 := he
    have hfx : |f x| ≤ 2 + M * |x - e| := by
      have h1 : |f x| ≤ |f e| + |f x - f e| := by
        have := abs_add_le (f e) (f x - f e)
        simpa using this
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hx1
      linarith
    set sv : ℝ := |f x| / 2 - 1 with hsv
    have hs0 : 0 ≤ sv := by rw [hsv]; linarith
    have hs1 : sv ≤ M * |x - e| / 2 := by rw [hsv]; linarith
    have hs2 : sv ≤ 1 := by linarith
    have hd : dens κ u x = (Real.pi * κ)⁻¹ * Real.arcosh (1 + sv) := by
      unfold dens QuantumNLS.RootDensity.hfun
      have : 2 < |(Dl κ u (x : ℂ)).re| := hband
      rw [if_pos this]
      congr 2; rw [hsv]; ring
    have hA := arcosh_le_sqrt hs0 hs2
    have hB : Real.sqrt sv ≤ Real.sqrt (M / 2) * Real.sqrt |x - e| := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [hd]
    calc (Real.pi * κ)⁻¹ * Real.arcosh (1 + sv) ≤ (Real.pi * κ)⁻¹ * (3 * Real.sqrt sv) :=
          mul_le_mul_of_nonneg_left hA hpk
      _ ≤ (Real.pi * κ)⁻¹ * (3 * (Real.sqrt (M / 2) * Real.sqrt |x - e|)) := by
          apply mul_le_mul_of_nonneg_left _ hpk
          linarith
      _ = _ := by ring

/-! ### The density hypotheses for the quantum limiting measure -/

theorem coreDensity_actual (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf) : CoreDensity (measure hκ u) := by
  have hL : 0 < L := Fact.out
  have hDre : ∀ x : ℝ, (Dl κ u (x : ℂ)).re = discReal L κ uf x := fun x =>
    congrArg Complex.re (disc_eq_rep hrep κ (x : ℂ))
  obtain ⟨-, hbound, -⟩ := root_density_structure hκ hu hrep
  have hstruct := QuantumNLS.RootSpectralDensityFinal.root_density_structure_final L κ hL hκ hrep.1
  have hcomp := hstruct.2.2.2.2.1
  have hfin := hstruct.2.2.2.2.2.1
  set P : Set ℝ := {t | 2 < |discReal L κ uf t|} with hP
  have hPdisc : ∀ t, t ∈ P ↔ 2 < |(Dl κ u (t : ℂ)).re| := fun t => by
    show 2 < |discReal L κ uf t| ↔ _
    rw [hDre]
  have hPopen : IsOpen P := by
    have : P = {x : ℝ | 2 < |(Dl κ u (x : ℂ)).re|} := by ext t; exact hPdisc t
    rw [this]
    exact isOpen_lt continuous_const (continuous_re_Delta κ u).abs
  -- components
  have key : ∀ i : {S : Set ℝ // ∃ x ∈ P, S = connectedComponentIn P x},
      ∃ a b : ℝ, a < b ∧ i.1 = Ioo a b ∧ |discReal L κ uf a| = 2 ∧ |discReal L κ uf b| = 2 := by
    rintro ⟨S, x, hx, rfl⟩
    obtain ⟨a, b, hax, hxb, hc, ha, hb⟩ := hcomp x hx
    exact ⟨a, b, hax.trans hxb, hc, ha, hb⟩
  choose a b hab hS ha hb using key
  have hcc : ∀ i, Ioo (a i) (b i) ⊆ P := by
    intro i y hy
    rw [← hS i] at hy
    obtain ⟨S, x, hx, hSx⟩ := i
    have : (S : Set ℝ) ⊆ P := by rw [hSx]; exact connectedComponentIn_subset _ _
    exact this hy
  refine ⟨dens κ u, continuous_dens κ u, dens_nonneg hκ u, ⟨_, hbound⟩,
    root_density hκ hu, ?_⟩
  refine ⟨{S : Set ℝ // ∃ x ∈ P, S = connectedComponentIn P x}, a, b, hab, ?_, ?_, ?_, ?_, ?_⟩
  · -- positive set
    ext x
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro hx
      have hxP : x ∈ P := (hPdisc x).2 ((dens_pos_iff hκ u x).1 hx)
      refine ⟨⟨connectedComponentIn P x, x, hxP, rfl⟩, ?_⟩
      rw [← hS]
      exact mem_connectedComponentIn hxP
    · rintro ⟨i, hxi⟩
      exact (dens_pos_iff hκ u x).2 ((hPdisc x).1 (hcc i hxi))
  · -- disjoint
    intro i j hij
    refine Set.disjoint_left.2 fun z hzi hzj => hij ?_
    have hzi' : z ∈ (i.1 : Set ℝ) := by rw [hS i]; exact hzi
    have hzj' : z ∈ (j.1 : Set ℝ) := by rw [hS j]; exact hzj
    obtain ⟨xi, hxi, hSi⟩ := i.2
    obtain ⟨xj, hxj, hSj⟩ := j.2
    apply Subtype.ext
    rw [hSi] at hzi' ⊢
    rw [hSj] at hzj' ⊢
    rw [connectedComponentIn_eq hzi', connectedComponentIn_eq hzj']
  · -- locally finite endpoints
    intro x
    refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
    refine (hfin (x - 1) (x + 1)).subset ?_
    rintro e ⟨heI, heE⟩
    refine ⟨heI, ?_⟩
    rcases heE with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ha i
    · exact hb i
  · -- smooth on each interval
    intro i
    intro x hx
    exact (contDiffAt_dens hκ u ((hPdisc x).1 (hcc i hx))).contDiffWithinAt
  · -- endpoints
    intro e he
    have hee : |(Dl κ u (e : ℂ)).re| = 2 := by
      rw [hDre]
      rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact ha i
      · exact hb i
    have hz := sq_zero_of_abs u hee
    obtain ⟨U2, hU2, C, hC⟩ := sqrt_bound hκ u hee
    rcases one_side hκ u hz with hl | hr
    · have hl' := (eventually_nhdsWithin_iff.1 hl)
      obtain ⟨U1, hU1, hU1'⟩ := eventually_iff_exists_mem.1 hl'
      refine ⟨U1 ∩ U2, inter_mem hU1 hU2, C, Or.inl fun x hx hxe => hU1' x hx.1 hxe, fun x hx => hC x hx.2⟩
    · have hr' := (eventually_nhdsWithin_iff.1 hr)
      obtain ⟨U1, hU1, hU1'⟩ := eventually_iff_exists_mem.1 hr'
      refine ⟨U1 ∩ U2, inter_mem hU1 hU2, C, Or.inr fun x hx hxe => hU1' x hx.1 hxe, fun x hx => hC x hx.2⟩

end QuantumNLS.RootCoreDensity

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RootCoreDensity.coreDensity_actual
