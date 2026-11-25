import Mathlib

/- G2-037 P4 SUPPORT M2 (proof development, AUTHOR; not self-reviewed; SUPPORTING, not the head).
   Polygonal connectedness of the complement of a set K ⊆ ℂ that lies on the real line and is
   bounded. Applied to K = finiteGapCuts u S (union of real gap segments), the complement is
   polygonally connected: any two points of Kᶜ are joined by a finite chain of segments each
   contained in Kᶜ. No hypothesis beyond realness and boundedness of K. -/
set_option autoImplicit false

open Set Relation Metric

namespace NlsGge.G2037P4M2
noncomputable section

/-- A segment whose endpoints lie on the real line stays on the real line. -/
theorem segment_im_zero_M2 {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0) :
    ∀ z ∈ segment ℝ a b, z.im = 0 := by
  rintro z ⟨α, β, hα, hβ, hab, rfl⟩
  simp [ha, hb]

/-- Segment with constant nonzero imaginary part avoids any subset of the real line. -/
theorem segment_const_im_compl_M2 {K : Set ℂ} (hK : ∀ z ∈ K, z.im = 0) {p q : ℂ}
    (hpq : p.im = q.im) (hne : p.im ≠ 0) : segment ℝ p q ⊆ Kᶜ := by
  intro z hz hzK
  obtain ⟨α, β, hα, hβ, hab, rfl⟩ := hz
  have h0 := hK _ hzK
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at h0
  rw [← hpq] at h0
  have e : (α + β) * p.im = 0 := by rw [add_mul]; linarith
  rw [hab, one_mul] at e
  exact hne e

/-- Upward segment from a point off K (with nonnegative imaginary part) to `I`. -/
theorem segment_up_compl_M2 {K : Set ℂ} (hK : ∀ z ∈ K, z.im = 0) {p : ℂ} (hp : p ∉ K)
    (him : 0 ≤ p.im) : segment ℝ p Complex.I ⊆ Kᶜ := by
  intro z hz hzK
  obtain ⟨α, β, hα, hβ, hab, rfl⟩ := hz
  have h0 := hK _ hzK
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.I_im] at h0
  have hβ0 : β = 0 := by nlinarith [mul_nonneg hα him]
  have hα1 : α = 1 := by linarith
  apply hp
  simpa [hα1, hβ0] using hzK

/-- Downward segment from a point off K (with nonpositive imaginary part) to `-I`. -/
theorem segment_down_compl_M2 {K : Set ℂ} (hK : ∀ z ∈ K, z.im = 0) {p : ℂ} (hp : p ∉ K)
    (him : p.im ≤ 0) : segment ℝ p (-Complex.I) ⊆ Kᶜ := by
  intro z hz hzK
  obtain ⟨α, β, hα, hβ, hab, rfl⟩ := hz
  have h0 := hK _ hzK
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.neg_im, Complex.I_im] at h0
  have hβ0 : β = 0 := by nlinarith [mul_nonneg hα (neg_nonneg.mpr him)]
  have hα1 : α = 1 := by linarith
  apply hp
  simpa [hα1, hβ0] using hzK

/-- Vertical segment through a real point `x` off K. -/
theorem segment_vert_compl_M2 {K : Set ℂ} (hK : ∀ z ∈ K, z.im = 0) {x : ℝ}
    (hx : (x : ℂ) ∉ K) :
    segment ℝ ((x : ℂ) + Complex.I) ((x : ℂ) - Complex.I) ⊆ Kᶜ := by
  intro z hz hzK
  obtain ⟨α, β, hα, hβ, hab, rfl⟩ := hz
  have h0 := hK _ hzK
  simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, smul_eq_mul, Complex.I_im,
    Complex.ofReal_im] at h0
  have hz' : α • ((x : ℂ) + Complex.I) + β • ((x : ℂ) - Complex.I) = (x : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul, Complex.ofReal_re,
        Complex.I_re]
      linear_combination x * hab
    · simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, smul_eq_mul, Complex.ofReal_im,
        Complex.I_im]
      linarith
  rw [hz'] at hzK
  exact hx hzK

/-- Any bounded set has a real point outside it. -/
theorem exists_real_notMem_M2 (K : Set ℂ) (hbdd : Bornology.IsBounded K) :
    ∃ x : ℝ, (x : ℂ) ∉ K := by
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
  refine ⟨max R 0 + 1, fun h => ?_⟩
  have h1 := hR h
  rw [mem_closedBall, dist_zero_right, Complex.norm_real,
    Real.norm_of_nonneg (by linarith [le_max_right R 0])] at h1
  linarith [le_max_left R 0]

/-- Reversal of a chain along a symmetric relation. -/
theorem reflTrans_symm_M2 {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a)
    {a b : α} (h : ReflTransGen r a b) : ReflTransGen r b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact (ReflTransGen.single (hr _ _ hbc)).trans ih

/-- Polygonal connectedness of the complement of a bounded real subset of `ℂ`:
any two points off `K` are joined by a finite chain of segments inside `Kᶜ`. -/
theorem polygonal_connected_compl_M2 (K : Set ℂ) (hK : ∀ z ∈ K, z.im = 0)
    (hbdd : Bornology.IsBounded K) (z w : ℂ) (hz : z ∉ K) (hw : w ∉ K) :
    ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) z w := by
  have hsymm : ∀ a b : ℂ, (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) a b →
      (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) b a := by
    intro a b h
    simpa only [segment_symm] using h
  obtain ⟨x, hx⟩ := exists_real_notMem_M2 K hbdd
  -- I connects to -I through the real point x.
  have hIneg : ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) Complex.I (-Complex.I) := by
    have s1 : (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) Complex.I ((x : ℂ) + Complex.I) :=
      segment_const_im_compl_M2 hK (by simp) (by simp)
    have s2 : (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) ((x : ℂ) + Complex.I) ((x : ℂ) - Complex.I) :=
      segment_vert_compl_M2 hK hx
    have s3 : (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) ((x : ℂ) - Complex.I) (-Complex.I) :=
      segment_const_im_compl_M2 hK (by simp) (by simp)
    exact ReflTransGen.tail (ReflTransGen.tail (ReflTransGen.single s1) s2) s3
  have toI : ∀ p : ℂ, p ∉ K →
      ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) p Complex.I := by
    intro p hp
    rcases le_total 0 p.im with him | him
    · have u1 : (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) p Complex.I :=
        segment_up_compl_M2 hK hp him
      exact ReflTransGen.single u1
    · have d1 : (fun a b : ℂ => segment ℝ a b ⊆ Kᶜ) p (-Complex.I) :=
        segment_down_compl_M2 hK hp him
      exact ReflTransGen.trans (ReflTransGen.single d1) (reflTrans_symm_M2 hsymm hIneg)
  exact (toI z hz).trans (reflTrans_symm_M2 hsymm (toI w hw))

/-- Bounded union of finitely many segments (used for the finite gap cut set). -/
theorem cuts_bounded_M2 (a b : ℤ → ℂ) (S : Finset ℤ) :
    Bornology.IsBounded (⋃ n ∈ (S : Set ℤ), segment ℝ (a n) (b n)) := by
  rw [Bornology.isBounded_biUnion (S.finite_toSet)]
  intro n _
  have hfin : ({a n, b n} : Set ℂ).Finite := Set.toFinite _
  rw [← convexHull_pair]
  exact (hfin.isCompact_convexHull ℝ).isBounded

end

end NlsGge.G2037P4M2
