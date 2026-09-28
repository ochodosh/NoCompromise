import NoCompromise.BV.CoareaCritical
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Null images from uniformly flat Taylor remainders

A bounded subset of `ℝⁿ` on which a scalar map has uniformly `o(rⁿ)` oscillation
has image of one-dimensional Lebesgue measure zero. The proof covers the source
by a finite disjoint grid and its image by intervals of total length tending to
zero. No Sard theorem or coarea identity is used.
-/

noncomputable section
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Exact image-interval cost for an order-`n` flat remainder in a grid cell. -/
lemma flat_gridCell_image_cost {n : ℕ} {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (k : Fin n → ℤ) (a : ℝ) :
    volume (Icc (a - ε * ((n : ℝ) * δ) ^ n) (a + ε * ((n : ℝ) * δ) ^ n)) =
      ENNReal.ofReal (2 * (n : ℝ) ^ n * ε) * volume (gridCell δ k) := by
  rw [Real.volume_Icc, volume_gridCell,
    show (a + ε * ((n : ℝ) * δ) ^ n) - (a - ε * ((n : ℝ) * δ) ^ n) =
      (2 * (n : ℝ) ^ n * ε) * δ ^ n by rw [mul_pow]; ring,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hδ]

/-- Bounded uniform order-`n` flatness forces a scalar image to be Lebesgue-null. -/
lemma measure_image_eq_zero_of_bounded_uniform_flat {n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : Bornology.IsBounded S)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hflat : ∀ ε : ℝ, 0 < ε → ∃ ρ > 0, ∀ x ∈ S, ∀ y,
      dist y x < ρ → dist (f y) (f x) ≤ ε * dist y x ^ n) :
    volume (f '' S) = 0 := by
  classical
  obtain ⟨R, _, hSR⟩ := hS.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  have hSR' : S ⊆ closedBall 0 R := hSR.trans ball_subset_closedBall
  have hbound (ε : ℝ) (hε : 0 < ε) :
      volume (f '' S) ≤ ENNReal.ofReal (2 * (n : ℝ) ^ n * ε) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + n)) := by
    obtain ⟨ρ, hρ, hf⟩ := hflat ε hε
    obtain ⟨δ, hδ, hδlt⟩ := exists_between
      (lt_min (by norm_num : (0 : ℝ) < 1) (div_pos hρ (by positivity : (0 : ℝ) < n + 1)))
    have hδone : δ ≤ 1 := (lt_min_iff.mp hδlt).1.le
    have hδρ : (n : ℝ) * δ < ρ := by
      have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mp
        (lt_min_iff.mp hδlt).2
      nlinarith
    let J := {k : Fin n → ℤ // (S ∩ gridCell δ k).Nonempty}
    let : Fintype J := (finite_gridCells_meeting hδ hS).fintype
    choose a haS haC using fun j : J => j.property
    let I (j : J) := Icc (f (a j) - ε * ((n : ℝ) * δ) ^ n)
      (f (a j) + ε * ((n : ℝ) * δ) ^ n)
    have hcover : f '' S ⊆ ⋃ j, I j := by
      rintro _ ⟨x, hxS, rfl⟩
      let j : J := ⟨gridIndex δ x, x, hxS, mem_gridCell_gridIndex hδ x⟩
      have hd : dist x (a j) ≤ (n : ℝ) * δ := by
        simpa only [dist_eq_norm] using
          norm_sub_le_of_mem_gridCell (haC j) (mem_gridCell_gridIndex hδ x)
      have h := (hf (a j) (haS j) x (hd.trans_lt hδρ)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg hd n) hε.le)
      rw [Real.dist_eq] at h
      refine mem_iUnion.mpr ⟨j, ?_⟩
      exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
    calc
      volume (f '' S) ≤ volume (⋃ j, I j) := measure_mono hcover
      _ ≤ ∑ j, volume (I j) := by simpa only [tsum_fintype] using measure_iUnion_le I
      _ = ENNReal.ofReal (2 * (n : ℝ) ^ n * ε) * ∑ j : J, volume (gridCell δ j.val) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ =>
          flat_gridCell_image_cost hδ.le hε.le j.val (f (a j))
      _ ≤ _ := mul_le_mul' le_rfl (sum_volume_gridCell_le hδ hδone hSR'
        (fun j : J => j.val) Subtype.coe_injective (fun j => j.property))
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal
      (2 * (n : ℝ) ^ n * (1 / 2 : ℝ) ^ j) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + n))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h := ENNReal.tendsto_ofReal (hpow.const_mul (2 * (n : ℝ) ^ n))
    simpa only [mul_zero, ENNReal.ofReal_zero, zero_mul] using
      ENNReal.Tendsto.mul_const h (Or.inr (isCompact_closedBall _ _).measure_lt_top.ne)
  exact le_antisymm (ge_of_tendsto hlim
    (Eventually.of_forall fun j => hbound _ (pow_pos (by norm_num) j))) bot_le

/-- Uniformly small first-order slopes near a compact set where the derivative vanishes.
The codomain may itself be a space of continuous linear maps. -/
lemma compact_uniform_small_slope_of_fderiv_eq_zero
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U S : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContDiffOn ℝ 1 f U) (hzero : ∀ x ∈ S, fderiv ℝ f x = 0)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ S, ∀ y, dist y x < δ → dist (f y) (f x) ≤ ε * dist y x := by
  have hlocal (x : S) : ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ (x : EuclideanSpace ℝ (Fin n)) ∈ V ∧ LipschitzOnWith ε f V := by
    have hc := hf.contDiffAt (hU.mem_nhds (hSU x.property))
    obtain ⟨V, hV, hLip⟩ := hc.exists_lipschitzOnWith_of_nnnorm_lt ε
      (by simpa [hzero x x.property] using hε)
    exact ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV,
      hLip.mono interior_subset⟩
  choose V hVo hVx hLip using hlocal
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric hS hVo
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hxy
  obtain ⟨i, hi⟩ := hcover x hx
  exact (hLip i).dist_le_mul y (hi hxy) x (hi (mem_ball_self hδ))

/-- Compact sets where both first and second derivatives vanish have uniformly
arbitrarily small quadratic remainders. -/
lemma compact_uniform_quadratic_flat {n : ℕ}
    {U S : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ 2 f U) (hfirst : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hsecond : ∀ x ∈ S, fderiv ℝ (fderiv ℝ f) x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ > 0, ∀ x ∈ S, ∀ y, dist y x < ρ → dist (f y) (f x) ≤ ε * dist y x ^ 2 := by
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf |>.2.2
  obtain ⟨δ, hδ, hflat⟩ := compact_uniform_small_slope_of_fderiv_eq_zero
    hU hS hSU hdf hsecond ⟨ε, hε.le⟩ hε
  obtain ⟨r, hr, hrU⟩ := hS.exists_thickening_subset_open hU hSU
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro x hx y hy
  have hyδ := hy.trans_le (min_le_left _ _)
  have hyr := hy.trans_le (min_le_right _ _)
  have hsegdist (z) (hz : z ∈ segment ℝ x y) : dist z x ≤ dist y x := by
    simpa only [mem_closedBall, dist_comm x y] using segment_subset_closedBall_left x y hz
  have hsegU : segment ℝ x y ⊆ U := by
    intro z hz
    apply hrU
    exact mem_thickening_iff.mpr ⟨x, hx, (hsegdist z hz).trans_lt hyr⟩
  have hbound (z) (hz : z ∈ segment ℝ x y) : ‖fderiv ℝ f z‖ ≤ ε * dist y x := by
    have h := hflat x hx z ((hsegdist z hz).trans_lt hyδ)
    rw [hfirst x hx, dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hsegdist z hz) hε.le)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf.differentiableOn (by norm_num) z (hsegU hz)).differentiableAt
      (hU.mem_nhds (hsegU hz))) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [dist_eq_norm, pow_two, mul_assoc] using h

end LiquidDrop
