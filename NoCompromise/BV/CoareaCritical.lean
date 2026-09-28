import NoCompromise.Measure.LevelSetCover
import NoCompromise.BV.Compactness
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Critical level sets have zero codimension-one area almost everywhere

Blueprint `lem:coarea-critical-part`, for every dimension at least two and a `C¹`
function on an arbitrary open Euclidean domain. Hausdorff measure is normalized
Euclidean Hausdorff measure.

Strict differentiability and the compact Lebesgue-number lemma give arbitrarily small
uniform slopes near a compact critical set. Finite half-open grid covers have total
volume bounded independently of scale. Their image intervals therefore have integrated
Hausdorff covering cost tending to zero. The finite-cover criterion from `LevelSetCover`
uses Fatou's lemma without any measurability assumption on Hausdorff content. A compact
exhaustion finishes the local theorem. No Sard theorem or coarea formula is used.
-/

noncomputable section

open MeasureTheory Filter Set Metric InnerProductSpace
open scoped ENNReal NNReal Topology Gradient

namespace LiquidDrop

/-- Near a compact critical set, the scalar function has uniformly arbitrarily small slopes. -/
lemma compact_critical_uniform_small_slope {n : ℕ}
    {U S : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiffOn ℝ 1 u U) (hzero : ∀ x ∈ S, gradient u x = 0)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ S, ∀ y, dist y x < δ → dist (u y) (u x) ≤ ε * dist y x := by
  have hlocal (x : S) : ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ (x : EuclideanSpace ℝ (Fin n)) ∈ V ∧ LipschitzOnWith ε u V := by
    have hD : fderiv ℝ u x = 0 := by rw [← toDual_gradient, hzero x x.property, map_zero]
    have hc := hu.contDiffAt (hU.mem_nhds (hSU x.property))
    obtain ⟨V, hV, hLip⟩ := hc.exists_lipschitzOnWith_of_nnnorm_lt ε
      (by simpa [hD] using hε)
    exact ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV,
      hLip.mono interior_subset⟩
  choose V hVo hVx hLip using hlocal
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric hS hVo
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hxy
  obtain ⟨i, hi⟩ := hcover x hx
  exact (hLip i).dist_le_mul y (hi hxy) x (hi (mem_ball_self hδ))

/-- A side-`δ` grid cell has extended diameter at most `n * δ`. -/
lemma ediam_gridCell_le {n : ℕ} (δ : ℝ) (k : Fin n → ℤ) :
    ediam (gridCell δ k) ≤ ENNReal.ofReal ((n : ℝ) * δ) := by
  apply ediam_le_of_forall_dist_le
  intro x hx y hy
  simpa only [dist_eq_norm] using norm_sub_le_of_mem_gridCell hy hx

/-- Cells of side at most one meeting a bounded set lie in a single fixed larger ball. -/
lemma gridCell_subset_closedBall_of_meets {n : ℕ} {δ R : ℝ} (hδ : δ ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSR : S ⊆ closedBall 0 R)
    {k : Fin n → ℤ} (hk : (S ∩ gridCell δ k).Nonempty) :
    gridCell δ k ⊆ closedBall 0 (R + n) := by
  obtain ⟨x, hxS, hxk⟩ := hk
  intro y hy
  have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp (hSR hxS)
  have hdist := norm_sub_le_of_mem_gridCell hxk hy
  have hd : (n : ℝ) * δ ≤ n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  apply mem_closedBall_zero_iff.mpr
  calc
    ‖y‖ ≤ ‖y - x‖ + ‖x‖ := norm_le_norm_sub_add _ _
    _ ≤ R + n := by linarith

/-- Disjoint grid cells meeting a bounded set have uniformly bounded total volume. -/
lemma sum_volume_gridCell_le {n : ℕ} {δ R : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSR : S ⊆ closedBall 0 R)
    {ι : Type*} [Fintype ι] (k : ι → Fin n → ℤ) (hk : Function.Injective k)
    (hmeet : ∀ i, (S ∩ gridCell δ (k i)).Nonempty) :
    ∑ i, volume (gridCell δ (k i)) ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + n)) := by
  have hdisj : Pairwise (fun i j => Disjoint (gridCell δ (k i)) (gridCell δ (k j))) := by
    intro i j hij
    exact gridCell_pairwise_disjoint hδ (fun heq => hij (hk heq))
  have hu := measure_iUnion (μ := volume) hdisj (fun i => measurableSet_gridCell δ (k i))
  rw [tsum_fintype] at hu
  rw [← hu]
  exact measure_mono (iUnion_subset fun i =>
    gridCell_subset_closedBall_of_meets hδone hSR (hmeet i))

/-- A small image interval gives a codimension-one covering cost bounded by cell volume. -/
lemma gridCell_level_cost_le {n : ℕ} (hn : 1 ≤ n) {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (k : Fin n → ℤ) (a : ℝ) :
    ediam (gridCell δ k) ^ ((n - 1 : ℕ) : ℝ) *
      volume (Icc (a - ε * ((n : ℝ) * δ)) (a + ε * ((n : ℝ) * δ))) ≤
      ENNReal.ofReal (2 * (n : ℝ) ^ n * ε) * volume (gridCell δ k) := by
  rw [Real.volume_Icc, show (a + ε * ((n : ℝ) * δ)) -
    (a - ε * ((n : ℝ) * δ)) = 2 * (ε * ((n : ℝ) * δ)) by ring,
    ENNReal.rpow_natCast, volume_gridCell]
  have hnδ : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ
  calc
    _ ≤ (ENNReal.ofReal ((n : ℝ) * δ)) ^ (n - 1) *
        ENNReal.ofReal (2 * (ε * ((n : ℝ) * δ))) := by
      gcongr
      exact ediam_gridCell_le δ k
    _ = ENNReal.ofReal (((n : ℝ) * δ) ^ (n - 1) *
        (2 * (ε * ((n : ℝ) * δ)))) := by
      rw [← ENNReal.ofReal_pow hnδ, ← ENNReal.ofReal_mul (pow_nonneg hnδ _)]
    _ = ENNReal.ofReal ((2 * (n : ℝ) ^ n * ε) * δ ^ n) := by
      congr 1
      calc
        _ = 2 * ε * (((n : ℝ) * δ) ^ (n - 1) * ((n : ℝ) * δ)) := by ring
        _ = 2 * ε * ((n : ℝ) * δ) ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        _ = _ := by rw [mul_pow]; ring
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hδ]

/-- The integrated finite-cover estimate, with explicit dimensional factor `2 * n^n`. -/
lemma grid_level_cover_cost_le {n : ℕ} (hn : 1 ≤ n) {δ ε R : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 ≤ ε)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hSR : S ⊆ closedBall 0 R)
    {ι : Type*} [Fintype ι] (k : ι → Fin n → ℤ) (hk : Function.Injective k)
    (hmeet : ∀ i, (S ∩ gridCell δ (k i)).Nonempty) (a : ι → ℝ) :
    ∑ i, ediam (gridCell δ (k i)) ^ ((n - 1 : ℕ) : ℝ) *
      volume (Icc (a i - ε * ((n : ℝ) * δ)) (a i + ε * ((n : ℝ) * δ))) ≤
      ENNReal.ofReal (2 * (n : ℝ) ^ n * ε) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + n)) := by
  calc
    _ ≤ ∑ i, ENNReal.ofReal (2 * (n : ℝ) ^ n * ε) * volume (gridCell δ (k i)) :=
      Finset.sum_le_sum fun i _ => gridCell_level_cost_le hn hδ.le hε (k i) (a i)
    _ = ENNReal.ofReal (2 * (n : ℝ) ^ n * ε) * ∑ i, volume (gridCell δ (k i)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul' le_rfl (sum_volume_gridCell_le hδ hδone hSR k hk hmeet)

/-- Uniformly vanishing local slopes on a bounded set force almost every fiber
to have zero normalized codimension-one Hausdorff measure. -/
lemma ae_null_fibers_of_bounded_uniform_small_slope {n : ℕ} (hn : 2 ≤ n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : Bornology.IsBounded S)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ ρ > 0, ∀ x ∈ S, ∀ y,
      dist y x < ρ → dist (u y) (u x) ≤ ε * dist y x) :
    ∀ᵐ t ∂volume, Measure.euclideanHausdorffMeasure (n - 1) (S ∩ u ⁻¹' {t}) = 0 := by
  classical
  obtain ⟨R, _, hSR⟩ := hS.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  have hSR' : S ⊆ closedBall 0 R := hSR.trans ball_subset_closedBall
  let ε : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have hεpos (k : ℕ) : 0 < ε k := pow_pos (by norm_num) _
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  choose ρ hρ hsl using fun k => hsmall ⟨ε k, (hεpos k).le⟩ (hεpos k)
  have hδex (k : ℕ) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ (n : ℝ) * δ < ε k ∧
      (n : ℝ) * δ < ρ k := by
    have hb : 0 < min 1 (min (ε k / (n + 1)) (ρ k / (n + 1))) := by
      exact lt_min (by norm_num) (lt_min (div_pos (hεpos k) (by positivity))
        (div_pos (hρ k) (by positivity)))
    obtain ⟨δ, hδpos, hδlt⟩ := exists_between hb
    have hδone := (lt_min_iff.mp hδlt).1
    have hδeps := (lt_min_iff.mp (lt_min_iff.mp hδlt).2).1
    have hδrho := (lt_min_iff.mp (lt_min_iff.mp hδlt).2).2
    have ha := (lt_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mp hδeps
    have hb := (lt_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mp hδrho
    exact ⟨δ, hδpos, hδone.le, by nlinarith, by nlinarith⟩
  choose δ hδpos hδone hδε hδρ using hδex
  let J : ℕ → Type := fun k => {j : Fin n → ℤ // (S ∩ gridCell (δ k) j).Nonempty}
  let (k : ℕ) : Fintype (J k) := (finite_gridCells_meeting (hδpos k) hS).fintype
  have hsample (k : ℕ) (j : J k) : ∃ x, x ∈ S ∧ x ∈ gridCell (δ k) j.val := j.property
  choose a haS haC using hsample
  let C : ∀ k, J k → Set (EuclideanSpace ℝ (Fin n)) := fun k j => gridCell (δ k) j.val
  let I : ∀ k, J k → Set ℝ := fun k j =>
    Icc (u (a k j) - ε k * ((n : ℝ) * δ k)) (u (a k j) + ε k * ((n : ℝ) * δ k))
  have hmass (k : ℕ) :
      ∑ j, ediam (C k j) ^ ((n - 1 : ℕ) : ℝ) * volume (I k j) ≤
        ENNReal.ofReal (2 * (n : ℝ) ^ n * ε k) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + n)) := by
    exact grid_level_cover_cost_le (by omega) (hδpos k) (hδone k) (hεpos k).le hSR'
      (fun j : J k => j.val) Subtype.coe_injective (fun j => j.property) (fun j => u (a k j))
  apply ae_euclideanHausdorffMeasure_fiber_eq_zero_of_covers (n - 1) (by omega)
    u S C I (fun _ _ => measurableSet_Icc) (fun k => ENNReal.ofReal (ε k))
    (by simpa using ENNReal.tendsto_ofReal hεlim)
  · intro k j
    exact (ediam_gridCell_le (δ k) j.val).trans (ENNReal.ofReal_le_ofReal (hδε k).le)
  · intro k x hx
    exact mem_iUnion.mpr ⟨⟨gridIndex (δ k) x, x, hx, mem_gridCell_gridIndex (hδpos k) x⟩,
      mem_gridCell_gridIndex (hδpos k) x⟩
  · intro k j t ht
    obtain ⟨y, ⟨hyS, hyC⟩, rfl⟩ := ht
    have hd : dist y (a k j) ≤ (n : ℝ) * δ k := by
      simpa only [dist_eq_norm] using norm_sub_le_of_mem_gridCell (haC k j) hyC
    have hbound := hsl k (a k j) (haS k j) y (hd.trans_lt (hδρ k))
    have hbound' : |u y - u (a k j)| ≤ ε k * dist y (a k j) := by
      change dist (u y) (u (a k j)) ≤ ε k * dist y (a k j) at hbound
      simpa only [Real.dist_eq] using hbound
    have he : |u y - u (a k j)| ≤ ε k * ((n : ℝ) * δ k) :=
      hbound'.trans (mul_le_mul_of_nonneg_left hd (hεpos k).le)
    exact ⟨by linarith [(abs_le.mp he).1], by linarith [(abs_le.mp he).2]⟩
  · have hcost : Tendsto (fun k => ENNReal.ofReal (2 * (n : ℝ) ^ n * ε k))
        atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (hεlim.const_mul (2 * (n : ℝ) ^ n))
    have hfin : volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + n)) ≠ ∞ :=
      (isCompact_closedBall _ _).measure_lt_top.ne
    have hcost' := ENNReal.Tendsto.mul_const hcost (Or.inr hfin)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hcost') (fun _ => bot_le) hmass

/-- The critical-level assertion on an arbitrary compact critical subset of the domain. -/
lemma ae_null_fibers_compact_critical {n : ℕ} (hn : 2 ≤ n)
    {U S : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiffOn ℝ 1 u U) (hzero : ∀ x ∈ S, gradient u x = 0) :
    ∀ᵐ t ∂volume, Measure.euclideanHausdorffMeasure (n - 1) (S ∩ u ⁻¹' {t}) = 0 :=
  ae_null_fibers_of_bounded_uniform_small_slope hn hS.isBounded u
    (compact_critical_uniform_small_slope hU hS hSU hu hzero)

/-- Blueprint `lem:coarea-critical-part`: critical points contribute zero
normalized codimension-one Hausdorff measure on almost every level. -/
lemma coarea_critical_part {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiffOn ℝ 1 u U) :
    ∀ᵐ t ∂volume, Measure.euclideanHausdorffMeasure (n - 1)
      {x | x ∈ U ∧ gradient u x = 0 ∧ u x = t} = 0 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  let A : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun j => Subtype.val '' K j
  have hAc (j : ℕ) : IsCompact (A j) := (K.isCompact j).image continuous_subtype_val
  have hAU (j : ℕ) : A j ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.property
  let S : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun j => A j ∩ gradient u ⁻¹' {0}
  have hSc (j : ℕ) : IsCompact (S j) := by
    apply (hAc j).of_isClosed_subset _ inter_subset_left
    have hc := (continuousOn_gradient_of_contDiffOn hU hu).mono (hAU j)
    exact hc.preimage_isClosed_of_isClosed (hAc j).isClosed isClosed_singleton
  have hnull (j : ℕ) : ∀ᵐ t ∂volume,
      Measure.euclideanHausdorffMeasure (n - 1) (S j ∩ u ⁻¹' {t}) = 0 :=
    ae_null_fibers_compact_critical hn hU (hSc j) (inter_subset_left.trans (hAU j)) hu
      (fun _ hx => hx.2)
  filter_upwards [ae_all_iff.mpr hnull] with t ht
  apply measure_mono_null (t := ⋃ j, S j ∩ u ⁻¹' {t}) _ (measure_iUnion_null ht)
  intro x hx
  obtain ⟨j, hj⟩ := K.exists_mem ⟨x, hx.1⟩
  exact mem_iUnion.mpr ⟨j, ⟨⟨⟨⟨x, hx.1⟩, hj, rfl⟩, hx.2.1⟩, hx.2.2⟩⟩

end LiquidDrop
