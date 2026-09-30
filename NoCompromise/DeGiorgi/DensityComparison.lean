module

public import NoCompromise.Area.Linear
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section

/-!
# Positive lower density and Hausdorff null sets

Disjoint balls selected by the five-covering lemma control the cost of a
Hausdorff cover by the ambient measure. Outer regularity then gives domination
on arbitrary subsets of a uniform positive-density piece. Countable pieces
allow the density constants and radius thresholds to depend on the point.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter Function Metric TopologicalSpace
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

section Metric
variable {X : Type*} [MetricSpace X] [SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- A fivefold ball cover at any prescribed diameter scale, with disjoint
original balls contained in a prescribed open neighborhood. -/
theorem exists_density_five_cover {A U : Set X} (hU : IsOpen U) (hAU : A ⊆ U)
    {R : A → ℝ} {δ : ℝ} (hR : ∀ x, 0 < R x) (hδ : 0 < δ) :
    ∃ (r : A → ℝ) (t : Set A), t.Countable ∧
      t.PairwiseDisjoint (fun x => ball (x : X) (r x)) ∧
      (∀ x, 0 < r x ∧ r x < R x ∧ 10 * r x ≤ δ ∧ ball (x : X) (r x) ⊆ U) ∧
      A ⊆ ⋃ x : t, ball (x.val : X) (5 * r x.val) := by
  classical
  have hradius : ∀ x : A, ∃ r : ℝ,
      0 < r ∧ r < R x ∧ 10 * r ≤ δ ∧ ball (x : X) r ⊆ U := by
    intro x
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU x (hAU x.property)
    have hRx := hR x
    let r := min (ρ / 2) (min (R x / 2) (δ / 10))
    have hr : 0 < r := lt_min (by positivity) (lt_min (by positivity) (by positivity))
    have hrρ : r ≤ ρ / 2 := min_le_left _ _
    have hrR : r ≤ R x / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hrδ : r ≤ δ / 10 := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨r, hr, by linarith, by linarith,
      (ball_subset_ball (by linarith)).trans hρU⟩
  choose r hr using hradius
  obtain ⟨t, -, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball (univ : Set A)
      (fun x => (x : X)) r (δ / 10) (fun x _ => by have h := (hr x).2.2.1; linarith)
      5 (by norm_num)
  have ht : t.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x _ => ⟨x, mem_ball_self (hr x).1⟩)
  refine ⟨r, t, ht, hdisj, hr, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hcover ⟨x, hx⟩ (mem_univ _)
  exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy (mem_ball_self (hr ⟨x, hx⟩).1)⟩

omit [SeparableSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The diameter of a fivefold ball is at most ten times its original radius. -/
lemma ediam_five_ball_le (x : X) (r : ℝ) :
    ediam (ball x (5 * r)) ≤ ENNReal.ofReal (10 * r) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro y hy z hz
  have hy' := mem_ball.mp hy
  have hz' := mem_ball.mp hz
  have ht := dist_triangle y x z
  rw [dist_comm x z] at ht
  linarith

omit [SeparableSpace X] [BorelSpace X] in
/-- The squared diameter cost is controlled by a lower-density ball mass. -/
lemma density_ball_cover_cost (μ : Measure X) {c : ℝ} (hc : 0 < c)
    (x : X) {r : ℝ} (hr : 0 < r)
    (hμ : ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r)) :
    ediam (ball x (5 * r)) ^ (2 : ℝ) ≤ ENNReal.ofReal (100 / c) * μ (ball x r) := by
  have heq : ENNReal.ofReal (10 * r) ^ (2 : ℕ) =
      ENNReal.ofReal (100 / c) * ENNReal.ofReal (c * r ^ 2) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  calc
    ediam (ball x (5 * r)) ^ (2 : ℝ) = ediam (ball x (5 * r)) ^ (2 : ℕ) := by
      exact ENNReal.rpow_natCast _ 2
    _ ≤ ENNReal.ofReal (10 * r) ^ (2 : ℕ) := by gcongr; exact ediam_five_ball_le x r
    _ = _ := heq
    _ ≤ _ := by gcongr

/-- A uniform positive lower density controls unnormalized Hausdorff area by
the mass of every open neighborhood. -/
theorem hausdorff_two_le_open_of_pointwise_radius (μ : Measure X)
    {A U : Set X} {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x ∈ A, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r))
    (hU : IsOpen U) (hAU : A ⊆ U) :
    Measure.hausdorffMeasure 2 A ≤ ENNReal.ofReal (100 / c) * μ U := by
  classical
  let δ : ℕ → ℝ := fun k => 1 / (k + 1)
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  choose R hR hbound using fun x : A => hlower x x.property
  choose r t ht hd hr hcover using fun k => exists_density_five_cover hU hAU hR (hδ k)
  let (k : ℕ) : Countable (t k) := (ht k).to_subtype
  let C : (k : ℕ) → t k → Set X := fun k x => ball (x.val : X) (5 * r k x.val)
  have hdiam : ∀ k (x : t k), ediam (C k x) ≤ ENNReal.ofReal (δ k) := by
    intro k x
    exact (ediam_five_ball_le _ _).trans (ENNReal.ofReal_le_ofReal (hr k x.val).2.2.1)
  have hδlim : Tendsto (fun k => ENNReal.ofReal (δ k)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, δ, Function.comp_def] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmass (k : ℕ) : ∑' x : t k, ediam (C k x) ^ (2 : ℝ) ≤
      ENNReal.ofReal (100 / c) * μ U := by
    calc
      ∑' x : t k, ediam (C k x) ^ (2 : ℝ) ≤
          ∑' x : t k, ENNReal.ofReal (100 / c) * μ (ball (x.val : X) (r k x.val)) :=
        ENNReal.tsum_le_tsum fun x => density_ball_cover_cost μ hc _ (hr k x.val).1
          (hbound x.val _ (hr k x.val).1 (hr k x.val).2.1)
      _ = ENNReal.ofReal (100 / c) * μ (⋃ x : t k, ball (x.val : X) (r k x.val)) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion]
        · exact (hd k).subtype _ _
        · exact fun _ => measurableSet_ball
      _ ≤ _ := by
        gcongr
        exact iUnion_subset fun x => (hr k x.val).2.2.2
  exact (Measure.hausdorffMeasure_le_liminf_tsum 2 A
    (fun k => ENNReal.ofReal (δ k)) hδlim C
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)).trans
    (liminf_le_of_frequently_le (Eventually.of_forall hmass).frequently)

/-- The uniform-radius instance of the open-neighborhood estimate. -/
theorem hausdorff_two_le_open_of_lower_density (μ : Measure X)
    {A U : Set X} {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlower : ∀ x ∈ A, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r))
    (hU : IsOpen U) (hAU : A ⊆ U) :
    Measure.hausdorffMeasure 2 A ≤ ENNReal.ofReal (100 / c) * μ U :=
  hausdorff_two_le_open_of_pointwise_radius μ hc
    (fun x hx => ⟨R, hR, hlower x hx⟩) hU hAU

/-- Quantitative domination with one common positive density constant and a
radius threshold that may depend on the point. -/
theorem hausdorff_two_le_of_pointwise_radius (μ : Measure X) [μ.OuterRegular]
    {A : Set X} {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x ∈ A, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r)) :
    Measure.hausdorffMeasure 2 A ≤ ENNReal.ofReal (100 / c) * μ A := by
  have hC : ENNReal.ofReal (100 / c) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  rw [A.measure_eq_iInf_isOpen μ]
  simp only [ENNReal.mul_iInf_of_ne hC ENNReal.ofReal_ne_top]
  exact le_iInf fun U => le_iInf fun hAU => le_iInf fun hU =>
    hausdorff_two_le_open_of_pointwise_radius μ hc hlower hU hAU


/-- Quantitative Hausdorff domination on a uniform positive lower-density piece.
No measurability of the set and no finiteness of its mass is assumed. -/
theorem hausdorff_two_le_of_lower_density (μ : Measure X) [μ.OuterRegular]
    {A : Set X} {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlower : ∀ x ∈ A, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r)) :
    Measure.hausdorffMeasure 2 A ≤ ENNReal.ofReal (100 / c) * μ A := by
  have hC : ENNReal.ofReal (100 / c) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  rw [A.measure_eq_iInf_isOpen μ]
  simp only [ENNReal.mul_iInf_of_ne hC ENNReal.ofReal_ne_top]
  exact le_iInf fun U => le_iInf fun hAU => le_iInf fun hU =>
    hausdorff_two_le_open_of_lower_density μ hc hR hlower hU hAU

/-- Uniform positive lower density transfers measure-zero sets to Hausdorff-zero sets. -/
theorem hausdorff_two_null_of_lower_density (μ : Measure X) [μ.OuterRegular]
    {A : Set X} {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlower : ∀ x ∈ A, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r)) (hA : μ A = 0) :
    Measure.hausdorffMeasure 2 A = 0 := by
  have h := hausdorff_two_le_of_lower_density μ hc hR hlower
  simpa only [hA, mul_zero, nonpos_iff_eq_zero] using h

/-- The lower-density constants and radius thresholds may depend on the point.
A countable reciprocal-scale cover reduces this statement to the uniform estimate. -/
theorem hausdorff_two_null_of_pointwise_lower_density (μ : Measure X) [μ.OuterRegular]
    {A : Set X} (hA : μ A = 0)
    (hlower : ∀ x ∈ A, ∃ c > 0, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r)) :
    Measure.hausdorffMeasure 2 A = 0 := by
  let a : ℕ → ℝ := fun n => 1 / (n + 1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  let S : ℕ → Set X := fun n => {x | x ∈ A ∧ ∀ r, 0 < r → r < a n →
    ENNReal.ofReal (a n * r ^ 2) ≤ μ (ball x r)}
  have hS (n : ℕ) : Measure.hausdorffMeasure 2 (S n) = 0 :=
    hausdorff_two_null_of_lower_density μ (ha n) (ha n) (fun _ hx => hx.2)
      (measure_mono_null (fun _ hx => hx.1) hA)
  apply measure_mono_null (t := ⋃ n, S n) _ (measure_iUnion_null hS)
  intro x hx
  obtain ⟨c, hc, R, hR, hxbound⟩ := hlower x hx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hc hR)
  have hn' : a n < min c R := hn
  refine mem_iUnion.mpr ⟨n, hx, ?_⟩
  intro r hr hrn
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (hn'.trans_le (min_le_left _ _)).le (sq_nonneg r))).trans
    (hxbound r hr (hrn.trans (hn'.trans_le (min_le_right _ _))))

/-- Every measure-null subset of a pointwise positive lower-density set is H²-null. -/
theorem hausdorff_two_inter_null_of_pointwise_lower_density
    (μ : Measure X) [μ.OuterRegular] {S N : Set X} (hN : μ N = 0)
    (hlower : ∀ x ∈ S, ∃ c > 0, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r)) :
    Measure.hausdorffMeasure 2 (S ∩ N) = 0 :=
  hausdorff_two_null_of_pointwise_lower_density μ
    (measure_mono_null inter_subset_right hN) (fun x hx => hlower x hx.1)

omit [SeparableSpace X] [BorelSpace X] in
/-- Positive extended-real lower density supplies pointwise lower ball bounds.
The density convention is `liminf μ(B_r x) / r²` as positive radii tend to zero. -/
lemma exists_lower_density_bound_of_liminf_pos (μ : Measure X) (x : X)
    (hx : 0 < liminf (fun r : ℝ => μ (ball x r) / ENNReal.ofReal (r ^ 2)) (𝓝[>] 0)) :
    ∃ c > 0, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r) := by
  obtain ⟨c, -, hc, hclim⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx
  have hc' : 0 < c := ENNReal.ofReal_pos.mp hc
  have hevent := eventually_lt_of_lt_liminf hclim
  obtain ⟨R, hR, hbound⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨c, hc', R, hR, fun r hr hrR => ?_⟩
  have hcr := hbound (show r ∈ ball (0 : ℝ) R ∩ Ioi 0 from
    ⟨by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr] using hrR, hr⟩)
  rw [ENNReal.ofReal_mul hc'.le]
  exact ENNReal.mul_le_of_le_div hcr.le

/-- The countable-scale density-to-Hausdorff null transfer, stated directly in
terms of positive lower density. The null set need not be Borel. -/
theorem hausdorff_two_inter_null_of_liminf_density_pos
    (μ : Measure X) [μ.OuterRegular] {S N : Set X} (hN : μ N = 0)
    (hS : ∀ x ∈ S, 0 < liminf
      (fun r : ℝ => μ (ball x r) / ENNReal.ofReal (r ^ 2)) (𝓝[>] 0)) :
    Measure.hausdorffMeasure 2 (S ∩ N) = 0 :=
  hausdorff_two_inter_null_of_pointwise_lower_density μ hN
    (fun x hx => exists_lower_density_bound_of_liminf_pos μ x (hS x hx))


omit [SeparableSpace X] [BorelSpace X] in
/-- The same ball lower bound from the real-valued lower-density convention.
No finite-mass premise is needed: `ofReal (μ B).toReal ≤ μ B` holds also at infinity. -/
lemma exists_lower_density_bound_of_real_liminf_pos (μ : Measure X) (x : X)
    (hx : 0 < liminf (fun r : ℝ => (μ (ball x r)).toReal / r ^ 2) (𝓝[>] 0)) :
    ∃ c > 0, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r) := by
  obtain ⟨c, hc, hclim⟩ := exists_between hx
  have hb : IsBoundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ))
      (fun r : ℝ => (μ (ball x r)).toReal / r ^ 2) :=
    isBoundedUnder_of ⟨0, fun r => div_nonneg ENNReal.toReal_nonneg (sq_nonneg r)⟩
  have hevent := eventually_lt_of_lt_liminf hclim hb
  obtain ⟨R, hR, hbound⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨c, hc, R, hR, fun r hr hrR => ?_⟩
  have hcr := hbound (show r ∈ ball (0 : ℝ) R ∩ Ioi 0 from
    ⟨by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr] using hrR, hr⟩)
  exact (ENNReal.ofReal_le_ofReal
    ((le_div_iff₀ (sq_pos_of_pos hr)).mp hcr.le)).trans ENNReal.ofReal_toReal_le

/-- Null transfer for positive lower density using real ball masses. -/
theorem hausdorff_two_inter_null_of_real_liminf_density_pos
    (μ : Measure X) [μ.OuterRegular] {S N : Set X} (hN : μ N = 0)
    (hS : ∀ x ∈ S, 0 < liminf
      (fun r : ℝ => (μ (ball x r)).toReal / r ^ 2) (𝓝[>] 0)) :
    Measure.hausdorffMeasure 2 (S ∩ N) = 0 :=
  hausdorff_two_inter_null_of_pointwise_lower_density μ hN
    (fun x hx => exists_lower_density_bound_of_real_liminf_pos μ x (hS x hx))

end Metric

/-- Universal constant in the normalized Hausdorff comparison. Its only factor
apart from the five-cover cost is the fixed planar Hausdorff normalization. -/
def densityComparisonConstant : ℝ :=
  100 * (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (Measure.hausdorffMeasure (2 : ℕ)) : ℝ≥0)

lemma densityComparisonConstant_pos : 0 < densityComparisonConstant := by
  unfold densityComparisonConstant
  apply mul_pos (by norm_num)
  exact_mod_cast (pos_iff_ne_zero.mpr
    (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2))

/-- Normalized H² domination with a common density constant and thresholds
allowed to vary pointwise. The comparison constant is independent of the ambient dimension. -/
theorem hausdorffMeasure2_le_of_pointwise_radius {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.OuterRegular]
    {A : Set (EuclideanSpace ℝ (Fin n))} {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x ∈ A, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r)) :
    hausdorffMeasure2 n A ≤ ENNReal.ofReal (densityComparisonConstant / c) * μ A := by
  let a : ℝ≥0 := Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) (Measure.hausdorffMeasure (2 : ℕ))
  have hconst : (a : ℝ≥0∞) * ENNReal.ofReal (100 / c) =
      ENNReal.ofReal (densityComparisonConstant / c) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg a)]
    congr 1
    dsimp only [densityComparisonConstant, a]
    ring
  unfold hausdorffMeasure2
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  calc
    (a : ℝ≥0∞) * Measure.hausdorffMeasure 2 A ≤
        a * (ENNReal.ofReal (100 / c) * μ A) :=
      mul_le_mul' le_rfl (hausdorff_two_le_of_pointwise_radius μ hc hlower)
    _ = _ := by rw [← mul_assoc, hconst]

/-- The uniform-radius normalized Hausdorff comparison. -/
theorem hausdorffMeasure2_le_of_lower_density {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.OuterRegular]
    {A : Set (EuclideanSpace ℝ (Fin n))} {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hlower : ∀ x ∈ A, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r)) :
    hausdorffMeasure2 n A ≤ ENNReal.ofReal (densityComparisonConstant / c) * μ A :=
  hausdorffMeasure2_le_of_pointwise_radius μ hc (fun x hx => ⟨R, hR, hlower x hx⟩)

/-- Transfer an unnormalized Hausdorff nullity statement to the project's
normalized Hausdorff area. -/
lemma hausdorffMeasure2_eq_zero_of_hausdorff_two_eq_zero {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : Measure.hausdorffMeasure 2 A = 0) :
    hausdorffMeasure2 n A = 0 := by
  simp [hausdorffMeasure2, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hA]

/-- Point-dependent positive lower-density pieces transfer ambient null sets
to normalized Hausdorff null sets, without any measurability assumption on the pieces. -/
theorem hausdorffMeasure2_inter_null_of_pointwise_lower_density {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.OuterRegular]
    {S N : Set (EuclideanSpace ℝ (Fin n))} (hN : μ N = 0)
    (hlower : ∀ x ∈ S, ∃ c > 0, ∃ R > 0, ∀ r, 0 < r → r < R →
      ENNReal.ofReal (c * r ^ 2) ≤ μ (ball x r)) :
    hausdorffMeasure2 n (S ∩ N) = 0 :=
  hausdorffMeasure2_eq_zero_of_hausdorff_two_eq_zero
    (hausdorff_two_inter_null_of_pointwise_lower_density μ hN hlower)

/-- Normalized Hausdorff null transfer from positive extended-real lower two-density. -/
theorem hausdorffMeasure2_inter_null_of_liminf_density_pos {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.OuterRegular]
    {S N : Set (EuclideanSpace ℝ (Fin n))} (hN : μ N = 0)
    (hS : ∀ x ∈ S, 0 < liminf
      (fun r : ℝ => μ (ball x r) / ENNReal.ofReal (r ^ 2)) (𝓝[>] 0)) :
    hausdorffMeasure2 n (S ∩ N) = 0 :=
  hausdorffMeasure2_eq_zero_of_hausdorff_two_eq_zero
    (hausdorff_two_inter_null_of_liminf_density_pos μ hN hS)

/-- Normalized Hausdorff null transfer from positive real lower two-density. -/
theorem hausdorffMeasure2_inter_null_of_real_liminf_density_pos {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.OuterRegular]
    {S N : Set (EuclideanSpace ℝ (Fin n))} (hN : μ N = 0)
    (hS : ∀ x ∈ S, 0 < liminf
      (fun r : ℝ => (μ (ball x r)).toReal / r ^ 2) (𝓝[>] 0)) :
    hausdorffMeasure2 n (S ∩ N) = 0 :=
  hausdorffMeasure2_eq_zero_of_hausdorff_two_eq_zero
    (hausdorff_two_inter_null_of_real_liminf_density_pos μ hN hS)

end LiquidDrop
