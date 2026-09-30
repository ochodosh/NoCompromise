module

public import NoCompromise.Area.Linear
public import Mathlib.MeasureTheory.Measure.Hausdorff

@[expose] public section

/-!
# Upper density and Hausdorff comparison

Small-set mass estimates follow from upper ball bounds at any point of the set.
The metric outer-measure construction converts them into Hausdorff domination,
without requiring measurability of the set on which the bounds hold.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

section Metric
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- A uniform upper ball bound controls the mass of every sufficiently small set. -/
lemma measure_inter_le_diam_sq_of_upper_density (μ : Measure X)
    {A : Set X} {C R : ℝ} (hR : 0 < R)
    (hupper : ∀ x ∈ A, ∀ r : ℝ, 0 < r → r < R →
      μ (ball x r) ≤ ENNReal.ofReal (C * r ^ 2))
    {S : Set X} (hS : ediam S ≤ ENNReal.ofReal (R / 2)) :
    μ (S ∩ A) ≤ ENNReal.ofReal C * ediam S ^ (2 : ℝ) := by
  by_cases hn : (S ∩ A).Nonempty
  · obtain ⟨x, hxS, hxA⟩ := hn
    have hfin : ediam S ≠ ∞ := (hS.trans_lt ENNReal.ofReal_lt_top).ne
    have hd : diam S ≤ R / 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hS
    have hdR : diam S < R := by linarith
    have hcont : Continuous (fun r : ℝ => ENNReal.ofReal (C * r ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ 2))
        (𝓝[>] (diam S)) (𝓝 (ENNReal.ofReal (C * diam S ^ 2))) :=
      (hcont.tendsto (diam S)).mono_left nhdsWithin_le_nhds
    have hb : μ (S ∩ A) ≤ ENNReal.ofReal (C * diam S ^ 2) := by
      apply ge_of_tendsto ht
      filter_upwards [Ioo_mem_nhdsGT hdR] with r hr
      have hp : 0 < r := diam_nonneg.trans_lt hr.1
      apply (measure_mono (show S ∩ A ⊆ ball x r from fun y hy => ?_)).trans
        (hupper x hxA r hp hr.2)
      exact (dist_le_diam_of_mem' hfin hy.1 hxS).trans_lt hr.1
    convert hb using 1
    rw [ENNReal.ofReal_mul' (sq_nonneg _), ENNReal.ofReal_pow (diam_nonneg : 0 ≤ diam S),
      diam, ENNReal.ofReal_toReal hfin]
    norm_num
  · rw [not_nonempty_iff_eq_empty.mp hn, measure_empty]
    exact bot_le

/-- Uniform upper quadratic density gives Hausdorff domination on arbitrary sets. -/
theorem measure_le_hausdorff_two_of_upper_density (μ : Measure X)
    {A : Set X} {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hupper : ∀ x ∈ A, ∀ r : ℝ, 0 < r → r < R →
      μ (ball x r) ≤ ENNReal.ofReal (C * r ^ 2)) :
    μ A ≤ ENNReal.ofReal C * Measure.hausdorffMeasure 2 A := by
  have hb := OuterMeasure.le_mkMetric
    (fun d : ℝ≥0∞ => ENNReal.ofReal C * d ^ (2 : ℝ))
    (OuterMeasure.restrict A μ.toOuterMeasure) (ENNReal.ofReal (R / 2))
    (ENNReal.ofReal_pos.mpr (by positivity))
    (fun S hS => by
      simpa only [OuterMeasure.restrict_apply, Measure.coe_toOuterMeasure] using
        measure_inter_le_diam_sq_of_upper_density μ hR hupper hS)
  have heq : (fun d : ℝ≥0∞ => ENNReal.ofReal C * d ^ (2 : ℝ)) =
      ENNReal.ofReal C • (fun d : ℝ≥0∞ => d ^ (2 : ℝ)) := rfl
  rw [heq, OuterMeasure.mkMetric_smul _ ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.mpr hC).ne'] at hb
  have hA := hb A
  simpa only [OuterMeasure.restrict_apply, inter_self, smul_apply,
    smul_eq_mul, Measure.coe_toOuterMeasure, OuterMeasure.coe_mkMetric,
    Measure.hausdorffMeasure] using hA

/-- Point-dependent finite upper density transfers Hausdorff-null sets to measure-null sets. -/
theorem measure_null_of_pointwise_upper_density (μ : Measure X)
    {A : Set X} (hA : Measure.hausdorffMeasure 2 A = 0)
    (hupper : ∀ x ∈ A, ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ r : ℝ, 0 < r → r < R → μ (ball x r) ≤ ENNReal.ofReal (C * r ^ 2)) :
    μ A = 0 := by
  let G (k m : ℕ) : Set X := {x ∈ A | ∀ r : ℝ, 0 < r → r < 1 / ((m : ℝ) + 1) →
    μ (ball x r) ≤ ENNReal.ofReal (((k : ℝ) + 1) * r ^ 2)}
  have hn (k m : ℕ) : μ (G k m) = 0 := by
    have hb := measure_le_hausdorff_two_of_upper_density μ
      (show (0 : ℝ) < k + 1 by positivity) (show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity)
      (A := G k m) (fun x hx => hx.2)
    rw [measure_mono_null (show G k m ⊆ A from fun _ hx => hx.1) hA, mul_zero] at hb
    exact le_antisymm hb bot_le
  apply measure_mono_null (t := ⋃ k, ⋃ m, G k m) ?_
    (measure_iUnion_null fun k => measure_iUnion_null (hn k))
  intro x hx
  obtain ⟨C, R, hC, hR, hb⟩ := hupper x hx
  obtain ⟨k, hk⟩ := exists_nat_gt C
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hR
  refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨m, hx, ?_⟩⟩
  intro r hr hsmall
  apply (hb r hr (hsmall.trans hm)).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)

end Metric
/-- Nullity for normalized Euclidean area implies nullity for unnormalized H². -/
lemma hausdorff_two_eq_zero_of_hausdorffMeasure2_eq_zero {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : hausdorffMeasure2 n A = 0) :
    Measure.hausdorffMeasure 2 A = 0 := by
  unfold hausdorffMeasure2 at hA
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply] at hA
  simp only [ENNReal.smul_def, smul_eq_mul] at hA
  exact (mul_eq_zero.mp hA).resolve_left
    (ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2))

/-- Normalized-area nullity and pointwise finite upper density imply measure nullity. -/
theorem measure_null_of_pointwise_upper_density_normalized {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : hausdorffMeasure2 n A = 0)
    (hupper : ∀ x ∈ A, ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ r : ℝ, 0 < r → r < R → μ (ball x r) ≤ ENNReal.ofReal (C * r ^ 2)) : μ A = 0 :=
  measure_null_of_pointwise_upper_density μ
    (hausdorff_two_eq_zero_of_hausdorffMeasure2_eq_zero hA) hupper

end LiquidDrop
