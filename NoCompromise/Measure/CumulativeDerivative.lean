module

public import NoCompromise.Measure.WeakDerivativeOne
public import NoCompromise.Measure.RadialMeasures
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Distributional derivatives of cumulative integrals

Fubini and the ordinary fundamental theorem of calculus identify the weak
derivative of a cumulative integral. This is the measure-theoretic step in
the radial flux argument, before any surface identification.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace LiquidDrop

/-- Cumulative masses have the expected distributional derivative. -/
theorem integral_cumulative_mul_deriv {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {f g : α → ℝ} (hf : Integrable f μ) (hg : Measurable g)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ r : ℝ, (∫ x in {x | g x < r}, f x ∂μ) * deriv ψ r) =
      -(∫ x, ψ (g x) * f x ∂μ) := by
  let S : Set (ℝ × α) := {p | g p.2 < p.1}
  have hS : MeasurableSet S := measurableSet_lt (hg.comp measurable_snd) measurable_fst
  let F : ℝ × α → ℝ := S.indicator (fun p => deriv ψ p.1 * f p.2)
  have hiψ : Integrable (deriv ψ) :=
    (hψ.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcψ.deriv
  have hiF : Integrable F (volume.prod μ) := (hiψ.mul_prod hf).indicator hS
  have hleft (r : ℝ) : (∫ x, F (r, x) ∂μ) =
      deriv ψ r * ∫ x in {x | g x < r}, f x ∂μ := by
    rw [← integral_const_mul, ← integral_indicator (measurableSet_lt hg measurable_const)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : g x < r <;> simp [F, S, hx]
  have hright (x : α) : (∫ r : ℝ, F (r, x)) = -ψ (g x) * f x := by
    calc
      _ = ∫ r in Ioi (g x), deriv ψ r * f x := by
        rw [← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        apply Eventually.of_forall
        intro r
        by_cases hr : g x < r <;> simp [F, S, hr]
      _ = (∫ r in Ioi (g x), deriv ψ r) * f x := integral_mul_const _ _
      _ = _ := by rw [hcψ.integral_Ioi_deriv_eq hψ]
  calc
    _ = ∫ r : ℝ, ∫ x, F (r, x) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun r => by dsimp only; rw [hleft]; ring
    _ = ∫ x, (∫ r : ℝ, F (r, x)) ∂μ :=
      integral_integral_swap (f := fun r x => F (r, x)) hiF
    _ = -(∫ x, ψ (g x) * f x ∂μ) := by
      simp_rw [hright, neg_mul]
      exact integral_neg _

/-- The cumulative integral over balls has the radial distributional derivative,
without finite total mass or any hypothesis on sphere atoms. -/
theorem integral_ball_mul_deriv {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrable f μ)
    (a : EuclideanSpace ℝ (Fin n)) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ r : ℝ, (∫ x in Metric.ball a r, f x ∂μ) * deriv ψ r) =
      -(∫ x, ψ (dist x a) * f x ∂μ) := by
  obtain ⟨R, hR, hsR⟩ := hcψ.isBounded.exists_pos_norm_lt
  let K := Metric.closedBall a R
  have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  have hif : Integrable (K.indicator f) μ :=
    (hf.integrableOn_isCompact (isCompact_closedBall a R)).integrable_indicator hK
  have hc := integral_cumulative_mul_deriv μ hif (g := fun x => dist x a)
    (continuous_id.dist continuous_const).measurable hψ hcψ
  have hleft (r : ℝ) : (∫ x in Metric.ball a r, K.indicator f x ∂μ) * deriv ψ r =
      (∫ x in Metric.ball a r, f x ∂μ) * deriv ψ r := by
    by_cases hr : r < R
    · congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact indicator_of_mem
        ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr.le)) hx) f
    · have hout : r ∉ tsupport ψ := by
        intro hmem
        have hh := hsR r hmem
        exact (not_lt_of_ge (le_trans (le_of_not_gt hr) (le_abs_self r))) hh
      rw [deriv_of_notMem_tsupport hout, mul_zero, mul_zero]
  have hright (x : EuclideanSpace ℝ (Fin n)) :
      ψ (dist x a) * K.indicator f x = ψ (dist x a) * f x := by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
    · have hd : R < dist x a := by simpa only [K, Metric.mem_closedBall, not_le] using hx
      have hout : dist x a ∉ tsupport ψ := by
        intro hmem
        have hh := hsR (dist x a) hmem
        rw [Real.norm_of_nonneg dist_nonneg] at hh
        exact (not_lt_of_ge hd.le) hh
      rw [image_eq_zero_of_notMem_tsupport hout, zero_mul, zero_mul]
  change (∫ r : ℝ, (∫ x in Metric.ball a r, K.indicator f x ∂μ) * deriv ψ r) = _ at hc
  simpa only [hleft, hright] using hc

/-- Restricting the radial test identity to positive radii loses nothing. -/
theorem integral_ball_mul_deriv_Ioi {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyIntegrable f μ)
    (a : EuclideanSpace ℝ (Fin n)) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ r in Ioi (0 : ℝ), (∫ x in Metric.ball a r, f x ∂μ) * deriv ψ r) =
      -(∫ x, ψ (dist x a) * f x ∂μ) := by
  rw [← integral_ball_mul_deriv μ hf a hψ hcψ, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro r
  dsimp only
  by_cases hr : 0 < r
  · exact indicator_of_mem hr _
  · rw [indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr)]
    simp only [Metric.ball_eq_empty.mpr (le_of_not_gt hr), setIntegral_empty, zero_mul]

end LiquidDrop
