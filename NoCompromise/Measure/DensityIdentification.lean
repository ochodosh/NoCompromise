module

public import NoCompromise.Measure.BallDifferentiation
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# Identifying locally finite measures by open-ball density

Open-ball Besicovitch differentiation applied to the real Radon--Nikodym density
identifies an absolutely continuous measure from its almost-everywhere ball-mass
ratios. Restriction fractions then transfer density limits from Borel pieces to
the ambient measure, including across countable conull covers.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

variable {n : ℕ}

/-- The real Radon--Nikodym density is locally integrable when the numerator
measure is locally finite; total mass may be infinite. -/
lemma locallyIntegrable_toReal_rnDeriv
    (μ ρ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ] :
    LocallyIntegrable (fun x => (μ.rnDeriv ρ x).toReal) ρ := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact Measure.integrableOn_toReal_rnDeriv (hK.measure_lt_top.ne)

/-- Actual Radon--Nikodym differentiation over open balls for locally finite
Euclidean measures, in the real ball-mass convention. -/
theorem ae_tendsto_measureReal_ball_ratio_rnDeriv
    (μ ρ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ρ] (hμρ : μ ≪ ρ) :
    ∀ᵐ x ∂ρ, Tendsto (fun r => μ.real (ball x r) / ρ.real (ball x r))
      (𝓝[>] 0) (𝓝 (μ.rnDeriv ρ x).toReal) := by
  filter_upwards [ae_tendsto_average_ball ρ (locallyIntegrable_toReal_rnDeriv μ ρ)] with x hx
  convert hx using 1
  ext r
  rw [setAverage_eq, Measure.setIntegral_toReal_rnDeriv hμρ]
  simp only [smul_eq_mul, div_eq_inv_mul]

/-- Equality follows from absolute continuity and almost-everywhere unit ball
ratios, without a finite-total-mass hypothesis. -/
theorem measure_eq_of_ae_tendsto_measureReal_ball_ratio_one
    (μ ρ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ρ] (hμρ : μ ≪ ρ)
    (hratio : ∀ᵐ x ∂ρ, Tendsto (fun r => μ.real (ball x r) / ρ.real (ball x r))
      (𝓝[>] 0) (𝓝 1)) : μ = ρ := by
  apply (Measure.rnDeriv_eq_one_iff_eq hμρ).mp
  filter_upwards [ae_tendsto_measureReal_ball_ratio_rnDeriv μ ρ hμρ, hratio] with x hx hy
  exact (ENNReal.toReal_eq_one_iff _).mp (tendsto_nhds_unique hx hy)

/-- Almost every point of a Borel set sees asymptotically all of the measure
inside that set. The balls are open even when spheres carry positive mass. -/
theorem ae_tendsto_restrict_measureReal_ball_ratio
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    ∀ᵐ x ∂μ.restrict S,
      Tendsto (fun r => (μ.restrict S).real (ball x r) / μ.real (ball x r))
        (𝓝[>] 0) (𝓝 1) := by
  filter_upwards [ae_restrict_of_ae
    (ae_tendsto_measureReal_ball_ratio_rnDeriv (μ.restrict S) μ
      Measure.absolutelyContinuous_restrict),
    ae_restrict_of_ae (Measure.rnDeriv_restrict_self μ hS), ae_restrict_mem hS]
    with x hx hder hxS
  simpa only [hder, indicator_of_mem hxS, Pi.one_apply, ENNReal.toReal_one] using hx

/-- Restriction mass fractions transfer any finite quadratic density limit
from a restricted measure to the original measure. -/
lemma tendsto_measureReal_ball_density_of_fraction
    (μ ν : Measure (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) {d : ℝ}
    (hfrac : Tendsto (fun r => ν.real (ball x r) / μ.real (ball x r))
      (𝓝[>] 0) (𝓝 1))
    (hν : Tendsto (fun r : ℝ => ν.real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun r : ℝ => μ.real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 d) := by
  have hquot := hν.div hfrac (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hquot
  apply hquot.congr'
  filter_upwards [hfrac.eventually_ne (by norm_num : (1 : ℝ) ≠ 0), self_mem_nhdsWithin]
    with r hr hrpos
  have hνr : ν.real (ball x r) ≠ 0 := (div_ne_zero_iff.mp hr).1
  have hμr : μ.real (ball x r) ≠ 0 := (div_ne_zero_iff.mp hr).2
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  dsimp only [Pi.div_apply]
  field_simp

/-- Almost-everywhere quadratic density of a restricted measure is the same
quadratic density of the ambient measure at almost every point of that piece. -/
theorem ae_tendsto_measureReal_ball_density_of_restrict
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (d : EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ᵐ x ∂μ.restrict S, Tendsto
      (fun r : ℝ => (μ.restrict S).real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 (d x))) :
    ∀ᵐ x ∂μ.restrict S, Tendsto
      (fun r : ℝ => μ.real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 (d x)) := by
  filter_upwards [ae_tendsto_restrict_measureReal_ball_ratio μ hS, hd] with x hx hy
  exact tendsto_measureReal_ball_density_of_fraction μ (μ.restrict S) x hx hy

/-- Quadratic density limits on a countable conull Borel cover determine the
quadratic density of the entire locally finite measure. -/
theorem ae_tendsto_measureReal_ball_density_of_countable_cover
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    (S : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ j, MeasurableSet (S j))
    (hcover : μ (⋃ j, S j)ᶜ = 0) (d : EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ j, ∀ᵐ x ∂μ.restrict (S j), Tendsto
      (fun r : ℝ => (μ.restrict (S j)).real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 (d x))) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => μ.real (ball x r) / r ^ 2)
      (𝓝[>] 0) (𝓝 (d x)) := by
  have hpiece : ∀ j, ∀ᵐ x ∂μ, x ∈ S j → Tendsto
      (fun r : ℝ => μ.real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 (d x)) :=
    fun j => (ae_restrict_iff' (hS j)).mp
      (ae_tendsto_measureReal_ball_density_of_restrict μ (hS j) d (hd j))
  filter_upwards [ae_all_iff.mpr hpiece, show ∀ᵐ x ∂μ, x ∈ ⋃ j, S j from ae_iff.mpr hcover]
    with x hx hxcover
  obtain ⟨j, hj⟩ := mem_iUnion.mp hxcover
  exact hx j hj


/-- Equal nonzero quadratic density limits give unit open-ball mass ratio. -/
lemma tendsto_measureReal_ball_ratio_of_equal_density
    (μ ρ : Measure (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    {d : ℝ} (hd : d ≠ 0)
    (hμ : Tendsto (fun r : ℝ => μ.real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 d))
    (hρ : Tendsto (fun r : ℝ => ρ.real (ball x r) / r ^ 2) (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun r => μ.real (ball x r) / ρ.real (ball x r)) (𝓝[>] 0) (𝓝 1) := by
  have hquot := hμ.div hρ hd
  rw [div_self hd] at hquot
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact div_div_div_cancel_right₀ (pow_ne_zero 2 (ne_of_gt hr)) _ _

/-- Two absolutely comparable locally finite measures with the same positive
quadratic density almost everywhere for the denominator measure are equal. -/
theorem measure_eq_of_ae_equal_positive_ball_density
    (μ ρ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ρ] (hμρ : μ ≪ ρ)
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hpos : ∀ᵐ x ∂ρ, 0 < d x)
    (hμ : ∀ᵐ x ∂ρ, Tendsto (fun r : ℝ => μ.real (ball x r) / r ^ 2)
      (𝓝[>] 0) (𝓝 (d x)))
    (hρ : ∀ᵐ x ∂ρ, Tendsto (fun r : ℝ => ρ.real (ball x r) / r ^ 2)
      (𝓝[>] 0) (𝓝 (d x))) : μ = ρ := by
  apply measure_eq_of_ae_tendsto_measureReal_ball_ratio_one μ ρ hμρ
  filter_upwards [hpos, hμ, hρ] with x hx hμx hρx
  exact tendsto_measureReal_ball_ratio_of_equal_density μ ρ x hx.ne' hμx hρx

/-- The convenient mutual-absolute-continuity form permits each density limit
to be stated almost everywhere for its own measure. -/
theorem measure_eq_of_mutually_absolutelyContinuous_of_ae_density
    (μ ρ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ρ]
    (hμρ : μ ≪ ρ) (hρμ : ρ ≪ μ)
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hpos : ∀ᵐ x ∂ρ, 0 < d x)
    (hμ : ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => μ.real (ball x r) / r ^ 2)
      (𝓝[>] 0) (𝓝 (d x)))
    (hρ : ∀ᵐ x ∂ρ, Tendsto (fun r : ℝ => ρ.real (ball x r) / r ^ 2)
      (𝓝[>] 0) (𝓝 (d x))) : μ = ρ :=
  measure_eq_of_ae_equal_positive_ball_density μ ρ hμρ d hpos (hρμ.ae_le hμ) hρ


/-- Restriction fractions transfer limits with any chosen radius normalization,
including `π * r²`; the normalization itself requires no hypotheses. -/
lemma tendsto_measureReal_ball_quotient_of_fraction
    (μ ν : Measure (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (q : ℝ → ℝ) {d : ℝ}
    (hfrac : Tendsto (fun r => ν.real (ball x r) / μ.real (ball x r))
      (𝓝[>] 0) (𝓝 1))
    (hν : Tendsto (fun r => ν.real (ball x r) / q r) (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun r => μ.real (ball x r) / q r) (𝓝[>] 0) (𝓝 d) := by
  have hquot := hν.div hfrac (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hquot
  apply hquot.congr'
  filter_upwards [hfrac.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with r hr
  exact div_div_div_cancel_left' _ _ (div_ne_zero_iff.mp hr).1

/-- Pointwise radius normalization is preserved in passing from a Borel piece
to the ambient locally finite measure. -/
theorem ae_tendsto_measureReal_ball_quotient_of_restrict
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (q : ℝ → ℝ) (d : EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ᵐ x ∂μ.restrict S, Tendsto
      (fun r => (μ.restrict S).real (ball x r) / q r) (𝓝[>] 0) (𝓝 (d x))) :
    ∀ᵐ x ∂μ.restrict S, Tendsto
      (fun r => μ.real (ball x r) / q r) (𝓝[>] 0) (𝓝 (d x)) := by
  filter_upwards [ae_tendsto_restrict_measureReal_ball_ratio μ hS, hd] with x hx hy
  exact tendsto_measureReal_ball_quotient_of_fraction μ (μ.restrict S) x q hx hy

/-- Countable-cover density globalization for an arbitrary radius normalization.
In the surface application take `q r = π * r²` and `d x = 1`. -/
theorem ae_tendsto_measureReal_ball_quotient_of_countable_cover
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    (S : ℕ → Set (EuclideanSpace ℝ (Fin n))) (hS : ∀ j, MeasurableSet (S j))
    (hcover : μ (⋃ j, S j)ᶜ = 0) (q : ℝ → ℝ) (d : EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ j, ∀ᵐ x ∂μ.restrict (S j), Tendsto
      (fun r => (μ.restrict (S j)).real (ball x r) / q r) (𝓝[>] 0) (𝓝 (d x))) :
    ∀ᵐ x ∂μ, Tendsto (fun r => μ.real (ball x r) / q r)
      (𝓝[>] 0) (𝓝 (d x)) := by
  have hpiece : ∀ j, ∀ᵐ x ∂μ, x ∈ S j → Tendsto
      (fun r => μ.real (ball x r) / q r) (𝓝[>] 0) (𝓝 (d x)) :=
    fun j => (ae_restrict_iff' (hS j)).mp
      (ae_tendsto_measureReal_ball_quotient_of_restrict μ (hS j) q d (hd j))
  filter_upwards [ae_all_iff.mpr hpiece, show ∀ᵐ x ∂μ, x ∈ ⋃ j, S j from ae_iff.mpr hcover]
    with x hx hxcover
  obtain ⟨j, hj⟩ := mem_iUnion.mp hxcover
  exact hx j hj

end LiquidDrop
