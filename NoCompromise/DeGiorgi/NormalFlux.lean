module

public import NoCompromise.DeGiorgi.Reduced
public import NoCompromise.DeGiorgi.RadialFlux

@[expose] public section

/-!
# Normal-flux comparison at a reduced point

The first inequality is a direct consequence of the defining unit vector limit.
The separately proved radial slicing identity supplies the exact Hausdorff
surface flux, completing the normal-flux lemma.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Near any reduced point, the polar mass is bounded by twice its inward
derivative flux against the limiting outward normal. -/
theorem eventually_normal_flux_comparison {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ reducedBoundaryOfPolar μ σ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), μ.real (ball x r) ≤
      -2 * inner ℝ (reducedNormalOfPolar μ σ x) (∫ y in ball x r, σ y ∂μ) := by
  let ν := reducedNormalOfPolar μ σ x
  have hν : ‖ν‖ = 1 := norm_reducedNormalOfPolar μ σ hx
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin n) => inner ℝ ν z) :=
    continuous_const.inner continuous_id
  have ht : Tendsto (fun r => inner ℝ ν (⨍ y in ball x r, σ y ∂μ))
      (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℝ)) := by
    have h := hc.continuousAt.tendsto.comp (tendsto_average_reducedNormalOfPolar μ σ hx)
    simpa only [ν, Function.comp_def, inner_neg_right, real_inner_self_eq_norm_sq,
      norm_reducedNormalOfPolar μ σ hx, one_pow] using h
  have he := ht.eventually (Iio_mem_nhds (show (-1 : ℝ) < -(1 / 2 : ℝ) by norm_num))
  filter_upwards [he, self_mem_nhdsWithin] with r hr hrpos
  have hmpos : 0 < μ (ball x r) :=
    (μ.mem_support_iff_forall x).mp hx.1 (ball x r) (ball_mem_nhds x hrpos)
  have hmfin : μ (ball x r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne
  have hmreal : 0 < μ.real (ball x r) := ENNReal.toReal_pos hmpos.ne' hmfin
  have hi : inner ℝ ν (∫ y in ball x r, σ y ∂μ) / μ.real (ball x r) < -(1 / 2 : ℝ) := by
    simpa only [setAverage_eq, inner_smul_right, smul_eq_mul, div_eq_inv_mul] using hr
  have hb := (div_lt_iff₀ hmreal).mp hi
  change μ.real (ball x r) ≤ -2 * inner ℝ ν (∫ y in ball x r, σ y ∂μ)
  linarith

theorem exists_normal_flux_comparison_radius {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ reducedBoundaryOfPolar μ σ) :
    ∃ δ > 0, ∀ r, 0 < r → r ≤ δ → μ.real (ball x r) ≤
      -2 * inner ℝ (reducedNormalOfPolar μ σ x) (∫ y in ball x r, σ y ∂μ) := by
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_normal_flux_comparison μ σ hx)
  exact ⟨δ, hδ, fun r hr hrd => hbound ⟨hr, hrd⟩⟩

/-- Blueprint normal-flux comparison for the actual perimeter measure and
distributional derivative of a measurable set of locally finite perimeter. -/
theorem normal_flux_comparison (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hE hmE) :
    ∃ δ > 0, ∀ r, 0 < r → r ≤ δ → (canonicalPerimeterMeasure E hE hmE).real (ball x r) ≤
      -2 * inner ℝ (reducedNormal E hE hmE x) (perimeterDerivativeBall E hE hmE x r) := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  exact exists_normal_flux_comparison_radius _ _ hx

/-- The complete normal-flux lemma, for every reduced point and all coordinate directions. -/
theorem normal_flux (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hE hmE) :
    (∃ δ > 0, ∀ r, 0 < r → r ≤ δ → (canonicalPerimeterMeasure E hE hmE).real (ball x r) ≤
      -2 * inner ℝ (reducedNormal E hE hmE x) (perimeterDerivativeBall E hE hmE x r)) ∧
    (∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin 3,
      perimeterDerivativeBall E hE hmE x r i =
        ∫ y in densityOne E ∩ sphere x r, (y - x) i / r ∂hausdorffMeasure2 3 ∧
      |perimeterDerivativeBall E hE hmE x r i| ≤
        (hausdorffMeasure2 3 (densityOne E ∩ sphere x r)).toReal) := by
  refine ⟨normal_flux_comparison E hE hmE hx, ?_⟩
  filter_upwards [ae_perimeterDerivativeBall_eq_surface_integral E hE hmE x,
    ae_abs_perimeterDerivativeBall_apply_le_sectionArea E hE hmE x] with r heq hbound
  exact fun i => ⟨heq i, hbound i⟩

end LiquidDrop
