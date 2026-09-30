module

public import NoCompromise.Measure.BallAverages
public import NoCompromise.Measure.BallDifferentiation
public import NoCompromise.DeGiorgi.PolarDifferentiation
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section

/-!
# Reduced boundary of a polar derivative

The input density `σ` represents the distributional derivative. Thus the outward
normal is the negative of its ball-average limit. Open balls and the full limit
through positive real radii are used, with Borel measurability proved through
rational radii. The definitions and exact representative invariance are separate
from existence of the polar derivative of a finite-perimeter set.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Points in the polar measure's support where its derivative-density average
has a unit limit. The density has the derivative sign, not the outward sign. -/
def reducedBoundaryOfPolar {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  μ.support ∩ {x | ∃ z, ‖z‖ = 1 ∧
    Tendsto (fun r => ⨍ y in ball x r, σ y ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 z)}

/-- The outward normal is the negative radial derivative-density limit.
Away from the convergence set, `limUnder` supplies an arbitrary total value. -/
def reducedNormalOfPolar {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  -limUnder (comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ)))
    (fun q : ℚ => ⨍ y in ball x (q : ℝ), σ y ∂μ)

theorem measurableSet_reducedBoundaryOfPolar {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : Measurable σ) (hi : LocallyIntegrable σ μ) :
    MeasurableSet (reducedBoundaryOfPolar μ σ) :=
  μ.isClosed_support.measurableSet.inter (measurableSet_exists_unit_ball_average_limit μ hσ hi)

theorem measurable_reducedNormalOfPolar {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [SFinite μ]
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσ : Measurable σ) : Measurable (reducedNormalOfPolar μ σ) := by
  exact (StronglyMeasurable.limUnder
    (fun q : ℚ => (measurable_average_ball μ hσ (q : ℝ)).stronglyMeasurable)).measurable.neg

lemma reducedNormalOfPolar_eq_neg_of_tendsto {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x z : EuclideanSpace ℝ (Fin n))
    (h : Tendsto (fun r => ⨍ y in ball x r, σ y ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 z)) :
    reducedNormalOfPolar μ σ x = -z := by
  have : NeBot (comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ))) :=
    neBot_comap_rat_nhdsGT_zero
  have hq : Tendsto (fun q : ℚ => ⨍ y in ball x (q : ℝ), σ y ∂μ)
      (comap (fun q : ℚ => (q : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 z) :=
    h.comp tendsto_comap
  exact congrArg Neg.neg hq.limUnder_eq

lemma norm_reducedNormalOfPolar {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ reducedBoundaryOfPolar μ σ) :
    ‖reducedNormalOfPolar μ σ x‖ = 1 := by
  obtain ⟨_, z, hz, ht⟩ := hx
  rw [reducedNormalOfPolar_eq_neg_of_tendsto μ σ x z ht, norm_neg, hz]

lemma tendsto_average_reducedNormalOfPolar {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ reducedBoundaryOfPolar μ σ) :
    Tendsto (fun r => ⨍ y in ball x r, σ y ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (-reducedNormalOfPolar μ σ x)) := by
  obtain ⟨_, z, _, ht⟩ := hx
  rw [reducedNormalOfPolar_eq_neg_of_tendsto μ σ x z ht, neg_neg]
  exact ht

theorem ae_mem_reducedBoundaryOfPolar {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hi : LocallyIntegrable σ μ) (hu : ∀ᵐ x ∂μ, ‖σ x‖ = 1) :
    ∀ᵐ x ∂μ, x ∈ reducedBoundaryOfPolar μ σ := by
  filter_upwards [μ.support_mem_ae, ae_tendsto_average_ball μ hi, hu] with x hx ht hnorm
  exact ⟨hx, σ x, hnorm, ht⟩

theorem measure_compl_reducedBoundaryOfPolar {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hi : LocallyIntegrable σ μ) (hu : ∀ᵐ x ∂μ, ‖σ x‖ = 1) :
    μ (reducedBoundaryOfPolar μ σ)ᶜ = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_mem_reducedBoundaryOfPolar μ hi hu] with x hx
  exact fun h => h hx

theorem reducedNormalOfPolar_ae_eq_neg {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hi : LocallyIntegrable σ μ) : reducedNormalOfPolar μ σ =ᵐ[μ] -σ := by
  filter_upwards [ae_tendsto_average_ball μ hi] with x hx
  exact reducedNormalOfPolar_eq_neg_of_tendsto μ σ x (σ x) hx

lemma average_ball_congr_ae {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {σ τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (h : σ =ᵐ[μ] τ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    (⨍ y in ball x r, σ y ∂μ) = ⨍ y in ball x r, τ y ∂μ := by
  simp only [setAverage_eq]
  rw [integral_congr_ae (ae_restrict_of_ae h)]

/-- The reduced set is exactly unchanged by an almost-everywhere change of
polar density; this is equality of sets, not only equality modulo null sets. -/
theorem reducedBoundaryOfPolar_congr_ae {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {σ τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (h : σ =ᵐ[μ] τ) :
    reducedBoundaryOfPolar μ σ = reducedBoundaryOfPolar μ τ := by
  simp_rw [reducedBoundaryOfPolar, average_ball_congr_ae μ h]

theorem reducedNormalOfPolar_congr_ae {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {σ τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (h : σ =ᵐ[μ] τ) :
    reducedNormalOfPolar μ σ = reducedNormalOfPolar μ τ := by
  funext x
  simp_rw [reducedNormalOfPolar, average_ball_congr_ae μ h]

/-- A chosen ambient perimeter measure, subsequently characterized on every
open set by the original variational definition of perimeter. -/
def canonicalPerimeterMeasure (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) : Measure AmbientSpace :=
  (exists_ambient_outward_perimeter_polar hE hmE).choose

def canonicalOutwardPolarDensity (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) : AmbientSpace → AmbientSpace :=
  (exists_ambient_outward_perimeter_polar hE hmE).choose_spec.choose

theorem canonicalPerimeterPolar (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) :
    IsAmbientOutwardPerimeterPolar E (canonicalPerimeterMeasure E hE hmE)
      (canonicalOutwardPolarDensity E hE hmE) :=
  (exists_ambient_outward_perimeter_polar hE hmE).choose_spec.choose_spec

theorem canonicalPerimeterMeasure_open (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {O : Set AmbientSpace} (hO : IsOpen O) :
    canonicalPerimeterMeasure E hE hmE O = perimeterIn E O :=
  (canonicalPerimeterPolar E hE hmE).open_eq O hO

/-- Blueprint reduced boundary: the support points where the normalized
distributional derivative on open balls has a unit limit. -/
def reducedBoundary (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) : Set AmbientSpace :=
  reducedBoundaryOfPolar (canonicalPerimeterMeasure E hE hmE)
    (-canonicalOutwardPolarDensity E hE hmE)

/-- The outward normal of the reduced boundary, with the blueprint minus sign. -/
def reducedNormal (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) : AmbientSpace → AmbientSpace :=
  reducedNormalOfPolar (canonicalPerimeterMeasure E hE hmE)
    (-canonicalOutwardPolarDensity E hE hmE)

theorem measurableSet_reducedBoundary (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    MeasurableSet (reducedBoundary E hE hmE) := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  exact measurableSet_reducedBoundaryOfPolar _ h.measurable.neg h.locallyIntegrable.neg

theorem measurable_reducedNormal (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    Measurable (reducedNormal E hE hmE) := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  exact measurable_reducedNormalOfPolar _ h.measurable.neg

theorem norm_reducedNormal (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hE hmE) : ‖reducedNormal E hE hmE x‖ = 1 :=
  norm_reducedNormalOfPolar _ _ hx

theorem ae_mem_reducedBoundary (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) :
    ∀ᵐ x ∂canonicalPerimeterMeasure E hE hmE, x ∈ reducedBoundary E hE hmE := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  apply ae_mem_reducedBoundaryOfPolar _ h.locallyIntegrable.neg
  simpa only [Pi.neg_apply, norm_neg] using h.norm_ae

theorem measure_compl_reducedBoundary (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    canonicalPerimeterMeasure E hE hmE (reducedBoundary E hE hmE)ᶜ = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_mem_reducedBoundary E hE hmE] with x hx
  exact fun h => h hx

theorem reducedNormal_ae_eq_polarDensity (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    reducedNormal E hE hmE =ᵐ[canonicalPerimeterMeasure E hE hmE]
      canonicalOutwardPolarDensity E hE hmE := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  simpa only [reducedNormal, neg_neg] using
    reducedNormalOfPolar_ae_eq_neg _ h.locallyIntegrable.neg

/-- The distributional perimeter derivative evaluated on an open ball. -/
def perimeterDerivativeBall (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace) (r : ℝ) : AmbientSpace :=
  ∫ y in ball x r, -canonicalOutwardPolarDensity E hE hmE y
    ∂canonicalPerimeterMeasure E hE hmE

theorem tendsto_normalized_perimeterDerivativeBall (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) {x : AmbientSpace}
    (hx : x ∈ reducedBoundary E hE hmE) :
    Tendsto (fun r => ((canonicalPerimeterMeasure E hE hmE).real (ball x r))⁻¹ •
      perimeterDerivativeBall E hE hmE x r) (𝓝[>] (0 : ℝ))
        (𝓝 (-reducedNormal E hE hmE x)) := by
  simpa only [setAverage_eq, reducedNormal, perimeterDerivativeBall, Pi.neg_apply] using
    tendsto_average_reducedNormalOfPolar _ _ hx

/-- The actual reduced normal has the open-ball Lebesgue-point property. -/
theorem polar_differentiation (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) :
    ∀ᵐ x ∂canonicalPerimeterMeasure E hE hmE,
      Tendsto (fun r => ⨍ y in ball x r,
        ‖reducedNormal E hE hmE y - reducedNormal E hE hmE x‖
        ∂canonicalPerimeterMeasure E hE hmE) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  have hi : LocallyIntegrable (reducedNormal E hE hmE) (canonicalPerimeterMeasure E hE hmE) := by
    apply locallyIntegrable_of_ae_norm_le (C := 1) _
      (measurable_reducedNormal E hE hmE).aestronglyMeasurable
    filter_upwards [ae_mem_reducedBoundary E hE hmE] with x hx
    exact (norm_reducedNormal E hE hmE hx).le
  exact ae_tendsto_average_norm_sub_ball _ hi

end LiquidDrop
