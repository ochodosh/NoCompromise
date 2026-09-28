import NoCompromise.DeGiorgi.Rectifiability
import NoCompromise.DeGiorgi.DensityComparison
import NoCompromise.DeGiorgi.UpperDensity
import NoCompromise.Area.Rectifiable
import NoCompromise.Area.GraphCoverDensity

/-!
# De Giorgi structure and Gauss--Green

The exact perimeter density yields uniform lower and upper density constants
with point-dependent radii. Hausdorff comparison transfers the graph cover's
null remainder, and identifies the null sets of perimeter and reduced-boundary
area. Unit graph-piece density and differentiation identify the measures exactly,
and the reduced normal gives the signed derivative and Gauss--Green formula.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
namespace LiquidDrop

/-- At each reduced point, perimeter is bounded between fixed multiples of r²
at all sufficiently small positive radii. -/
theorem exists_perimeter_density_bounds (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE) :
    ∃ R > 0, ∀ r : ℝ, 0 < r → r < R →
      ENNReal.ofReal (Real.pi / 2 * r ^ 2) ≤ canonicalPerimeterMeasure E hE hmE (ball x r) ∧
      canonicalPerimeterMeasure E hE hmE (ball x r) ≤ ENNReal.ofReal (2 * Real.pi * r ^ 2) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  have ht := tendsto_perimeter_div_radius_sq E hE hmE hx
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0,
      Real.pi / 2 < μ.real (ball x r) / r ^ 2 ∧
      μ.real (ball x r) / r ^ 2 < 2 * Real.pi :=
    ht.eventually (Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  obtain ⟨R, hR, hb⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨R, hR, fun r hr hsmall => ?_⟩
  have hh := hb (show r ∈ ball (0 : ℝ) R ∩ Ioi 0 from
    ⟨by simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr] using hsmall, hr⟩)
  have hf : μ (ball x r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal hf).mpr
      ((lt_div_iff₀ (sq_pos_of_pos hr)).mp hh.1).le,
    (ENNReal.le_ofReal_iff_toReal_le hf (by positivity)).mpr
      ((div_lt_iff₀ (sq_pos_of_pos hr)).mp hh.2).le⟩

/-- Reduced-boundary area is uniformly dominated by canonical perimeter on every subset. -/
theorem hausdorffMeasure2_reducedBoundary_inter_le (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (A : Set AmbientSpace) :
    hausdorffMeasure2 3 (A ∩ reducedBoundary E hE hmE) ≤
      ENNReal.ofReal (densityComparisonConstant / (Real.pi / 2)) *
        canonicalPerimeterMeasure E hE hmE A := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let := (canonicalPerimeterPolar E hE hmE).regular
  apply (hausdorffMeasure2_le_of_pointwise_radius μ
    (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2)) ?_).trans
    (mul_le_mul' le_rfl (measure_mono inter_subset_left))
  intro x hx
  obtain ⟨R, hR, hb⟩ := exists_perimeter_density_bounds E hE hmE hx.2
  exact ⟨R, hR, fun r hr hsmall => (hb r hr hsmall).1⟩

/-- A perimeter-null set meets the reduced boundary in an area-null set. -/
theorem hausdorffMeasure2_reducedBoundary_inter_null (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {A : Set AmbientSpace} (hA : canonicalPerimeterMeasure E hE hmE A = 0) :
    hausdorffMeasure2 3 (A ∩ reducedBoundary E hE hmE) = 0 := by
  have hb := hausdorffMeasure2_reducedBoundary_inter_le E hE hmE A
  rw [hA, mul_zero] at hb
  exact le_antisymm hb bot_le

/-- The reduced boundary is countably rectifiable for normalized Hausdorff area. -/
theorem countablyH2Rectifiable_reducedBoundary (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    CountablyH2Rectifiable (reducedBoundary E hE hmE) := by
  obtain ⟨e, f, hf, hnull⟩ := canonicalPerimeterMeasure_carried_by_graphs E hE hmE
  let g (j : ℕ) (p : EuclideanSpace ℝ (Fin 2)) : AmbientSpace := e j (graphMapN (f j) p)
  have hg (j : ℕ) : LipschitzWith 2 (g j) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (e j (graphMapN (f j) p)) (e j (graphMapN (f j) q)) ≤ (2 : ℝ) * dist p q
    rw [(e j).dist_map]
    have hb := (lipschitzWith_graphMapN (hf j)).dist_le_mul p q
    norm_num only [NNReal.coe_add, NNReal.coe_one] at hb
    exact hb
  refine ⟨(measurableSet_reducedBoundary E hE hmE).nullMeasurableSet,
    g, fun _ => 2, hg, ?_⟩
  have hh := hausdorffMeasure2_reducedBoundary_inter_null E hE hmE hnull
  convert hh using 1
  congr 1
  ext x
  simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, and_comm, g]

/-- Hausdorff area restricted to the reduced boundary is finite on compact sets. -/
theorem reducedBoundary_area_finiteOnCompacts (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    IsFiniteMeasureOnCompacts ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) := by
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  constructor
  intro K hK
  rw [Measure.restrict_apply hK.measurableSet]
  exact (hausdorffMeasure2_reducedBoundary_inter_le E hE hmE K).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top)

/-- Reduced-boundary area is absolutely continuous with respect to perimeter. -/
theorem reducedBoundary_area_absolutelyContinuous_perimeter (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE) ≪
      canonicalPerimeterMeasure E hE hmE := by
  intro A hA
  rw [Measure.restrict_apply' (measurableSet_reducedBoundary E hE hmE)]
  exact hausdorffMeasure2_reducedBoundary_inter_null E hE hmE hA

/-- Canonical perimeter is absolutely continuous with respect to reduced-boundary area. -/
theorem perimeter_absolutelyContinuous_reducedBoundary_area (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    canonicalPerimeterMeasure E hE hmE ≪
      (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE) := by
  intro A hA
  rw [Measure.restrict_apply' (measurableSet_reducedBoundary E hE hmE)] at hA
  have hnull : canonicalPerimeterMeasure E hE hmE (A ∩ reducedBoundary E hE hmE) = 0 := by
    apply measure_null_of_pointwise_upper_density_normalized _ hA
    intro x hx
    obtain ⟨R, hR, hb⟩ := exists_perimeter_density_bounds E hE hmE hx.2
    exact ⟨2 * Real.pi, R, by positivity, hR, fun r hr hsmall => (hb r hr hsmall).2⟩
  have hcompl : canonicalPerimeterMeasure E hE hmE (reducedBoundary E hE hmE)ᶜ = 0 :=
    ae_iff.mp (ae_mem_reducedBoundary E hE hmE)
  apply measure_mono_null (t := (A ∩ reducedBoundary E hE hmE) ∪
    (reducedBoundary E hE hmE)ᶜ) ?_ (measure_union_null hnull hcompl)
  intro x hx
  by_cases hs : x ∈ reducedBoundary E hE hmE
  · exact Or.inl ⟨hx, hs⟩
  · exact Or.inr hs

/-- The reduced-boundary area measure is Radon. -/
theorem reducedBoundary_area_regular (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).Regular := by
  let := reducedBoundary_area_finiteOnCompacts E hE hmE
  infer_instance

/-- The reduced-boundary area measure has exact unit surface density almost everywhere. -/
theorem ae_reducedBoundary_area_density (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE),
      Tendsto (fun r : ℝ =>
        ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).real (ball x r) /
          (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 1) := by
  let := reducedBoundary_area_finiteOnCompacts E hE hmE
  obtain ⟨e, f, hf, hcover⟩ := canonicalPerimeterMeasure_carried_by_graphs E hE hmE
  exact ae_area_density_of_graph_cover _ (measurableSet_reducedBoundary E hE hmE)
    e f (fun _ => 1) hf ((reducedBoundary_area_absolutelyContinuous_perimeter E hE hmE) hcover)

/-- Canonical perimeter is precisely normalized Hausdorff area on the reduced boundary. -/
theorem canonicalPerimeterMeasure_eq_reducedBoundary_area (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    canonicalPerimeterMeasure E hE hmE =
      (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE) := by
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  let := reducedBoundary_area_finiteOnCompacts E hE hmE
  apply measure_eq_of_mutually_absolutelyContinuous_of_ae_density _ _
    (perimeter_absolutelyContinuous_reducedBoundary_area E hE hmE)
    (reducedBoundary_area_absolutelyContinuous_perimeter E hE hmE)
    (fun _ => Real.pi) (Filter.Eventually.of_forall fun _ => Real.pi_pos)
  · filter_upwards [ae_mem_reducedBoundary E hE hmE] with x hx
    exact tendsto_perimeter_div_radius_sq E hE hmE hx
  · filter_upwards [ae_reducedBoundary_area_density E hE hmE] with x hx
    have ht := hx.mul_const Real.pi
    simp only [one_mul] at ht
    convert ht using 1
    funext r
    rw [mul_comm Real.pi, div_mul_eq_div_div, div_mul_cancel₀ _ Real.pi_ne_zero]

/-- The outward reduced normal is the exact Hausdorff-area polar field. -/
theorem reducedBoundary_outwardPerimeterPolar (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    IsAmbientOutwardPerimeterPolar E
      ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) (reducedNormal E hE hmE) := by
  rw [← canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE]
  have h := canonicalPerimeterPolar E hE hmE
  have hν := reducedNormal_ae_eq_polarDensity E hE hmE
  refine ⟨h.regular, h.finiteOnCompacts, measurable_reducedNormal E hE hmE,
    ?_, h.open_eq, ?_, ?_⟩
  · filter_upwards [hν, h.norm_ae] with x hx hnorm
    rwa [hx]
  · intro i φ hφ
    rw [h.coordinate_eq i φ hφ]
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    rw [hx]
  · intro X hX hcX
    rw [h.divergence_eq X hX hcX]
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    rw [hx]

/-- Perimeter on any open region equals its reduced-boundary area. -/
theorem perimeterIn_eq_reducedBoundary_area (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {O : Set AmbientSpace} (hO : IsOpen O) :
    perimeterIn E O = hausdorffMeasure2 3 (O ∩ reducedBoundary E hE hmE) := by
  rw [← (reducedBoundary_outwardPerimeterPolar E hE hmE).open_eq O hO,
    Measure.restrict_apply hO.measurableSet]

/-- The unchanged global perimeter convention equals total reduced-boundary area. -/
theorem perimeter_eq_reducedBoundary_area (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    perimeter E = hausdorffMeasure2 3 (reducedBoundary E hE hmE) := by
  rw [← perimeterN_eq_perimeter E hmE]
  simpa only [perimeterN, univ_inter] using
    perimeterIn_eq_reducedBoundary_area E hE hmE isOpen_univ

/-- Gauss--Green for locally finite perimeter sets and compactly supported C¹ fields. -/
theorem gauss_green (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (X : AmbientSpace → AmbientSpace) (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ x in E, divergenceN X x) =
      ∫ x in reducedBoundary E hE hmE, inner ℝ (X x) (reducedNormal E hE hmE x)
        ∂hausdorffMeasure2 3 :=
  (reducedBoundary_outwardPerimeterPolar E hE hmE).divergence_eq X hX hcX

/-- The local distributional derivative on a compact restriction. Its density
has the derivative sign, the negative of the outward normal. -/
def perimeterDerivativeRestriction (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (K : Set AmbientSpace) : VectorMeasure AmbientSpace AmbientSpace :=
  polarVectorRestriction (canonicalPerimeterMeasure E hE hmE)
    (-canonicalOutwardPolarDensity E hE hmE) K

/-- The signed De Giorgi identity on each genuine compact vector restriction. -/
theorem perimeterDerivativeRestriction_eq_reducedBoundary_area (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (K : Set AmbientSpace) :
    perimeterDerivativeRestriction E hE hmE K =
      -(((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).restrict K).withDensityᵥ
        (reducedNormal E hE hmE) := by
  unfold perimeterDerivativeRestriction polarVectorRestriction
  rw [← MeasureTheory.withDensityᵥ_neg]
  have heq : -canonicalOutwardPolarDensity E hE hmE =ᵐ[
      (canonicalPerimeterMeasure E hE hmE).restrict K] -reducedNormal E hE hmE := by
    filter_upwards [ae_restrict_of_ae (reducedNormal_ae_eq_polarDensity E hE hmE)] with x hx
    simp only [Pi.neg_apply, hx]
  rw [WithDensityᵥEq.congr_ae heq, canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE]

/-- The derivative on a compact region has exactly the restricted perimeter as variation. -/
theorem variation_perimeterDerivativeRestriction (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {K : Set AmbientSpace} (hK : IsCompact K) :
    (perimeterDerivativeRestriction E hE hmE K).variation =
      ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).restrict K := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  rw [perimeterDerivativeRestriction, polarVectorRestriction,
    Measure.variation_withDensityᵥ (h.locallyIntegrable.integrableOn_isCompact hK).neg]
  have heq : (fun x => ‖(-canonicalOutwardPolarDensity E hE hmE) x‖ₑ) =ᵐ[
      (canonicalPerimeterMeasure E hE hmE).restrict K] 1 := by
    filter_upwards [ae_restrict_of_ae h.norm_ae] with x hx
    simp only [Pi.neg_apply, ← ofReal_norm, norm_neg, hx, ENNReal.ofReal_one, Pi.one_apply]
  rw [withDensity_congr_ae heq, withDensity_one,
    canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE]

/-- Compact derivative measures agree on nested compact regions. -/
theorem perimeterDerivativeRestriction_restrict (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {K L : Set AmbientSpace} (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    (perimeterDerivativeRestriction E hE hmE L).restrict K =
      perimeterDerivativeRestriction E hE hmE K := by
  have h := canonicalPerimeterPolar E hE hmE
  let := h.finiteOnCompacts
  ext A hA
  rw [VectorMeasure.restrict_apply _ hK.measurableSet hA,
    perimeterDerivativeRestriction, polarVectorRestriction,
    withDensityᵥ_apply (h.locallyIntegrable.integrableOn_isCompact hL).neg
      (hA.inter hK.measurableSet),
    perimeterDerivativeRestriction, polarVectorRestriction,
    withDensityᵥ_apply (h.locallyIntegrable.integrableOn_isCompact hK).neg hA,
    Measure.restrict_restrict (hA.inter hK.measurableSet), Measure.restrict_restrict hA]
  rw [inter_assoc, inter_eq_left.mpr hKL]

/-- Perimeter measure on every Borel set is reduced-boundary Hausdorff area. -/
theorem canonicalPerimeterMeasure_apply_eq_reducedBoundary_area (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {A : Set AmbientSpace} (hA : MeasurableSet A) :
    canonicalPerimeterMeasure E hE hmE A =
      hausdorffMeasure2 3 (A ∩ reducedBoundary E hE hmE) := by
  rw [canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE, Measure.restrict_apply hA]

/-- De Giorgi structure: rectifiability, exact area measure, and its outward
polar field, with the signed identity on all compact vector restrictions. -/
theorem degiorgi_structure (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    CountablyH2Rectifiable (reducedBoundary E hE hmE) ∧
    canonicalPerimeterMeasure E hE hmE =
      (hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE) ∧
    IsAmbientOutwardPerimeterPolar E
      ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)) (reducedNormal E hE hmE) ∧
    ∀ K, IsCompact K →
      perimeterDerivativeRestriction E hE hmE K =
        -(((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).restrict K).withDensityᵥ
          (reducedNormal E hE hmE) ∧
      (perimeterDerivativeRestriction E hE hmE K).variation =
        ((hausdorffMeasure2 3).restrict (reducedBoundary E hE hmE)).restrict K :=
  ⟨countablyH2Rectifiable_reducedBoundary E hE hmE,
    canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE,
    reducedBoundary_outwardPerimeterPolar E hE hmE, fun K hK =>
      ⟨perimeterDerivativeRestriction_eq_reducedBoundary_area E hE hmE K,
        variation_perimeterDerivativeRestriction E hE hmE hK⟩⟩

end LiquidDrop
