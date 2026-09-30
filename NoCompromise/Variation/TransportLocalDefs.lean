module

public import NoCompromise.DeGiorgi.Reduced
public import NoCompromise.BV.CompactnessIndicators
public import NoCompromise.BV.ScalarDistributionUniqueness

@[expose] public section

/-!
# Local reduced boundary on an open domain

For `E` with locally finite perimeter only inside an open set `U`, the blueprint's
`def:reduced-boundary` is applied verbatim to the polar decomposition of `D1_E` on `U`:
the chosen polar measure on the subtype `U` is pushed to the ambient space, and the
derivative density is extended by zero. The outward normal is the negative density
limit. Locality: on an open `O ⊆ U` where `E` agrees with a set `E'` of globally locally
finite perimeter, the local measure, reduced boundary and normal coincide with the
canonical ones of `E'`.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- The chosen local polar data of `D1_E` on `U`. -/
theorem exists_localPerimeterPolar (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    ∃ ρ : Measure U, ∃ σ : U → AmbientSpace,
      ρ.Regular ∧ IsDistributionalPolarRepresentation (E.indicator (fun _ => (1 : ℝ))) U ρ σ ∧
      ∀ O, IsOpen O → O ⊆ U → variation (E.indicator (fun _ => (1 : ℝ))) O =
        ρ (Subtype.val ⁻¹' O) :=
  exists_polar_representation_with_variation hU (hE.isLocallyBVOn_indicator hmE)

/-- The chosen polar measure `|D1_E|` on the subtype `U`. -/
def localPolarMeasure (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) : Measure U :=
  (exists_localPerimeterPolar E U hU hE hmE).choose

/-- The chosen polar derivative density on the subtype `U` (`D1_E = σ |D1_E|`). -/
def localPolarDensity (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    U → AmbientSpace :=
  (exists_localPerimeterPolar E U hU hE hmE).choose_spec.choose

theorem localPolar_spec (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    (localPolarMeasure E U hU hE hmE).Regular ∧
      IsDistributionalPolarRepresentation (E.indicator (fun _ => (1 : ℝ))) U
        (localPolarMeasure E U hU hE hmE) (localPolarDensity E U hU hE hmE) ∧
      ∀ O, IsOpen O → O ⊆ U → variation (E.indicator (fun _ => (1 : ℝ))) O =
        localPolarMeasure E U hU hE hmE (Subtype.val ⁻¹' O) :=
  (exists_localPerimeterPolar E U hU hE hmE).choose_spec.choose_spec

/-- The local perimeter measure `|D1_E|` on `U`, as an ambient measure. -/
def localPerimeterMeasureAmbient (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    Measure AmbientSpace :=
  Measure.map Subtype.val (localPolarMeasure E U hU hE hmE)

open Classical in
/-- The local derivative density, extended by zero outside `U`. -/
def localDerivativeDensity (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    AmbientSpace → AmbientSpace :=
  fun x => if h : x ∈ U then localPolarDensity E U hU hE hmE ⟨x, h⟩ else 0

/-- Blueprint `def:reduced-boundary` for `μ_E = |D1_E|` on `U`. -/
def localReducedBoundary (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    Set AmbientSpace :=
  U ∩ reducedBoundaryOfPolar (localPerimeterMeasureAmbient E U hU hE hmE)
    (localDerivativeDensity E U hU hE hmE)

/-- The outward normal on the local reduced boundary (negative density limit). -/
def localReducedNormal (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    AmbientSpace → AmbientSpace :=
  reducedNormalOfPolar (localPerimeterMeasureAmbient E U hU hE hmE)
    (localDerivativeDensity E U hU hE hmE)

/-- On open subsets of `U` the local perimeter measure is the perimeter. -/
theorem localPerimeterMeasureAmbient_open (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume)
    {O : Set AmbientSpace} (hO : IsOpen O) (hOU : O ⊆ U) :
    localPerimeterMeasureAmbient E U hU hE hmE O = perimeterIn E O := by
  rw [localPerimeterMeasureAmbient, Measure.map_apply measurable_subtype_coe hO.measurableSet]
  exact ((localPolar_spec E U hU hE hmE).2.2 O hO hOU).symm

theorem localPerimeterMeasureAmbient_compl (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    localPerimeterMeasureAmbient E U hU hE hmE Uᶜ = 0 := by
  rw [localPerimeterMeasureAmbient, Measure.map_apply measurable_subtype_coe
    hU.measurableSet.compl]
  simp

/-- Countable cover of an open set by balls with a prescribed local property. -/
theorem exists_countable_ball_cover {O : Set AmbientSpace} (P : AmbientSpace → ℝ → Prop)
    (hP : ∀ x ∈ O, ∃ r > 0, ball x r ⊆ O ∧ P x r) :
    ∃ T : Set O, T.Countable ∧ ∃ r : O → ℝ,
      (∀ x, 0 < r x ∧ ball (x : AmbientSpace) (r x) ⊆ O ∧ P x (r x)) ∧
      ⋃ x ∈ T, ball (x : AmbientSpace) (r x) = O := by
  choose r hr hPr using fun x : O => hP x x.2
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : O => ball (x : AmbientSpace) (r x)) (fun _ => isOpen_ball)
  refine ⟨T, hT, r, fun x => ⟨hr x, hPr x⟩, ?_⟩
  rw [hTU]
  apply Subset.antisymm
  · exact iUnion_subset fun x => (hPr x).1
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩

/-- Two measures agreeing on all open subsets of an open `O`, the first finite on
relatively compact open subsets of `O`, have the same restriction to `O`. -/
theorem restrict_eq_of_forall_isOpen_eq {μ₁ μ₂ : Measure AmbientSpace} {O : Set AmbientSpace}
    (hO : IsOpen O)
    (hfin : ∀ W, IsOpen W → IsCompact (closure W) → closure W ⊆ O → μ₁ W < ∞)
    (heq : ∀ W, IsOpen W → W ⊆ O → μ₁ W = μ₂ W) : μ₁.restrict O = μ₂.restrict O := by
  obtain ⟨T, hT, r, hr, hcov⟩ := exists_countable_ball_cover
    (O := O) (fun x r => closedBall x r ⊆ O) (by
      intro x hx
      obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO x hx
      refine ⟨ε / 2, by positivity, (ball_subset_ball (by linarith)).trans hεO,
        (closedBall_subset_ball (by linarith)).trans hεO⟩)
  rw [← hcov]
  refine (Measure.restrict_biUnion_congr hT).mpr fun x _ => ?_
  have hB : IsOpen (ball (x : AmbientSpace) (r x)) := isOpen_ball
  have hcl : closure (ball (x : AmbientSpace) (r x)) ⊆ closedBall x (r x) :=
    closure_ball_subset_closedBall
  have hK : IsCompact (closure (ball (x : AmbientSpace) (r x))) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hcl
  have : IsFiniteMeasure (μ₁.restrict (ball (x : AmbientSpace) (r x))) :=
    isFiniteMeasure_restrict.mpr (hfin _ hB hK (hcl.trans (hr x).2.2)).ne
  apply ext_of_generate_finite _ (BorelSpace.measurable_eq.trans rfl) isPiSystem_isOpen
  · intro S hS
    rw [Measure.restrict_apply' hB.measurableSet, Measure.restrict_apply' hB.measurableSet]
    exact heq _ ((show IsOpen S from hS).inter hB) (inter_subset_right.trans (hr x).2.1)
  · rw [Measure.restrict_apply' hB.measurableSet, Measure.restrict_apply' hB.measurableSet,
      univ_inter]
    exact heq _ hB (hr x).2.1

/-- Locality of the local perimeter measure: on an open `O ⊆ U` where `E` agrees with a
set `E'` of globally locally finite perimeter, it equals the canonical measure of `E'`. -/
theorem localPerimeterMeasureAmbient_restrict_eq_of_inter_eq (E U : Set AmbientSpace)
    (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume)
    {E' : Set AmbientSpace} (hE' : HasLocallyFinitePerimeter E')
    (hmE' : NullMeasurableSet E' volume) {O : Set AmbientSpace} (hO : IsOpen O) (hOU : O ⊆ U)
    (hEE' : E ∩ O = E' ∩ O) :
    (localPerimeterMeasureAmbient E U hU hE hmE).restrict O =
      (canonicalPerimeterMeasure E' hE' hmE').restrict O := by
  apply restrict_eq_of_forall_isOpen_eq hO
  · intro W hW hcW hWO
    rw [localPerimeterMeasureAmbient_open E U hU hE hmE hW ((subset_closure.trans hWO).trans hOU)]
    exact hE W hW hcW (hWO.trans hOU)
  · intro W hW hWO
    rw [localPerimeterMeasureAmbient_open E U hU hE hmE hW (hWO.trans hOU),
      canonicalPerimeterMeasure_open E' hE' hmE' hW]
    apply perimeterIn_congr_ae
    refine (ae_restrict_iff' hW.measurableSet).mpr (Eventually.of_forall fun x hx => ?_)
    exact propext ⟨fun h => (hEE'.subset ⟨h, hWO hx⟩).1,
      fun h => (hEE'.symm.subset ⟨h, hWO hx⟩).1⟩

theorem measurable_localDerivativeDensity (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    Measurable (localDerivativeDensity E U hU hE hmE) := by
  classical
  exact Measurable.dite (localPolar_spec E U hU hE hmE).2.1.measurable measurable_const
    hU.measurableSet

theorem localDerivativeDensity_norm_ae (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    ∀ᵐ x ∂localPerimeterMeasureAmbient E U hU hE hmE,
      ‖localDerivativeDensity E U hU hE hmE x‖ = 1 := by
  rw [localPerimeterMeasureAmbient, (MeasurableEmbedding.subtype_coe hU.measurableSet).ae_map_iff]
  filter_upwards [(localPolar_spec E U hU hE hmE).2.1.norm_ae] with x hx
  simpa [localDerivativeDensity, x.2] using hx

/-- Locality of the derivative density: on an open `O ⊆ U` where `E` agrees with `E'`,
the local derivative density agrees with the canonical derivative density of `E'`
almost everywhere for the local perimeter measure. -/
theorem localDerivativeDensity_ae_eq_of_inter_eq (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume)
    {E' : Set AmbientSpace} (hE' : HasLocallyFinitePerimeter E')
    (hmE' : NullMeasurableSet E' volume) {O : Set AmbientSpace} (hO : IsOpen O) (hOU : O ⊆ U)
    (hEE' : E ∩ O = E' ∩ O) :
    localDerivativeDensity E U hU hE hmE =ᵐ[(localPerimeterMeasureAmbient E U hU hE hmE).restrict O]
      -canonicalOutwardPolarDensity E' hE' hmE' := by
  obtain ⟨T, hT, r, hr, hcov⟩ := exists_countable_ball_cover
    (O := O) (fun x r => closedBall x r ⊆ O) (by
      intro x hx
      obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO x hx
      refine ⟨ε / 2, by positivity, (ball_subset_ball (by linarith)).trans hεO,
        (closedBall_subset_ball (by linarith)).trans hεO⟩)
  rw [← hcov]
  refine (ae_restrict_biUnion_iff _ hT _).mpr fun x _ => ?_
  have hBO : ball (x : AmbientSpace) (r x) ⊆ O := (hr x).2.1
  have hBU := hBO.trans hOU
  have hmeas :
      (localPerimeterMeasureAmbient E U hU hE hmE).restrict (ball (x : AmbientSpace) (r x)) =
      (canonicalPerimeterMeasure E' hE' hmE').restrict (ball (x : AmbientSpace) (r x)) := by
    have h := localPerimeterMeasureAmbient_restrict_eq_of_inter_eq E U hU hE hmE hE' hmE'
      hO hOU hEE'
    rw [← Measure.restrict_restrict_of_subset hBO, h, Measure.restrict_restrict_of_subset hBO]
  have hpolar := (localPolar_spec E U hU hE hmE).2.1
  have hcan := canonicalPerimeterPolar E' hE' hmE'
  have : IsFiniteMeasure
      ((canonicalPerimeterMeasure E' hE' hmE').restrict (ball (x : AmbientSpace) (r x))) := by
    let := hcan.finiteOnCompacts
    exact isFiniteMeasure_restrict.mpr ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall _ _).measure_lt_top).ne
  have hσ : LocallyIntegrable (localDerivativeDensity E U hU hE hmE)
      ((canonicalPerimeterMeasure E' hE' hmE').restrict (ball (x : AmbientSpace) (r x))) := by
    refine (Integrable.of_bound
      (measurable_localDerivativeDensity E U hU hE hmE).aestronglyMeasurable 1 ?_).locallyIntegrable
    rw [← hmeas]
    exact ae_restrict_of_ae ((localDerivativeDensity_norm_ae E U hU hE hmE).mono
      fun _ hx => hx.le)
  have hν : LocallyIntegrable (-canonicalOutwardPolarDensity E' hE' hmE')
      ((canonicalPerimeterMeasure E' hE' hmE').restrict (ball (x : AmbientSpace) (r x))) := by
    refine (Integrable.of_bound hcan.measurable.neg.aestronglyMeasurable 1 ?_).locallyIntegrable
    exact ae_restrict_of_ae (hcan.norm_ae.mono fun _ hx => by simp [hx])
  have hmain := ae_eq_density_on_of_coordinate_pairings (U := ball (x : AmbientSpace) (r x))
    isOpen_ball hσ hν ?_
  · rw [Measure.restrict_restrict_of_subset subset_rfl] at hmain
    rw [hmeas]
    exact hmain
  intro i φ hφ hsφ
  have hzero : ∀ y, y ∉ tsupport φ → φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hdzero : ∀ y, y ∉ tsupport φ → fderiv ℝ φ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (tsupport_fderiv_subset ℝ h))
  conv_lhs => rw [← hmeas]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [hzero y (fun h => hy (hsφ h)), zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [hzero y (fun h => hy (hsφ h)), zero_mul])]
  have hL : (∫ y, φ y * localDerivativeDensity E U hU hE hmE y i
      ∂localPerimeterMeasureAmbient E U hU hE hmE) =
      -(∫ y in U, E.indicator (fun _ => (1 : ℝ)) y *
        fderiv ℝ φ y (EuclideanSpace.single i 1)) := by
    rw [hpolar.test_eq i φ hφ (hsφ.trans hBU), localPerimeterMeasureAmbient,
      (MeasurableEmbedding.subtype_coe hU.measurableSet).integral_map]
    congr 1
    funext y
    simp [localDerivativeDensity, y.2]
  have hR : (∫ y, φ y * (-canonicalOutwardPolarDensity E' hE' hmE') y i
      ∂canonicalPerimeterMeasure E' hE' hmE') =
      -(∫ y, E'.indicator (fun _ => (1 : ℝ)) y *
        fderiv ℝ φ y (EuclideanSpace.single i 1)) := by
    rw [hcan.coordinate_eq i φ hφ]
    simp
  rw [hL, hR, setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [hdzero y (fun h => hy (hsφ.trans hBU h))]; simp)]
  congr 1
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  by_cases hy : y ∈ tsupport φ
  · have hyO : y ∈ O := hBO (hsφ hy)
    have hiff : y ∈ E ↔ y ∈ E' := ⟨fun h => (hEE'.subset ⟨h, hyO⟩).1,
      fun h => (hEE'.symm.subset ⟨h, hyO⟩).1⟩
    by_cases hyE : y ∈ E
    · simp [hyE, hiff.mp hyE]
    · simp [hyE, mt hiff.mpr hyE]
  · simp [hdzero y hy]

section Locality

variable {μ₁ μ₂ : Measure AmbientSpace} {σ₁ σ₂ : AmbientSpace → AmbientSpace}
  {O : Set AmbientSpace} {x : AmbientSpace}

/-- Membership in the support is local. -/
theorem mem_support_iff_of_restrict_eq (hO : IsOpen O) (h : μ₁.restrict O = μ₂.restrict O)
    (hx : x ∈ O) : x ∈ μ₁.support ↔ x ∈ μ₂.support := by
  have key : ∀ {ν₁ ν₂ : Measure AmbientSpace}, ν₁.restrict O = ν₂.restrict O →
      x ∈ ν₁.support → x ∈ ν₂.support := by
    intro ν₁ ν₂ h hx1
    rw [Measure.mem_support_iff_forall] at hx1 ⊢
    intro V hV
    calc 0 < ν₁ (V ∩ O) := hx1 (V ∩ O) (inter_mem hV (hO.mem_nhds hx))
      _ = ν₁.restrict O V := (Measure.restrict_apply' hO.measurableSet).symm
      _ = ν₂.restrict O V := by rw [h]
      _ ≤ ν₂ V := Measure.restrict_apply_le _ _
  exact ⟨key h, key h.symm⟩

/-- Small ball averages only see the measure and density on an open neighbourhood. -/
theorem average_ball_eventuallyEq_of_restrict_eq (hO : IsOpen O)
    (h : μ₁.restrict O = μ₂.restrict O) (hσ : σ₁ =ᵐ[μ₁.restrict O] σ₂) (hx : x ∈ O) :
    ∀ᶠ r in 𝓝 (0 : ℝ), (⨍ y in ball x r, σ₁ y ∂μ₁) = ⨍ y in ball x r, σ₂ y ∂μ₂ := by
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO x hx
  filter_upwards [eventually_lt_nhds hε] with r hr
  have hsub : ball x r ⊆ O := (ball_subset_ball hr.le).trans hεO
  have hB : μ₁.restrict (ball x r) = μ₂.restrict (ball x r) := by
    rw [← Measure.restrict_restrict_of_subset hsub, h, Measure.restrict_restrict_of_subset hsub]
  have hσB : σ₁ =ᵐ[μ₁.restrict (ball x r)] σ₂ := by
    rw [← Measure.restrict_restrict_of_subset hsub]
    exact ae_restrict_of_ae hσ
  rw [average_congr hσB, hB]

/-- The reduced boundary of a polar pair is local. -/
theorem mem_reducedBoundaryOfPolar_iff_of_restrict_eq (hO : IsOpen O)
    (h : μ₁.restrict O = μ₂.restrict O) (hσ : σ₁ =ᵐ[μ₁.restrict O] σ₂) (hx : x ∈ O) :
    x ∈ reducedBoundaryOfPolar μ₁ σ₁ ↔ x ∈ reducedBoundaryOfPolar μ₂ σ₂ := by
  have hev := (average_ball_eventuallyEq_of_restrict_eq hO h hσ hx).filter_mono
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [reducedBoundaryOfPolar, mem_inter_iff, mem_ofPred_eq,
    mem_support_iff_of_restrict_eq hO h hx]
  exact and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ =>
    tendsto_congr' hev

/-- The reduced normal of a polar pair is local. -/
theorem reducedNormalOfPolar_eq_of_restrict_eq (hO : IsOpen O)
    (h : μ₁.restrict O = μ₂.restrict O) (hσ : σ₁ =ᵐ[μ₁.restrict O] σ₂) (hx : x ∈ O) :
    reducedNormalOfPolar μ₁ σ₁ x = reducedNormalOfPolar μ₂ σ₂ x := by
  have hev := ((average_ball_eventuallyEq_of_restrict_eq hO h hσ hx).filter_mono
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).comap (fun q : ℚ => (q : ℝ))
  unfold reducedNormalOfPolar limUnder
  rw [Filter.map_congr hev]

end Locality

/-- Locality of the local reduced boundary. -/
theorem localReducedBoundary_inter_eq_of_inter_eq (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume)
    {E' : Set AmbientSpace} (hE' : HasLocallyFinitePerimeter E')
    (hmE' : NullMeasurableSet E' volume) {O : Set AmbientSpace} (hO : IsOpen O) (hOU : O ⊆ U)
    (hEE' : E ∩ O = E' ∩ O) :
    O ∩ localReducedBoundary E U hU hE hmE = O ∩ reducedBoundary E' hE' hmE' := by
  ext x
  simp only [mem_inter_iff, localReducedBoundary, reducedBoundary]
  constructor
  · rintro ⟨hx, -, hx'⟩
    exact ⟨hx, (mem_reducedBoundaryOfPolar_iff_of_restrict_eq hO
      (localPerimeterMeasureAmbient_restrict_eq_of_inter_eq E U hU hE hmE hE' hmE' hO hOU hEE')
      (localDerivativeDensity_ae_eq_of_inter_eq E U hU hE hmE hE' hmE' hO hOU hEE') hx).mp hx'⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨hx, hOU hx, (mem_reducedBoundaryOfPolar_iff_of_restrict_eq hO
      (localPerimeterMeasureAmbient_restrict_eq_of_inter_eq E U hU hE hmE hE' hmE' hO hOU hEE')
      (localDerivativeDensity_ae_eq_of_inter_eq E U hU hE hmE hE' hmE' hO hOU hEE') hx).mpr hx'⟩

/-- Locality of the local reduced normal. -/
theorem localReducedNormal_eq_of_inter_eq (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume)
    {E' : Set AmbientSpace} (hE' : HasLocallyFinitePerimeter E')
    (hmE' : NullMeasurableSet E' volume) {O : Set AmbientSpace} (hO : IsOpen O) (hOU : O ⊆ U)
    (hEE' : E ∩ O = E' ∩ O) {x : AmbientSpace} (hx : x ∈ O) :
    localReducedNormal E U hU hE hmE x = reducedNormal E' hE' hmE' x :=
  reducedNormalOfPolar_eq_of_restrict_eq hO
    (localPerimeterMeasureAmbient_restrict_eq_of_inter_eq E U hU hE hmE hE' hmE' hO hOU hEE')
    (localDerivativeDensity_ae_eq_of_inter_eq E U hU hE hmE hE' hmE' hO hOU hEE') hx

theorem localPerimeterMeasureAmbient_restrict_self (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume) :
    (localPerimeterMeasureAmbient E U hU hE hmE).restrict U =
      localPerimeterMeasureAmbient E U hU hE hmE :=
  Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (localPerimeterMeasureAmbient_compl E U hU hE hmE))

/-- Consistency with the global canonical objects when `E` has globally locally finite
perimeter. -/
theorem localPerimeterMeasureAmbient_eq_canonical_restrict (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume)
    (hE' : HasLocallyFinitePerimeter E) :
    localPerimeterMeasureAmbient E U hU hE hmE =
      (canonicalPerimeterMeasure E hE' hmE).restrict U := by
  rw [← localPerimeterMeasureAmbient_restrict_self E U hU hE hmE]
  exact localPerimeterMeasureAmbient_restrict_eq_of_inter_eq E U hU hE hmE hE' hmE hU subset_rfl rfl

theorem localReducedBoundary_eq_inter_reducedBoundary (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume)
    (hE' : HasLocallyFinitePerimeter E) :
    localReducedBoundary E U hU hE hmE = U ∩ reducedBoundary E hE' hmE := by
  rw [← localReducedBoundary_inter_eq_of_inter_eq E U hU hE hmE hE' hmE hU subset_rfl rfl,
    localReducedBoundary, ← inter_assoc, inter_self]

theorem localReducedNormal_eq_reducedNormal (E U : Set AmbientSpace) (hU : IsOpen U)
    (hE : HasLocallyFinitePerimeterIn E U) (hmE : NullMeasurableSet E volume)
    (hE' : HasLocallyFinitePerimeter E) :
    ∀ x ∈ U, localReducedNormal E U hU hE hmE x = reducedNormal E hE' hmE x :=
  fun _ hx => localReducedNormal_eq_of_inter_eq E U hU hE hmE hE' hmE hU subset_rfl rfl hx

end LiquidDrop
