module

public import NoCompromise.BV.GraphTraces
public import NoCompromise.BV.FlatCutMeasure
public import NoCompromise.BV.ScalarC1Pairing
public import NoCompromise.Measure.PolarTransport

@[expose] public section

/-!
# Actual BV cuts on C¹ graph domains

The graph shear has determinant one and transforms the flat trace term into
its genuine upward surface normal. All bulk derivatives come from original
compact C¹ distributional pairings.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma c1GraphShear_eq_add {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Continuous g) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    c1GraphShear hg z = z + g (graphProjectionN n z) • EuclideanSpace.single (Fin.last n) 1 := by
  rw [c1GraphShear_apply]
  change graphBaseN n (graphProjectionN n z) +
    (z (Fin.last n) + g (graphProjectionN n z)) • EuclideanSpace.single (Fin.last n) 1 = _
  rw [add_smul, ← add_assoc]
  congr 1
  exact graphAppendN_projection z

lemma fderiv_c1GraphShear {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContDiff ℝ 1 g) (z v : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ (c1GraphShear hg.continuous) z v =
      v + fderiv ℝ g (graphProjectionN n z) (graphProjectionN n v) •
        EuclideanSpace.single (Fin.last n) 1 := by
  have he : (c1GraphShear hg.continuous : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) =
      fun z => z + g (graphProjectionN n z) • EuclideanSpace.single (Fin.last n) 1 :=
    funext (c1GraphShear_eq_add hg.continuous)
  rw [he]
  have hd := (hasFDerivAt_id z).add
    (((hg.differentiable one_ne_zero (graphProjectionN n z)).hasFDerivAt.comp z
      (graphProjectionN n).hasFDerivAt).smul_const (EuclideanSpace.single (Fin.last n) (1 : ℝ)))
  exact congrArg (fun L => L v) hd.fderiv

lemma standardMatrix3_fderiv_c1GraphShear {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hg : ContDiff ℝ 1 g) (z : AmbientSpace) :
    standardMatrix3 (fderiv ℝ (c1GraphShear hg.continuous) z) =
      !![1, 0, 0; 0, 1, 0;
        fderiv ℝ g (graphProjectionN 2 z) (EuclideanSpace.single 0 1),
        fderiv ℝ g (graphProjectionN 2 z) (EuclideanSpace.single 1 1), 1] := by
  have h0 : graphProjectionN 2 (EuclideanSpace.single 0 (1 : ℝ)) =
      EuclideanSpace.single 0 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [graphProjectionN_apply]
  have h1 : graphProjectionN 2 (EuclideanSpace.single 1 (1 : ℝ)) =
      EuclideanSpace.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [graphProjectionN_apply]
  have h2 : graphProjectionN 2 (EuclideanSpace.single 2 (1 : ℝ)) = 0 := by
    ext i
    fin_cases i <;> simp [graphProjectionN_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardMatrix3_apply, fderiv_c1GraphShear hg, h0, h1, h2]

lemma det_fderiv_c1GraphShear {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hg : ContDiff ℝ 1 g) (z : AmbientSpace) :
    (fderiv ℝ (c1GraphShear hg.continuous) z).det = 1 := by
  rw [← standardMatrix3_det, standardMatrix3_fderiv_c1GraphShear hg, Matrix.det_fin_three]
  simp

lemma cofactor_fderiv_c1GraphShear_last {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hg : ContDiff ℝ 1 g) (z : AmbientSpace) :
    cofactor3 (fderiv ℝ (c1GraphShear hg.continuous) z) (EuclideanSpace.single 2 1) =
      graphAppendN (-gradient g (graphProjectionN 2 z)) 1 := by
  have hm := standardMatrix3_cofactor3 (fderiv ℝ (c1GraphShear hg.continuous) z)
  rw [standardMatrix3_fderiv_c1GraphShear hg, Matrix.adjugate_fin_three] at hm
  apply PiLp.ext
  intro i
  have hi := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i 2) hm
  change cofactor3 (fderiv ℝ (c1GraphShear hg.continuous) z)
    (EuclideanSpace.single 2 1) i = _ at hi
  rw [hi]
  fin_cases i <;> simp [graphAppendN, graphBaseN, Fin.sum_univ_two,
    ← inner_gradient_left, EuclideanSpace.inner_single_right]

/-- A genuine C¹ subgraph cut preserves local BV, without boundedness of the graph. -/
theorem IsLocallyBVOn.indicator_smoothSubgraph {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) :
    IsLocallyBVOn ((smoothSubgraph g).indicator f) univ := by
  classical
  let P := c1GraphShear hg.continuous
  have hh := ((hf.comp_c1GraphShear hg).indicator_lowerHalfspace 0
    ).comp_C1_diffeomorphism P.symm (contDiff_c1GraphShear_symm hg) (contDiff_c1GraphShear hg)
  convert hh using 1
  funext z
  have hz : P.symm z (Fin.last n) < 0 ↔ z ∈ smoothSubgraph g := by
    simp [P, smoothSubgraph]
  by_cases h : z ∈ smoothSubgraph g
  · have hh : P.symm z ∈ {z | z (Fin.last n) < 0} := hz.mpr h
    simp only [Function.comp_def, Set.indicator_of_mem hh, Set.indicator_of_mem h]
    exact congrArg f (P.apply_symm_apply z).symm
  · simp [Function.comp_def, mt hz.mp h, h]

/-- The open upper C¹ graph cut is also locally BV. -/
theorem IsLocallyBVOn.indicator_smoothEpigraph {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 1 g) :
    IsLocallyBVOn ((smoothEpigraph g).indicator f) univ := by
  classical
  let P := c1GraphShear hg.continuous
  have hh := ((hf.comp_c1GraphShear hg).indicator_upperHalfspace 0
    ).comp_C1_diffeomorphism P.symm (contDiff_c1GraphShear_symm hg) (contDiff_c1GraphShear hg)
  convert hh using 1
  funext z
  have hz : 0 < P.symm z (Fin.last n) ↔ z ∈ smoothEpigraph g := by
    simp [P, smoothEpigraph, sub_pos]
  by_cases h : z ∈ smoothEpigraph g
  · have hh : P.symm z ∈ {z | 0 < z (Fin.last n)} := hz.mpr h
    simp only [Function.comp_def, Set.indicator_of_mem hh, Set.indicator_of_mem h]
    exact congrArg f (P.apply_symm_apply z).symm
  · simp [Function.comp_def, mt hz.mp h, h]

lemma integrable_cofactor_density_pairing
    {μ : Measure AmbientSpace} {σ : AmbientSpace → AmbientSpace}
    (hσ : LocallyIntegrable σ μ) (P : AmbientSpace ≃ₜ AmbientSpace)
    (hP : ContDiff ℝ 1 P) {X : AmbientSpace → AmbientSpace}
    (hX : Continuous X) (hcX : HasCompactSupport X) :
    Integrable (fun z => inner ℝ (X (P z)) (cofactor3 (fderiv ℝ P z) (σ z))) μ := by
  have hZ := continuous_piolaPullback hP hX
  have hcZ := hasCompactSupport_piolaPullback P hcX
  have hi := integrable_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) =>
    integrable_coordinate_density_pairing hσ hZ hcZ i)
  have he (z : AmbientSpace) : ∑ i : Fin 3, piolaPullback P X z i * σ z i =
      inner ℝ (X (P z)) (cofactor3 (fderiv ℝ P z) (σ z)) := by
    calc
      _ = inner ℝ (piolaPullback P X z) (σ z) := by
        simp only [PiLp.inner_apply, Real.inner_apply, mul_comm]
      _ = _ := (cofactor3 (fderiv ℝ P z)).adjoint_inner_left _ _
  simpa only [he] using! hi

lemma graphAppendN_neg_eq_sqrt_smul_normal (p : EuclideanSpace ℝ (Fin 2)) :
    graphAppendN (-p) 1 = Real.sqrt (1 + ‖p‖ ^ 2) • smoothGraphUnitNormal p := by
  rw [smoothGraphUnitNormal, smul_smul, mul_inv_cancel₀
    (ne_of_gt (Real.sqrt_pos.2 (by positivity))), one_smul]

/-- The graph cut identity, derived from the genuine derivative of the pulled-back
function. Its boundary term is the actual lower trace times the upward unit normal. -/
theorem IsLocallyBVOn.smoothSubgraph_cut_pairing
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ)
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ 1 g)
    {μ : Measure AmbientSpace} [SFinite μ] {σ : AmbientSpace → AmbientSpace}
    (hσ : LocallyIntegrable σ μ)
    (hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ → -(∫ z, f (c1GraphShear hg.continuous z) *
        fderiv ℝ φ z (EuclideanSpace.single i 1)) = ∫ z, φ z * σ z i ∂μ)
    {X : AmbientSpace → AmbientSpace} (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) :
    (∫ z in smoothSubgraph g, f z * divergenceN X z) =
      -(∫ z in {z : AmbientSpace | z 2 < 0}, inner ℝ (X (c1GraphShear hg.continuous z))
        (cofactor3 (fderiv ℝ (c1GraphShear hg.continuous) z) (σ z)) ∂μ) +
      ∫ z, graphBVLowerTrace f g z * inner ℝ (X z) (smoothSubgraphNormal g z)
        ∂smoothGraphArea g := by
  classical
  let P := c1GraphShear hg.continuous
  let u := f ∘ P
  have hu : IsLocallyBVOn u univ := hf.comp_c1GraphShear hg
  have hcut := hu.indicator_lowerHalfspace 0
  have hden := hu.locallyIntegrable_flatCutDensity hσ 0
  let : SFinite (flatCutMeasure μ 0) := by
    dsimp only [flatCutMeasure]
    infer_instance
  have hsgn (z : AmbientSpace) : |(fderiv ℝ P z).det| = 1 * (fderiv ℝ P z).det := by
    simp only [P, det_fderiv_c1GraphShear hg, abs_one, mul_one]
  have ht := scalar_distributional_transport_C1 (locallyIntegrableOn_univ.mp hcut.1)
    hden (fun i φ hφ => hu.flat_cut_distributional_pairing hσ hpair 0 i φ hφ)
    P (contDiff_c1GraphShear hg) (contDiff_c1GraphShear_symm hg) hX hcX hsgn
  simp only [one_smul] at ht
  have hleft : (∫ y, ({z : AmbientSpace | z (Fin.last 2) < 0}.indicator u) (P.symm y) *
      divergenceN X y) = ∫ y in smoothSubgraph g, f y * divergenceN X y := by
    rw [← integral_indicator (isOpen_smoothSubgraph hg.continuous).measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      have hh : P.symm y (Fin.last 2) < 0 ↔ y ∈ smoothSubgraph g := by
        dsimp only [P]
        rw [c1GraphShear_symm_apply, graphAppendN_last]
        exact sub_lt_zero
      by_cases hy : y ∈ smoothSubgraph g
      · have hH : P.symm y ∈ {z : AmbientSpace | z (Fin.last 2) < 0} := hh.mpr hy
        simp only [Set.indicator_of_mem hH, Set.indicator_of_mem hy]
        change f (P (P.symm y)) * divergenceN X y = _
        rw [P.apply_symm_apply]
      · have hH : P.symm y ∉ {z : AmbientSpace | z (Fin.last 2) < 0} := mt hh.mp hy
        simp only [Set.indicator_of_notMem hH, Set.indicator_of_notMem hy, zero_mul]
  rw [hleft] at ht
  have hi := integrable_cofactor_density_pairing hden P (contDiff_c1GraphShear hg)
    hX.continuous hcX
  have hib : Integrable (fun z => inner ℝ (X (P z))
      (cofactor3 (fderiv ℝ P z) (flatCutDensity σ u 0 z)))
      (μ.restrict {z | z (Fin.last 2) < 0}) := hi.mono_measure (Measure.le_add_right le_rfl)
  have his : Integrable (fun z => inner ℝ (X (P z))
      (cofactor3 (fderiv ℝ P z) (flatCutDensity σ u 0 z)))
      (flatHyperplaneMeasure 2 0) := hi.mono_measure (Measure.le_add_left le_rfl)
  have hb : (∫ z in {z : AmbientSpace | z (Fin.last 2) < 0}, inner ℝ (X (P z))
      (cofactor3 (fderiv ℝ P z) (flatCutDensity σ u 0 z)) ∂μ) =
      ∫ z in {z : AmbientSpace | z 2 < 0}, inner ℝ (X (P z))
        (cofactor3 (fderiv ℝ P z) (σ z)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [flatCutDensity_ae_bulk μ σ u 0] with z hz
    rw [hz]
  have hs : (∫ z, inner ℝ (X (P z))
      (cofactor3 (fderiv ℝ P z) (flatCutDensity σ u 0 z)) ∂flatHyperplaneMeasure 2 0) =
      -(∫ z, graphBVLowerTrace f g z * inner ℝ (X z) (smoothSubgraphNormal g z)
        ∂smoothGraphArea g) := by
    rw [integral_congr_ae (show
      (fun z => inner ℝ (X (P z)) (cofactor3 (fderiv ℝ P z) (flatCutDensity σ u 0 z))) =ᵐ[
        flatHyperplaneMeasure 2 0]
      (fun z => inner ℝ (X (P z)) (cofactor3 (fderiv ℝ P z) (flatCutSurfaceDensity u 0 z)))
      from (flatCutDensity_ae_surface σ u 0).mono fun z hz => by
        dsimp only
        rw [hz])]
    rw [flatHyperplaneMeasure,
      (isClosedEmbedding_graphAppendN 2 0).measurableEmbedding.integral_map,
      integral_smoothGraphArea hg, ← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp only [flatCutSurfaceDensity, graphProjectionN_append, map_smul, inner_smul_right]
      change -flatBVLeftTrace u 0 x * inner ℝ (X (P (graphAppendN x 0)))
        (cofactor3 (fderiv ℝ P (graphAppendN x 0)) (EuclideanSpace.single 2 1)) = _
      rw [cofactor_fderiv_c1GraphShear_last hg, graphProjectionN_append,
        graphAppendN_neg_eq_sqrt_smul_normal, inner_smul_right]
      have hP : P (graphAppendN x 0) = graphMapN g x := by
        simp only [P, c1GraphShear_apply, graphProjectionN_append, graphAppendN_last, zero_add]
        rfl
      have hproj : graphProjectionN 2 (graphMapN g x) = x := graphProjectionN_append x (g x)
      rw [hP, graphBVLowerTrace_graphMap f hg.continuous]
      simp only [smoothSubgraphNormal, hproj]
      change -flatBVLeftTrace u 0 x *
        (Real.sqrt (1 + ‖gradient g x‖ ^ 2) * inner ℝ (X (graphMapN g x))
          (smoothGraphUnitNormal (gradient g x))) =
        -(Real.sqrt (1 + ‖gradient g x‖ ^ 2) * (flatBVLeftTrace u 0 x *
          inner ℝ (X (graphMapN g x)) (smoothGraphUnitNormal (gradient g x))))
      ring
  rw [flatCutMeasure, integral_add_measure hib his, hb, hs] at ht
  exact ht.trans (by ring)

/-- Actual simultaneous derivative and cut representations, obtained solely
from local BV and a C¹ graph. The first pairing identifies the bulk derivative
of `f`; the second restricts that same derivative and adds its constructed trace. -/
theorem IsLocallyBVOn.exists_smoothSubgraph_cut_representation
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ)
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ 1 g) :
    ∃ μ : Measure AmbientSpace, ∃ σ : AmbientSpace → AmbientSpace,
      μ.Regular ∧ IsFiniteMeasureOnCompacts μ ∧ LocallyIntegrable σ μ ∧
      (∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
        (∫ z, f z * divergenceN X z) =
          -∫ z, inner ℝ (X (c1GraphShear hg.continuous z))
            (cofactor3 (fderiv ℝ (c1GraphShear hg.continuous) z) (σ z)) ∂μ) ∧
      (∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
        (∫ z in smoothSubgraph g, f z * divergenceN X z) =
          -(∫ z in {z : AmbientSpace | z 2 < 0}, inner ℝ (X (c1GraphShear hg.continuous z))
            (cofactor3 (fderiv ℝ (c1GraphShear hg.continuous) z) (σ z)) ∂μ) +
          ∫ z, graphBVLowerTrace f g z * inner ℝ (X z) (smoothSubgraphNormal g z)
            ∂smoothGraphArea g) := by
  let P := c1GraphShear hg.continuous
  have hu : IsLocallyBVOn (f ∘ P) univ := hf.comp_c1GraphShear hg
  obtain ⟨μ, σ, hμ, hμfin, _, _, hσ, hp, _⟩ := hu.exists_ambient_scalar_polar
  let : μ.Regular := hμ
  let : IsFiniteMeasureOnCompacts μ := hμfin
  refine ⟨μ, σ, hμ, hμfin, hσ, ?_, fun X hX hcX =>
    hf.smoothSubgraph_cut_pairing hg hσ hp hX hcX⟩
  intro X hX hcX
  have hsgn (z : AmbientSpace) : |(fderiv ℝ P z).det| = 1 * (fderiv ℝ P z).det := by
    simp only [P, det_fderiv_c1GraphShear hg, abs_one, mul_one]
  have ht := scalar_distributional_transport_C1 (locallyIntegrableOn_univ.mp hu.1) hσ hp
    P (contDiff_c1GraphShear hg) (contDiff_c1GraphShear_symm hg) hX hcX hsgn
  simpa only [Function.comp_def, P.apply_symm_apply, one_smul] using ht

lemma setIntegral_inner_transportedUnitPolar (P : AmbientSpace ≃ₜ AmbientSpace)
    (μ : Measure AmbientSpace) {w : AmbientSpace → AmbientSpace} (hw : Measurable w)
    {A : Set AmbientSpace} (hA : MeasurableSet A) (X : AmbientSpace → AmbientSpace) :
    (∫ z in A, inner ℝ (X z) (transportedUnitPolar P w z) ∂transportedPolarMeasure P μ w) =
      ∫ z in P ⁻¹' A, inner ℝ (X (P z)) (w z) ∂μ := by
  classical
  have ht := integral_inner_transportedUnitPolar P μ hw (A.indicator X)
  have hl : (fun z => inner ℝ (A.indicator X z) (transportedUnitPolar P w z)) =
      A.indicator (fun z => inner ℝ (X z) (transportedUnitPolar P w z)) := by
    funext z
    by_cases hz : z ∈ A <;> simp [hz]
  have hr : (fun z => inner ℝ (A.indicator X (P z)) (w z)) =
      (P ⁻¹' A).indicator (fun z => inner ℝ (X (P z)) (w z)) := by
    funext z
    by_cases hz : P z ∈ A <;> simp [hz]
  rw [hl, hr, integral_indicator hA, integral_indicator (hA.preimage P.continuous.measurable)] at ht
  exact ht

/-- The graph cut formula with the original derivative and its restriction
represented in ambient coordinates by one regular measure and unit polar.
No derivative, trace, or extension formula is included among the assumptions. -/
theorem IsLocallyBVOn.exists_ambient_smoothSubgraph_cut_representation
    {f : AmbientSpace → ℝ} (hf : IsLocallyBVOn f univ)
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg : ContDiff ℝ 1 g) :
    ∃ μ : Measure AmbientSpace, ∃ σ : AmbientSpace → AmbientSpace,
      μ.Regular ∧ IsFiniteMeasureOnCompacts μ ∧ Measurable σ ∧
      (∀ᵐ z ∂μ, ‖σ z‖ = 1) ∧ LocallyIntegrable σ μ ∧
      (∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
        (∫ z, f z * divergenceN X z) = -∫ z, inner ℝ (X z) (σ z) ∂μ) ∧
      (∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
        (∫ z in smoothSubgraph g, f z * divergenceN X z) =
          -(∫ z in smoothSubgraph g, inner ℝ (X z) (σ z) ∂μ) +
          ∫ z, graphBVLowerTrace f g z * inner ℝ (X z) (smoothSubgraphNormal g z)
            ∂smoothGraphArea g) := by
  let P := c1GraphShear hg.continuous
  have hu : IsLocallyBVOn (f ∘ P) univ := hf.comp_c1GraphShear hg
  obtain ⟨μ, σ, hμ, hμfin, hmσ, hnσ, hσ, hp, _⟩ := hu.exists_ambient_scalar_polar
  let : μ.Regular := hμ
  let : IsFiniteMeasureOnCompacts μ := hμfin
  let w : AmbientSpace → AmbientSpace := fun z => cofactor3 (fderiv ℝ P z) (σ z)
  have hC : Continuous (fun z => cofactor3 (fderiv ℝ P z)) :=
    continuous_cofactor3.comp ((contDiff_c1GraphShear hg).continuous_fderiv one_ne_zero)
  have hmw : Measurable w := by
    have ha : Continuous (fun p : (AmbientSpace →L[ℝ] AmbientSpace) × AmbientSpace => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    exact ha.measurable.comp (hC.measurable.prodMk hmσ)
  have hw : LocallyIntegrable w μ := locallyIntegrable_continuous_linear_apply_unit μ hC hmσ hnσ
  let ν := transportedPolarMeasure P μ w
  let τ := transportedUnitPolar P w
  let : ν.Regular := transportedPolarMeasure_regular P μ hw
  have hmτ : Measurable τ := measurable_transportedUnitPolar P hmw
  have hnτ : ∀ᵐ z ∂ν, ‖τ z‖ = 1 := norm_transportedUnitPolar_ae P μ hmw
  have hiτ : LocallyIntegrable τ ν :=
    locallyIntegrable_of_ae_norm_le ν hmτ.aestronglyMeasurable (hnτ.mono fun _ hx => hx.le)
  refine ⟨ν, τ, inferInstance, inferInstance, hmτ, hnτ, hiτ, ?_, ?_⟩
  · intro X hX hcX
    have hsgn (z : AmbientSpace) : |(fderiv ℝ P z).det| = 1 * (fderiv ℝ P z).det := by
      simp only [P, det_fderiv_c1GraphShear hg, abs_one, mul_one]
    have ht := scalar_distributional_transport_C1 (locallyIntegrableOn_univ.mp hu.1) hσ hp
      P (contDiff_c1GraphShear hg) (contDiff_c1GraphShear_symm hg) hX hcX hsgn
    rw [integral_inner_transportedUnitPolar P μ hmw]
    simpa only [Function.comp_def, P.apply_symm_apply, one_smul] using ht
  · intro X hX hcX
    rw [setIntegral_inner_transportedUnitPolar P μ hmw
      (isOpen_smoothSubgraph hg.continuous).measurableSet,
      show P ⁻¹' smoothSubgraph g = {z : AmbientSpace | z 2 < 0} from
        c1GraphShear_preimage_subgraph hg.continuous]
    exact hf.smoothSubgraph_cut_pairing hg hσ hp hX hcX

end LiquidDrop
