module

public import NoCompromise.BV.GoodRadii
public import NoCompromise.DeGiorgi.AmbientPolar

@[expose] public section

/-!
# Exact cuts at good radii

The genuine trace product formula gives a unit polar supported on disjoint
bulk and spherical parts. Its mass therefore computes the exact perimeter,
including when the exterior perimeter is infinite.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Unit normal densities on disjoint bulk and surface measures give their
exact sum as perimeter, directly from the original divergence pairing. -/
lemma perimeterIn_eq_of_disjoint_divergence_pairing
    {F D : Set AmbientSpace} (hmF : NullMeasurableSet F volume) (hD : MeasurableSet D)
    {μ ρ : Measure AmbientSpace} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ρ]
    {ν η : AmbientSpace → AmbientSpace} (hν : Measurable ν) (hη : Measurable η)
    (hnν : ∀ᵐ x ∂μ.restrict D, ‖ν x‖ = 1) (hnη : ∀ᵐ x ∂ρ, ‖η x‖ = 1)
    (hρD : ρ D = 0)
    (hpair : ∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
      (∫ x in F, divergenceN X x) =
        (∫ x in D, inner ℝ (X x) (ν x) ∂μ) + ∫ x, inner ℝ (X x) (η x) ∂ρ)
    {U : Set AmbientSpace} (hU : IsOpen U) :
    perimeterIn F U = (μ.restrict D + ρ) U := by
  classical
  let : IsFiniteMeasureOnCompacts (μ.restrict D + ρ) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  let N : AmbientSpace → AmbientSpace := fun x => if x ∈ D then ν x else η x
  have hNm : Measurable N := Measurable.ite hD hν hη
  have hNb : N =ᵐ[μ.restrict D] ν := by
    filter_upwards [ae_restrict_mem hD] with x hx
    exact ite_eq_left hx
  have hNs : N =ᵐ[ρ] η := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hρD] with x hx
    exact ite_eq_right hx
  have hn : ∀ᵐ x ∂(μ.restrict D + ρ), ‖N x‖ = 1 := by
    rw [ae_add_measure_iff]
    constructor
    · filter_upwards [hNb, hnν] with x hx hnx
      rw [hx, hnx]
    · filter_upwards [hNs, hnη] with x hx hnx
      rw [hx, hnx]
  have hNi : LocallyIntegrable N (μ.restrict D + ρ) :=
    locallyIntegrable_of_ae_norm_le _ hNm.aestronglyMeasurable (hn.mono fun _ hx => hx.le)
  have hdiv (X : AmbientSpace → AmbientSpace) (hX : ContDiff ℝ 1 X)
      (hcX : HasCompactSupport X) :
      (∫ x in F, divergenceN X x) = ∫ x, inner ℝ (X x) (N x) ∂(μ.restrict D + ρ) := by
    have hi := integrable_inner_density_compact hNi hX.continuous hcX
    have hib : Integrable (fun x => inner ℝ (X x) (N x)) (μ.restrict D) :=
      hi.mono_measure (Measure.le_add_right le_rfl)
    have his : Integrable (fun x => inner ℝ (X x) (N x)) ρ :=
      hi.mono_measure (Measure.le_add_left le_rfl)
    rw [integral_add_measure hib his, hpair X hX hcX]
    congr 1
    · exact integral_congr_ae (hNb.mono fun x hx => congrArg (fun v => inner ℝ (X x) v) hx) |>.symm
    · exact integral_congr_ae (hNs.mono fun x hx => congrArg (fun v => inner ℝ (X x) v) hx) |>.symm
  apply perimeterIn_eq_of_ambient_coordinate_pairing hmF hNm hn _ hU
  intro i φ hφ
  let X : AmbientSpace → AmbientSpace := fun z => φ z • EuclideanSpace.single i 1
  have hdiff (z : AmbientSpace) : divergenceN X z =
      fderiv ℝ φ z (EuclideanSpace.single i 1) := by
    rw [divergenceN_smul hφ contDiff_const]
    simp [divergenceN, inner_gradient_left]
  have ht := hdiv X (hφ.smul contDiff_const) φ.hasCompactSupport.smul_right
  simp only [hdiff, X, real_inner_smul_left, EuclideanSpace.inner_single_left,
    one_mul, conj_trivial] at ht
  have hi : (fun x => F.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      F.indicator (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    funext x
    by_cases hx : x ∈ F <;> simp [hx]
  rw [hi, integral_indicator₀ hmF, ht]
  simp only [mul_neg, integral_neg]

/-- Omitting or including the sphere makes no difference to a measure which
gives the sphere zero mass. -/
lemma ball_compl_ae_eq_closedBall_compl {μ : Measure AmbientSpace}
    {c : AmbientSpace} {r : ℝ} (hnull : μ (sphere c r) = 0) :
    (ball c r)ᶜ =ᵐ[μ] (closedBall c r)ᶜ := by
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hnull] with x hx
  apply propext
  change (¬dist x c < r) ↔ ¬dist x c ≤ r
  have hne : dist x c ≠ r := hx
  simp only [not_lt, not_le]
  exact ⟨fun hh => lt_of_le_of_ne hh hne.symm, le_of_lt⟩

lemma integral_ball_add_closedBall_compl {μ : Measure AmbientSpace}
    {c : AmbientSpace} {r : ℝ} (hnull : μ (sphere c r) = 0)
    {q : AmbientSpace → ℝ} (hq : Integrable q μ) :
    (∫ x in ball c r, q x ∂μ) + (∫ x in (closedBall c r)ᶜ, q x ∂μ) = ∫ x, q x ∂μ := by
  have he := setIntegral_congr_set (f := q) (ball_compl_ae_eq_closedBall_compl hnull)
  exact (congrArg (fun t => (∫ x in ball c r, q x ∂μ) + t) he).symm.trans
    (integral_add_compl measurableSet_ball hq)

lemma setIntegral_indicator_eq_inter_of_nullMeasurable {E D : Set AmbientSpace}
    {μ : Measure AmbientSpace} (hmE : NullMeasurableSet E μ) (q : AmbientSpace → ℝ) :
    (∫ x in D, E.indicator q x ∂μ) = ∫ x in E ∩ D, q x ∂μ := by
  rw [integral_indicator₀ (hmE.mono Measure.restrict_le_self),
    Measure.restrict_restrict₀ (hmE.mono Measure.restrict_le_self)]

/-- The two actual cuts have bulk and spherical divergence terms with opposite
normal signs. The exterior identity uses the absence of original derivative
mass on the cutting sphere, and permits infinite exterior perimeter. -/
theorem IsGoodRadius.exists_cut_divergence_pairings {E : Set AmbientSpace}
    {hE : HasLocallyFinitePerimeter E} {hmE : NullMeasurableSet E volume}
    {c : AmbientSpace} {r : ℝ} (hg : IsGoodRadius E hE hmE c r) :
    ∃ N : AmbientSpace → AmbientSpace, Measurable N ∧
      (∀ᵐ x ∂(hausdorffMeasure2 3).restrict (sphere c r), ‖N x‖ = 1) ∧
      (∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
        (∫ x in E ∩ ball c r, divergenceN X x) =
          (∫ x in ball c r, inner ℝ (X x) (canonicalOutwardPolarDensity E hE hmE x)
            ∂canonicalPerimeterMeasure E hE hmE) +
          ∫ x in densityOne E ∩ sphere c r, inner ℝ (X x) (N x) ∂hausdorffMeasure2 3) ∧
      ∀ (X : AmbientSpace → AmbientSpace), ContDiff ℝ 1 X → HasCompactSupport X →
        (∫ x in E \ closedBall c r, divergenceN X x) =
          (∫ x in (closedBall c r)ᶜ,
            inner ℝ (X x) (canonicalOutwardPolarDensity E hE hmE x)
              ∂canonicalPerimeterMeasure E hE hmE) -
          ∫ x in densityOne E ∩ sphere c r, inner ℝ (X x) (N x) ∂hausdorffMeasure2 3 := by
  have hp := canonicalPerimeterPolar E hE hmE
  let := hp.regular
  let := hp.finiteOnCompacts
  have hB := hasC1Boundary_ball c hg.1
  have hK : IsCompact (frontier (ball c r)) := by
    rw [frontier_ball c hg.1.ne']
    exact isCompact_sphere c r
  have hf := hE.isLocallyBVOn_indicator hmE univ
  have hpair : ∀ (i : Fin 3) (φ : CompactlySupportedContinuousMap AmbientSpace ℝ),
      ContDiff ℝ 1 φ →
        -(∫ z, E.indicator (fun _ => (1 : ℝ)) z *
          fderiv ℝ φ z (EuclideanSpace.single i 1)) =
          ∫ z, φ z * (-canonicalOutwardPolarDensity E hE hmE z) i
            ∂canonicalPerimeterMeasure E hE hmE := fun i φ hφ => hp.coordinate_eq i φ hφ
  obtain ⟨T, N, _, hNm, hn, hTC, _, hcut⟩ :=
    hB.exists_integrable_trace_cut_pairing isOpen_ball hK hf hp.locallyIntegrable.neg hpair
  have hTeq : T =ᵐ[(hausdorffMeasure2 3).restrict (frontier (ball c r))]
      (densityOne E).indicator (fun _ => (1 : ℝ)) := by
    apply hB.ae_of_chartwise hK
    intro d hd
    have hh := hg.2.2 d hd
    rw [← frontier_ball c hg.1.ne'] at hh
    filter_upwards [hTC d hd, hh] with z hz hz'
    intro hzd
    exact (hz hzd).trans (hz' hzd)
  rw [frontier_ball c hg.1.ne'] at hTeq hn hcut
  have hinside (X : AmbientSpace → AmbientSpace) (hX : ContDiff ℝ 1 X)
      (hcX : HasCompactSupport X) :
      (∫ x in E ∩ ball c r, divergenceN X x) =
        (∫ x in ball c r, inner ℝ (X x) (canonicalOutwardPolarDensity E hE hmE x)
          ∂canonicalPerimeterMeasure E hE hmE) +
        ∫ x in densityOne E ∩ sphere c r, inner ℝ (X x) (N x) ∂hausdorffMeasure2 3 := by
    have ht := hcut X hX hcX
    have hfun : (fun x => E.indicator (fun _ => (1 : ℝ)) x * divergenceN X x) =
        E.indicator (divergenceN X) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [hfun, setIntegral_indicator_eq_inter_of_nullMeasurable hmE] at ht
    simp only [Pi.neg_apply, inner_neg_right, integral_neg, neg_neg] at ht
    have hs : (∫ x in sphere c r, T x * inner ℝ (X x) (N x) ∂hausdorffMeasure2 3) =
        ∫ x in densityOne E ∩ sphere c r, inner ℝ (X x) (N x) ∂hausdorffMeasure2 3 := by
      calc
        _ = ∫ x in sphere c r, (densityOne E).indicator
            (fun y => inner ℝ (X y) (N y)) x ∂hausdorffMeasure2 3 := by
          apply integral_congr_ae
          filter_upwards [hTeq] with x hx
          rw [hx]
          by_cases he : x ∈ densityOne E <;> simp [he]
        _ = _ := setIntegral_indicator_eq_inter_of_nullMeasurable
          (measurableSet_densityOne hmE).nullMeasurableSet _
    exact ht.trans (by rw [hs])
  refine ⟨N, hNm, hn, hinside, fun X hX hcX => ?_⟩
  have hsource := integral_ball_add_closedBall_compl (Measure.addHaar_sphere volume c r)
    ((integrable_divergenceN hX hcX).indicator₀ hmE)
  rw [setIntegral_indicator_eq_inter_of_nullMeasurable hmE,
    setIntegral_indicator_eq_inter_of_nullMeasurable hmE, integral_indicator₀ hmE] at hsource
  have hbulk := integral_ball_add_closedBall_compl hg.2.1
    (integrable_inner_density_compact hp.locallyIntegrable hX.continuous hcX)
  have htotal := hp.divergence_eq X hX hcX
  have hin := hinside X hX hcX
  change (∫ x in E ∩ (closedBall c r)ᶜ, divergenceN X x) = _
  linarith

/-- Exact relative perimeter formulas for both cuts, on every open region. -/
theorem IsGoodRadius.perimeterIn_cut_identities {E : Set AmbientSpace}
    {hE : HasLocallyFinitePerimeter E} {hmE : NullMeasurableSet E volume}
    {c : AmbientSpace} {r : ℝ} (hg : IsGoodRadius E hE hmE c r)
    {U : Set AmbientSpace} (hU : IsOpen U) :
    perimeterIn (E ∩ ball c r) U = perimeterIn E (U ∩ ball c r) +
      hausdorffMeasure2 3 (U ∩ (densityOne E ∩ sphere c r)) ∧
    perimeterIn (E \ ball c r) U = perimeterIn E (U ∩ (closedBall c r)ᶜ) +
      hausdorffMeasure2 3 (U ∩ (densityOne E ∩ sphere c r)) := by
  have hp := canonicalPerimeterPolar E hE hmE
  let := hp.regular
  let := hp.finiteOnCompacts
  obtain ⟨N, hNm, hn, hin, hout⟩ := hg.exists_cut_divergence_pairings
  let S := densityOne E ∩ sphere c r
  have hSm : MeasurableSet S := (measurableSet_densityOne hmE).inter isClosed_sphere.measurableSet
  let ρ := (hausdorffMeasure2 3).restrict S
  let : IsFiniteMeasure ρ := ⟨by
    rw [Measure.restrict_apply_univ]
    apply (measure_mono (show S ⊆ sphere c r from inter_subset_right)).trans_lt
    rw [hausdorffMeasure2_sphere c hg.1]
    exact ENNReal.ofReal_lt_top⟩
  have hnρ : ∀ᵐ x ∂ρ, ‖N x‖ = 1 :=
    ae_restrict_of_ae_restrict_of_subset (show S ⊆ sphere c r from inter_subset_right) hn
  have hρB : ρ (ball c r) = 0 := by
    rw [Measure.restrict_apply measurableSet_ball]
    apply measure_mono_null (t := ∅) _ (measure_empty)
    intro x hx
    have hlt : dist x c < r := hx.1
    have heq : dist x c = r := hx.2.2
    exact (hlt.ne heq).elim
  have hρO : ρ (closedBall c r)ᶜ = 0 := by
    rw [Measure.restrict_apply isClosed_closedBall.measurableSet.compl]
    apply measure_mono_null (t := ∅) _ (measure_empty)
    intro x hx
    have hnot : ¬ dist x c ≤ r := hx.1
    have heq : dist x c = r := hx.2.2
    exact (hnot heq.le).elim
  have hi := perimeterIn_eq_of_disjoint_divergence_pairing
    (hmE.inter measurableSet_ball.nullMeasurableSet) measurableSet_ball hp.measurable hNm
    (ae_restrict_of_ae hp.norm_ae) hnρ hρB hin hU
  have ho := perimeterIn_eq_of_disjoint_divergence_pairing
    (F := E \ closedBall c r) (D := (closedBall c r)ᶜ) (ρ := ρ)
    (hmE.diff isClosed_closedBall.measurableSet.nullMeasurableSet)
    isClosed_closedBall.measurableSet.compl hp.measurable hNm.neg
    (ae_restrict_of_ae hp.norm_ae) (hnρ.mono fun x hx => by simpa using hx) hρO
    (fun X hX hcX => by
      simpa only [Pi.neg_apply, inner_neg_right, integral_neg, sub_eq_add_neg]
        using! hout X hX hcX) hU
  have hset : E \ ball c r =ᵐ[volume] E \ closedBall c r := by
    filter_upwards [ball_compl_ae_eq_closedBall_compl (Measure.addHaar_sphere volume c r)] with x hx
    apply propext
    exact and_congr Iff.rfl (Iff.of_eq hx)
  have he : perimeterIn (E \ ball c r) U = perimeterIn (E \ closedBall c r) U :=
    perimeterIn_congr_ae U (ae_restrict_of_ae hset)
  rw [he]
  constructor
  · rw [hi, Measure.add_apply, Measure.restrict_apply hU.measurableSet,
      Measure.restrict_apply hU.measurableSet, hp.open_eq _ (hU.inter isOpen_ball)]
  · rw [ho, Measure.add_apply, Measure.restrict_apply hU.measurableSet,
      Measure.restrict_apply hU.measurableSet,
      hp.open_eq _ (hU.inter isClosed_closedBall.isOpen_compl)]

/-- Blueprint `prop:cut-identities`, for both spherical cuts. All terms are
extended real, so no finite global perimeter hypothesis is needed. -/
theorem IsGoodRadius.perimeter_cut_identities {E : Set AmbientSpace}
    {hE : HasLocallyFinitePerimeter E} {hmE : NullMeasurableSet E volume}
    {c : AmbientSpace} {r : ℝ} (hg : IsGoodRadius E hE hmE c r) :
    perimeter (E ∩ ball c r) = perimeterIn E (ball c r) +
      hausdorffMeasure2 3 (densityOne E ∩ sphere c r) ∧
    perimeter (E \ ball c r) = perimeterIn E (closedBall c r)ᶜ +
      hausdorffMeasure2 3 (densityOne E ∩ sphere c r) := by
  have ht := hg.perimeterIn_cut_identities isOpen_univ
  rw [← perimeterN_eq_perimeter _ (hmE.inter measurableSet_ball.nullMeasurableSet),
    ← perimeterN_eq_perimeter _ (hmE.diff measurableSet_ball.nullMeasurableSet)]
  simpa only [perimeterN, univ_inter] using ht

/-- Ordinary volume partitions exactly into the two radial cuts. -/
lemma volume_radial_cut_add (E : Set AmbientSpace) (c : AmbientSpace) (r : ℝ) :
    volume (E ∩ ball c r) + volume (E \ ball c r) = volume E := by
  exact measure_inter_add_sdiff E measurableSet_ball

end LiquidDrop
