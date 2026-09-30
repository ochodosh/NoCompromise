module

public import NoCompromise.Variation.TransportLocalPerimeter
public import NoCompromise.Variation.TransportLocalDefs

@[expose] public section

/-!
# Perimeter transport under a C¹ diffeomorphism between open sets

Blueprint `thm:transport-perimeter` on open domains, perimeter-measure clause. Near each
source point, `Φ` and `E` agree with a global C¹ diffeomorphism and a cut-off set; the
global theorem and locality of the local perimeter measure and reduced boundary give the
identity on small balls, and a countable ball cover glues it.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Local data at a source point: a ball, a global C¹ diffeomorphism agreeing with `Φ`, and
a cut-off set agreeing with `E` on the ball, with matching images on the image ball. -/
theorem exists_transportLocal_ball_data
    (Φ : OpenPartialHomeomorph AmbientSpace AmbientSpace)
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hΦi : ContDiffOn ℝ 1 Φ.symm Φ.target)
    {E : Set AmbientSpace} (hEU : E ⊆ Φ.source)
    (hE : HasLocallyFinitePerimeterIn E Φ.source) (hmE : NullMeasurableSet E volume)
    {x₀ : AmbientSpace} (hx₀ : x₀ ∈ Φ.source) :
    ∃ r > 0, ball x₀ r ⊆ Φ.source ∧ ∃ Ψ : AmbientSpace ≃ₜ AmbientSpace,
      ContDiff ℝ 1 Ψ ∧ ContDiff ℝ 1 Ψ.symm ∧ EqOn Ψ Φ (ball x₀ r) ∧
      ∃ E' : Set AmbientSpace, HasLocallyFinitePerimeter E' ∧ NullMeasurableSet E' volume ∧
        E ∩ ball x₀ r = E' ∩ ball x₀ r ∧
        Φ '' E ∩ Ψ '' ball x₀ r = Ψ '' E' ∩ Ψ '' ball x₀ r := by
  obtain ⟨r, hr, hsub, Ψ, hΨ, hΨi, hEq⟩ :=
    exists_local_C1_extension_of_C1_diffeomorphism_on Φ hΦ hΦi hx₀
  obtain ⟨E', hE', hmE', hEE'⟩ := exists_globalPerimeter_eq_on_ball Φ.open_source hE hmE hr hsub
  have hBs : ball x₀ r ⊆ Φ.source :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hsub
  refine ⟨r, hr, hBs, Ψ, hΨ, hΨi, hEq, E', hE', hmE', hEE'.symm, ?_⟩
  ext z
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, ⟨w, hw, hwz⟩⟩
    have hvw : v = w := by
      apply Φ.injOn (hEU hv) (hBs hw)
      rw [← hEq hw, hwz]
    subst hvw
    exact ⟨⟨v, (hEE'.symm.subset ⟨hv, hw⟩).1, hwz⟩, ⟨v, hw, hwz⟩⟩
  · rintro ⟨⟨v, hv, rfl⟩, ⟨w, hw, hwz⟩⟩
    have hvw : w = v := Ψ.injective hwz
    subst hvw
    exact ⟨⟨w, (hEE'.subset ⟨hv, hw⟩).1, (hEq hw).symm⟩, ⟨w, hw, rfl⟩⟩

theorem nullMeasurableSet_image_homeomorph_C1 (Ψ : AmbientSpace ≃ₜ AmbientSpace)
    (hΨ : ContDiff ℝ 1 Ψ) {E' : Set AmbientSpace} (hmE' : NullMeasurableSet E' volume) :
    NullMeasurableSet (Ψ '' E') volume := by
  have h := nullMeasurableSet_image_of_C1_diffeomorphism_on Ψ.toOpenPartialHomeomorph
    (by simpa using hΨ.contDiffOn) (by simp) hmE'
  simpa using h

/-- Blueprint `thm:transport-perimeter` on open domains, perimeter clause: for every Borel
`A ⊆ U`, `Per(Φ(E); Φ(A)) = ∫_{∂*E ∩ A} |cof DΦ ν_E| dH²`, with local perimeter measures
and local reduced boundaries on `U` and `V`. -/
theorem perimeter_transport_of_C1_diffeomorphism_on
    (Φ : OpenPartialHomeomorph AmbientSpace AmbientSpace)
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hΦi : ContDiffOn ℝ 1 Φ.symm Φ.target)
    {E : Set AmbientSpace} (hEU : E ⊆ Φ.source)
    (hE : HasLocallyFinitePerimeterIn E Φ.source) (hmE : NullMeasurableSet E volume)
    {A : Set AmbientSpace} (hA : MeasurableSet A) (hAU : A ⊆ Φ.source) :
    localPerimeterMeasureAmbient (Φ '' E) Φ.target Φ.open_target
        (hasLocallyFinitePerimeterIn_image_of_C1_diffeomorphism_on Φ hΦ hΦi hEU hE hmE)
        (nullMeasurableSet_image_of_C1_diffeomorphism_on Φ hΦ hEU hmE) (Φ '' A) =
      ∫⁻ x in A ∩ localReducedBoundary E Φ.source Φ.open_source hE hmE,
        ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
          (localReducedNormal E Φ.source Φ.open_source hE hmE x)‖ ∂hausdorffMeasure2 3 := by
  set μ := localPerimeterMeasureAmbient (Φ '' E) Φ.target Φ.open_target
    (hasLocallyFinitePerimeterIn_image_of_C1_diffeomorphism_on Φ hΦ hΦi hEU hE hmE)
    (nullMeasurableSet_image_of_C1_diffeomorphism_on Φ hΦ hEU hmE) with hμ
  set R := localReducedBoundary E Φ.source Φ.open_source hE hmE with hR
  set f : AmbientSpace → ℝ≥0∞ := fun x => ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
    (localReducedNormal E Φ.source Φ.open_source hE hmE x)‖ with hf
  have hball : ∀ x₀ ∈ Φ.source, ∃ r > 0, ball x₀ r ⊆ Φ.source ∧
      ∀ A, MeasurableSet A → A ⊆ ball x₀ r →
        μ (Φ '' A) = ∫⁻ x in A ∩ R, f x ∂hausdorffMeasure2 3 := by
    intro x₀ hx₀
    obtain ⟨r, hr, hBs, Ψ, hΨ, hΨi, hEq, E', hE', hmE', hEE', himg⟩ :=
      exists_transportLocal_ball_data Φ hΦ hΦi hEU hE hmE hx₀
    refine ⟨r, hr, hBs, fun A hA hAB => ?_⟩
    have hWo : IsOpen (Ψ '' ball x₀ r) := Ψ.isOpenMap _ isOpen_ball
    have hWt : Ψ '' ball x₀ r ⊆ Φ.target := by
      rintro _ ⟨w, hw, rfl⟩
      rw [hEq hw]
      exact Φ.map_source (hBs hw)
    have hmF := nullMeasurableSet_image_homeomorph_C1 Ψ hΨ hmE'
    have hF := hasLocallyFinitePerimeter_image_of_C1_diffeomorphism Ψ hΨ hΨi E' hE' hmE'
    have hloc := localPerimeterMeasureAmbient_restrict_eq_of_inter_eq (Φ '' E) Φ.target
      Φ.open_target (hasLocallyFinitePerimeterIn_image_of_C1_diffeomorphism_on Φ hΦ hΦi hEU hE hmE)
      (nullMeasurableSet_image_of_C1_diffeomorphism_on Φ hΦ hEU hmE) hF hmF hWo hWt himg
    have hAimg : Φ '' A = Ψ '' A := ((hEq.mono hAB).image_eq).symm
    have hAW : Ψ '' A ⊆ Ψ '' ball x₀ r := image_mono hAB
    have hmA : MeasurableSet (Ψ '' A) := Ψ.measurableEmbedding.measurableSet_image.mpr hA
    have hset : A ∩ reducedBoundary E' hE' hmE' = A ∩ R := by
      have h := localReducedBoundary_inter_eq_of_inter_eq E Φ.source Φ.open_source hE hmE
        hE' hmE' isOpen_ball hBs hEE'
      calc A ∩ reducedBoundary E' hE' hmE'
          = A ∩ (ball x₀ r ∩ reducedBoundary E' hE' hmE') := by
            rw [← inter_assoc, inter_eq_left.mpr hAB]
        _ = A ∩ (ball x₀ r ∩ R) := by rw [← h]
        _ = A ∩ R := by rw [← inter_assoc, inter_eq_left.mpr hAB]
    calc μ (Φ '' A) = μ.restrict (Ψ '' ball x₀ r) (Ψ '' A) := by
          rw [hAimg, Measure.restrict_apply hmA, inter_eq_left.mpr hAW]
      _ = (canonicalPerimeterMeasure (Ψ '' E') hF hmF).restrict (Ψ '' ball x₀ r) (Ψ '' A) := by
          rw [hloc]
      _ = canonicalPerimeterMeasure (Ψ '' E') hF hmF (Ψ '' A) := by
          rw [Measure.restrict_apply hmA, inter_eq_left.mpr hAW]
      _ = ∫⁻ x in A ∩ reducedBoundary E' hE' hmE', ENNReal.ofReal ‖cofactor3 (fderiv ℝ Ψ x)
            (reducedNormal E' hE' hmE' x)‖ ∂hausdorffMeasure2 3 :=
          perimeter_transport_of_C1_diffeomorphism Ψ hΨ hΨi E' hE' hmE' hF hmF hA
      _ = ∫⁻ x in A ∩ reducedBoundary E' hE' hmE', f x ∂hausdorffMeasure2 3 := by
          apply setLIntegral_congr_fun (hA.inter (measurableSet_reducedBoundary E' hE' hmE'))
          intro x hx
          have hxB : x ∈ ball x₀ r := hAB hx.1
          have hd : fderiv ℝ Ψ x = fderiv ℝ Φ x :=
            (hEq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxB)).fderiv_eq
          change _ = ENNReal.ofReal ‖cofactor3 (fderiv ℝ Φ x)
            (localReducedNormal E Φ.source Φ.open_source hE hmE x)‖
          dsimp only
          rw [hd, localReducedNormal_eq_of_inter_eq E Φ.source Φ.open_source hE hmE
            hE' hmE' isOpen_ball hBs hEE' hxB]
      _ = ∫⁻ x in A ∩ R, f x ∂hausdorffMeasure2 3 := by rw [hset]
  have hμt : μ Φ.targetᶜ = 0 := localPerimeterMeasureAmbient_compl _ _ _ _ _
  have haem : AEMeasurable Φ.symm μ := by
    have hself : μ.restrict Φ.target = μ := localPerimeterMeasureAmbient_restrict_self _ _ _ _ _
    rw [← hself]
    exact Φ.continuousOn_symm.aemeasurable Φ.open_target.measurableSet
  have hm₁ : ∀ S, MeasurableSet S → S ⊆ Φ.source → μ.map Φ.symm S = μ (Φ '' S) := by
    intro S hS hSU
    rw [Measure.map_apply_of_aemeasurable haem hS, Φ.image_eq_target_inter_inv_preimage hSU,
      inter_comm, measure_inter_conull hμt]
  have hm₂ : ∀ S, MeasurableSet S →
      ((hausdorffMeasure2 3).restrict R).withDensity f S =
        ∫⁻ x in S ∩ R, f x ∂hausdorffMeasure2 3 := by
    intro S hS
    rw [withDensity_apply _ hS, Measure.restrict_restrict hS]
  obtain ⟨T, hT, r, hr, hcov⟩ := exists_countable_ball_cover (O := Φ.source)
    (fun x r => ∀ A, MeasurableSet A → A ⊆ ball x r →
      μ (Φ '' A) = ∫⁻ x in A ∩ R, f x ∂hausdorffMeasure2 3) (by
        intro x hx
        obtain ⟨r, hr, hBs, hP⟩ := hball x hx
        exact ⟨r, hr, hBs, hP⟩)
  have heq : (μ.map Φ.symm).restrict Φ.source =
      (((hausdorffMeasure2 3).restrict R).withDensity f).restrict Φ.source := by
    rw [← hcov]
    refine (Measure.restrict_biUnion_congr hT).mpr fun x _ => ?_
    ext S hS
    have hSB : MeasurableSet (S ∩ ball (x : AmbientSpace) (r x)) :=
      hS.inter isOpen_ball.measurableSet
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS,
      hm₁ _ hSB (inter_subset_right.trans (hr x).2.1), hm₂ _ hSB]
    exact (hr x).2.2 _ hSB inter_subset_right
  calc μ (Φ '' A) = μ.map Φ.symm A := (hm₁ A hA hAU).symm
    _ = (μ.map Φ.symm).restrict Φ.source A := by
        rw [Measure.restrict_apply hA, inter_eq_left.mpr hAU]
    _ = (((hausdorffMeasure2 3).restrict R).withDensity f).restrict Φ.source A := by rw [heq]
    _ = ((hausdorffMeasure2 3).restrict R).withDensity f A := by
        rw [Measure.restrict_apply hA, inter_eq_left.mpr hAU]
    _ = ∫⁻ x in A ∩ R, f x ∂hausdorffMeasure2 3 := hm₂ A hA

/-- Blueprint `thm:transport-perimeter` on open domains, normal clause: at `H²`-a.e. point
of the local reduced boundary of `E` in `U`, the local reduced normal of `Φ(E)` in `V` at
`Φ x` is `sign(det DΦ) · cof DΦ ν_E / |cof DΦ ν_E|`. -/
theorem reducedNormal_image_of_C1_diffeomorphism_on
    (Φ : OpenPartialHomeomorph AmbientSpace AmbientSpace)
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hΦi : ContDiffOn ℝ 1 Φ.symm Φ.target)
    {E : Set AmbientSpace} (hEU : E ⊆ Φ.source)
    (hE : HasLocallyFinitePerimeterIn E Φ.source) (hmE : NullMeasurableSet E volume) :
    ∀ᵐ x ∂(hausdorffMeasure2 3).restrict
        (localReducedBoundary E Φ.source Φ.open_source hE hmE),
      localReducedNormal (Φ '' E) Φ.target Φ.open_target
          (hasLocallyFinitePerimeterIn_image_of_C1_diffeomorphism_on Φ hΦ hΦi hEU hE hmE)
          (nullMeasurableSet_image_of_C1_diffeomorphism_on Φ hΦ hEU hmE) (Φ x) =
        Real.sign (fderiv ℝ Φ x).det •
          (‖cofactor3 (fderiv ℝ Φ x)
              (localReducedNormal E Φ.source Φ.open_source hE hmE x)‖⁻¹ •
            cofactor3 (fderiv ℝ Φ x) (localReducedNormal E Φ.source Φ.open_source hE hmE x)) := by
  set R := localReducedBoundary E Φ.source Φ.open_source hE hmE with hR
  set P : AmbientSpace → Prop := fun x =>
      localReducedNormal (Φ '' E) Φ.target Φ.open_target
          (hasLocallyFinitePerimeterIn_image_of_C1_diffeomorphism_on Φ hΦ hΦi hEU hE hmE)
          (nullMeasurableSet_image_of_C1_diffeomorphism_on Φ hΦ hEU hmE) (Φ x) =
        Real.sign (fderiv ℝ Φ x).det •
          (‖cofactor3 (fderiv ℝ Φ x)
              (localReducedNormal E Φ.source Φ.open_source hE hmE x)‖⁻¹ •
            cofactor3 (fderiv ℝ Φ x) (localReducedNormal E Φ.source Φ.open_source hE hmE x))
    with hP
  have hball : ∀ x₀ ∈ Φ.source, ∃ r > 0, ball x₀ r ⊆ Φ.source ∧
      ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (R ∩ ball x₀ r), P x := by
    intro x₀ hx₀
    obtain ⟨r, hr, hBs, Ψ, hΨ, hΨi, hEq, E', hE', hmE', hEE', himg⟩ :=
      exists_transportLocal_ball_data Φ hΦ hΦi hEU hE hmE hx₀
    refine ⟨r, hr, hBs, ?_⟩
    have hWo : IsOpen (Ψ '' ball x₀ r) := Ψ.isOpenMap _ isOpen_ball
    have hWt : Ψ '' ball x₀ r ⊆ Φ.target := by
      rintro _ ⟨w, hw, rfl⟩
      rw [hEq hw]
      exact Φ.map_source (hBs hw)
    have hmF := nullMeasurableSet_image_homeomorph_C1 Ψ hΨ hmE'
    have hF := hasLocallyFinitePerimeter_image_of_C1_diffeomorphism Ψ hΨ hΨi E' hE' hmE'
    have hglob := reducedNormal_image_of_C1_diffeomorphism Ψ hΨ hΨi E' hE' hmE' hF hmF
    have hset : R ∩ ball x₀ r = reducedBoundary E' hE' hmE' ∩ ball x₀ r := by
      have h := localReducedBoundary_inter_eq_of_inter_eq E Φ.source Φ.open_source hE hmE
        hE' hmE' isOpen_ball hBs hEE'
      rw [inter_comm, h, inter_comm]
    rw [hset]
    have h1 := ae_restrict_of_ae_restrict_of_subset
      (inter_subset_left (s := reducedBoundary E' hE' hmE') (t := ball x₀ r)) hglob
    filter_upwards [h1, ae_restrict_mem
      ((measurableSet_reducedBoundary E' hE' hmE').inter isOpen_ball.measurableSet)]
      with x hx hxm
    have hxB : x ∈ ball x₀ r := hxm.2
    have hd : fderiv ℝ Ψ x = fderiv ℝ Φ x :=
      (hEq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxB)).fderiv_eq
    have hn := localReducedNormal_eq_of_inter_eq E Φ.source Φ.open_source hE hmE
      hE' hmE' isOpen_ball hBs hEE' hxB
    have hΦW : Φ x ∈ Ψ '' ball x₀ r := ⟨x, hxB, hEq hxB⟩
    have hn' := localReducedNormal_eq_of_inter_eq (Φ '' E) Φ.target Φ.open_target
      (hasLocallyFinitePerimeterIn_image_of_C1_diffeomorphism_on Φ hΦ hΦi hEU hE hmE)
      (nullMeasurableSet_image_of_C1_diffeomorphism_on Φ hΦ hEU hmE) hF hmF hWo hWt himg hΦW
    rw [hEq hxB, hd] at hx
    simp only [hP]
    rw [hn', hn, hx]
  obtain ⟨T, hT, r, hr, hcov⟩ := exists_countable_ball_cover (O := Φ.source)
    (fun x r => ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (R ∩ ball x r), P y) (by
      intro x hx
      obtain ⟨r, hr, hBs, hPr⟩ := hball x hx
      exact ⟨r, hr, hBs, hPr⟩)
  have hRU : R ⊆ Φ.source := inter_subset_left
  have hRcov : R = ⋃ x ∈ T, (R ∩ ball (x : AmbientSpace) (r x)) := by
    rw [← inter_iUnion₂, hcov, inter_eq_left.mpr hRU]
  rw [hRcov]
  exact (ae_restrict_biUnion_iff _ hT _).mpr fun x _ => (hr x).2.2

end LiquidDrop
