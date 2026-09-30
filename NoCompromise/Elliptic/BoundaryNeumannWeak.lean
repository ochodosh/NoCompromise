module

public import NoCompromise.Elliptic.BoundaryNeumannCutoff
public import NoCompromise.Elliptic.BoundaryNeumannEquation

@[expose] public section

/-! Identification of the weak gradient supplied by the even-fold theorem. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma HasH1GradientOn.boundary_neumann_fold_h1
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hw : HasH1GradientOn w F {x | 0 < x (Fin.last 2)}) :
    HasH1GradientOn (w ∘ coordinateFold (Fin.last 2)) (boundaryNeumannDatum F) (ball 0 1) := by
  let R := coordinateReflection (Fin.last 2)
  let U := {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}
  let L := ball (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩ {x | x (Fin.last 2) < 0}
  have hU : IsOpen U := boundary_holder_open_upper
  have hL : IsOpen L := isOpen_ball.inter
    (isOpen_lt (EuclideanSpace.proj (Fin.last 2)).continuous continuous_const)
  have hc := hw.mono (show coordinateHalfCube (Fin.last 2) 3 ⊆ U from inter_subset_right)
  obtain ⟨G, hG, _, _⟩ := hc.coordinateFold_halfCube (Fin.last 2)
    (by norm_num : (2 : ℝ) < 3)
  have hb : ball (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ coordinateCube 3 2 := by
    intro x hx i
    have hn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
    have hi := PiLp.norm_apply_le x i
    change |x i| < 2
    change |x i| ≤ ‖x‖ at hi
    linarith
  have hGB := hG.mono hb
  have heU : (w ∘ coordinateFold (Fin.last 2)) =ᵐ[volume.restrict (boundaryHalfBall 1)] w := by
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
    simp only [Function.comp_def, coordinateFold_eq_self hx.2.le]
  have hGU := (hGB.mono (show boundaryHalfBall 1 ⊆ ball 0 1 from inter_subset_left)).congr_ae
    heU EventuallyEq.rfl
  have hupper : G =ᵐ[volume.restrict (boundaryHalfBall 1)] F :=
    HasWeakGradientOn.unique (isOpen_boundaryHalfBall 1) hGU.toHasWeakGradientOn
      (hw.mono (show boundaryHalfBall 1 ⊆ U from inter_subset_right)).toHasWeakGradientOn
  have hmaps : MapsTo R L U := by
    intro x hx
    change 0 < R x (Fin.last 2)
    rw [boundary_reflection_last]
    exact neg_pos.mpr hx.2
  have hR := (hw.comp_homeomorph_on hL hU R.toHomeomorph R.lipschitzWith R.symm.lipschitzWith hmaps).1
  have hR' : HasH1GradientOn (w ∘ R) (fun x => R (F (R x))) L := by
    change HasH1GradientOn (w ∘ R) (fun x => (fderiv ℝ R x).adjoint (F (R x))) L at hR
    have hfder (x) : fderiv ℝ R x = R.toContinuousLinearEquiv.toContinuousLinearMap :=
      R.toContinuousLinearEquiv.fderiv
    have hadj : R.toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
        R.toContinuousLinearEquiv.toContinuousLinearMap := boundary_reflection_adjoint
    simpa only [hfder, hadj, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hR
  have heL : (w ∘ coordinateFold (Fin.last 2)) =ᵐ[volume.restrict L] w ∘ R := by
    filter_upwards [ae_restrict_mem hL.measurableSet] with x hx
    simp only [Function.comp_def, coordinateFold_eq_reflection hx.2.le, R]
  have hGL := (hGB.mono (show L ⊆ ball 0 1 from inter_subset_left)).congr_ae
    heL EventuallyEq.rfl
  have hlower : G =ᵐ[volume.restrict L] fun x => R (F (R x)) :=
    HasWeakGradientOn.unique hL hGL.toHasWeakGradientOn hR'.toHasWeakGradientOn
  apply hGB.congr_ae EventuallyEq.rfl
  have hu := (ae_restrict_iff' (isOpen_boundaryHalfBall 1).measurableSet).mp hupper
  have hl := (ae_restrict_iff' hL.measurableSet).mp hlower
  filter_upwards [ae_restrict_of_ae hu, ae_restrict_of_ae hl,
    ae_restrict_of_ae (ae_coordinate_ne_zero (Fin.last 2)),
    ae_restrict_mem measurableSet_ball] with x hux hlx hn hx
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · rw [boundaryNeumannDatum, ite_eq_right (not_le.mpr hneg)]
    exact hlx ⟨hx, hneg⟩
  · rw [boundaryNeumannDatum_eq_upper F hpos.le]
    exact hux ⟨hx, hpos⟩

lemma HasH1GradientOn.boundary_even_h1_ball
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hw : HasH1GradientOn w F (boundaryHalfBall 1))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasH1GradientOn (boundaryEvenFunction w) (boundaryEvenField F) (ball 0 r) := by
  let ζ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
    ⟨r, (1 + r) / 2, hr, by linarith⟩
  have hsζ : tsupport ζ ⊆ ball 0 1 := by
    rw [ζ.tsupport_eq]
    exact closedBall_subset_ball (by dsimp [ζ]; linarith)
  have hc := hw.boundary_neumann_cutoff ζ.contDiff ζ.hasCompactSupport hsζ
  have he := hc.boundary_neumann_fold_h1
  have hsub : ball (0 : EuclideanSpace ℝ (Fin 3)) r ⊆ ball 0 1 := ball_subset_ball hr1.le
  have hone {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 r) : ζ x = 1 :=
    ζ.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hgrad {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 r) : gradient ζ x = 0 := by
    have hh := ζ.eventuallyEq_one_of_mem_ball hx
    ext i
    rw [gradient_apply_eq_fderiv_single, hh.fderiv_eq]
    simp
  have hreflect {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 r) :
      coordinateReflection (Fin.last 2) x ∈ ball 0 r := by
    simpa only [mem_ball, dist_zero_right, (coordinateReflection (Fin.last 2)).norm_map] using hx
  apply (he.mono hsub).congr_ae
  · filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero (Fin.last 2)),
      ae_restrict_mem measurableSet_ball] with x hn hx
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have hRx : coordinateReflection (Fin.last 2) x ∈ boundaryHalfBall 1 := by
        refine ⟨hsub (hreflect hx), ?_⟩
        change 0 < coordinateReflection (Fin.last 2) x (Fin.last 2)
        rw [boundary_reflection_last]
        linarith
      have hval : boundaryEvenFunction w x = w (coordinateReflection (Fin.last 2) x) := by
        rw [← boundaryEvenFunction_reflect w x, boundaryEvenFunction_eq_upper w hRx]
      simp only [Function.comp_def, coordinateFold_eq_reflection hneg.le,
        hone (hreflect hx), one_mul, hval]
    · simp only [Function.comp_def, coordinateFold_eq_self hpos.le, hone hx, one_mul,
        boundaryEvenFunction_eq_upper w ⟨hsub hx, hpos⟩]
  · filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero (Fin.last 2)),
      ae_restrict_mem measurableSet_ball] with x hn hx
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · simp only [boundaryNeumannDatum, ite_eq_right (not_le.mpr hneg), hone (hreflect hx),
        hgrad (hreflect hx), one_smul, smul_zero, add_zero,
        boundaryEvenField_eq_lower F (hsub hx) hneg]
    · simp only [boundaryNeumannDatum_eq_upper _ hpos.le, hone hx, hgrad hx,
        one_smul, smul_zero, add_zero, boundaryEvenField_eq_upper F ⟨hsub hx, hpos⟩]

/-- Even reflection has the explicitly reflected weak gradient on the full ball.
The proof localizes away from the curved boundary and identifies the gradient
of the existing cube extension by weak-gradient uniqueness on both sides. -/
theorem HasH1GradientOn.boundary_even_h1
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hw : HasH1GradientOn w F (boundaryHalfBall 1)) :
    HasH1GradientOn (boundaryEvenFunction w) (boundaryEvenField F) (ball 0 1) := by
  apply hasH1GradientOn_of_memLp_test
    ((boundaryEvenFunction_memLp hw.memLp_function).restrict (ball 0 1))
    ((boundaryEvenField_memLp hw.memLp_gradient).restrict (ball 0 1))
  intro i φ hφ hcφ hsφ
  obtain ⟨r, hr1, hsr⟩ := exists_lt_subset_ball (isClosed_tsupport φ) hsφ
  have hrpos : 0 < max r (1 / 2 : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hrlt : max r (1 / 2 : ℝ) < 1 := max_lt hr1 (by norm_num)
  have hs : tsupport φ ⊆ ball 0 (max r (1 / 2 : ℝ)) :=
    hsr.trans (ball_subset_ball (le_max_left _ _))
  have hh := (hw.boundary_even_h1_ball hrpos hrlt).test_eq i φ hφ hcφ hs
  have hleft (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : tsupport φ ⊆ U) :
      (∫ x in U, boundaryEvenFunction w x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, boundaryEvenFunction w x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun ht => hx (hU ht))]
    simp
  have hright (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : tsupport φ ⊆ U) :
      (∫ x in U, φ x * boundaryEvenField F x i) = ∫ x, φ x * boundaryEvenField F x i := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hU ht)), zero_mul]
  rw [hleft _ hs, hright _ hs] at hh
  rw [hleft _ hsφ, hright _ hsφ]
  exact hh

end LiquidDrop
