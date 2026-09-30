module

public import NoCompromise.Elliptic.BoundaryHolderTraceAlgebra
public import NoCompromise.Elliptic.BoundaryNeumannReflection

@[expose] public section

/-! Compact localization across the curved face, preserving the flat boundary. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- A cutoff supported in the ambient ball extends upper-half-ball H¹ data to
the whole upper half-space. It is not required to vanish on the flat face. -/
lemma HasH1GradientOn.boundary_neumann_cutoff
    {w ζ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hw : HasH1GradientOn w F (boundaryHalfBall 1))
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ ball 0 1) :
    HasH1GradientOn (fun x => ζ x * w x)
      (fun x => ζ x • F x + w x • gradient ζ x)
        {x | 0 < x (Fin.last 2)} := by
  let U := {x : EuclideanSpace ℝ (Fin 3) | 0 < x (Fin.last 2)}
  have hU : MeasurableSet U := boundary_holder_open_upper.measurableSet
  obtain ⟨hmf, hmG⟩ := boundary_cutoff_memLp_upper measurableSet_ball
    hw.memLp_function hw.memLp_gradient hζ hcζ hsζ
  apply hasH1GradientOn_of_memLp_test ((memLp_indicator_iff_restrict hU).mp hmf)
    ((memLp_indicator_iff_restrict hU).mp hmG)
  intro i φ hφ hcφ hsφ
  let v := EuclideanSpace.single i (1 : ℝ)
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdζ : Continuous (fun x => fderiv ℝ ζ x v) :=
    (hζ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hmA : MemLp (fun x => ζ x * fderiv ℝ φ x v) 2 volume :=
    (hζ.continuous.mul hdφ).memLp_of_hasCompactSupport hcζ.mul_right
  have hmB : MemLp (fun x => φ x * fderiv ℝ ζ x v) 2 volume :=
    (hφ.continuous.mul hdζ).memLp_of_hasCompactSupport hcφ.mul_right
  have hmZ : MemLp (fun x => ζ x * φ x) 2 volume :=
    (hζ.continuous.mul hφ.continuous).memLp_of_hasCompactSupport hcζ.mul_right
  have hiA := (hmA.restrict (boundaryHalfBall 1)).integrable_mul hw.memLp_function
  have hiB := (hmB.restrict (boundaryHalfBall 1)).integrable_mul hw.memLp_function
  change IntegrableOn (fun x => (ζ x * fderiv ℝ φ x v) * w x) (boundaryHalfBall 1) at hiA
  change IntegrableOn (fun x => (φ x * fderiv ℝ ζ x v) * w x) (boundaryHalfBall 1) at hiB
  have hmFi := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).comp_memLp'
    hw.memLp_gradient
  have hiZ := (hmZ.restrict (boundaryHalfBall 1)).integrable_mul hmFi
  change IntegrableOn (fun x => (ζ x * φ x) * F x i) (boundaryHalfBall 1) at hiZ
  have htest := hw.test_eq i (fun x => ζ x * φ x) (hζ.mul hφ) hcζ.mul_right
    (fun x hx => ⟨hsζ (tsupport_mul_subset_left hx), hsφ (tsupport_mul_subset_right hx)⟩)
  have hderiv (x) : w x * fderiv ℝ (fun y => ζ y * φ y) x v =
      (ζ x * fderiv ℝ φ x v) * w x + (φ x * fderiv ℝ ζ x v) * w x := by
    rw [fderiv_fun_mul (hζ.differentiable one_ne_zero x)
      (hφ.differentiable one_ne_zero x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  change -(∫ x in boundaryHalfBall 1, w x * fderiv ℝ (fun y => ζ y * φ y) x v) = _ at htest
  simp_rw [hderiv] at htest
  rw [integral_add hiA hiB] at htest
  have hζzero (x) (hx : x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1) : ζ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h))
  have hgzero (x) (hx : x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1) : gradient ζ x = 0 :=
    gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h))
  have hrestrict (g : EuclideanSpace ℝ (Fin 3) → ℝ)
      (hg : ∀ x ∉ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = 0) :
      (∫ x in U, g x) = ∫ x in boundaryHalfBall 1, g x := by
    have hh := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume.restrict U) (s := ball 0 1) hg
    rw [Measure.restrict_restrict measurableSet_ball] at hh
    exact hh.symm
  change -(∫ x in U, ζ x * w x * fderiv ℝ φ x v) =
    ∫ x in U, φ x * (ζ x • F x + w x • gradient ζ x) i
  rw [hrestrict _ (fun x hx => by rw [hζzero x hx]; simp),
    hrestrict _ (fun x hx => by rw [hζzero x hx, hgzero x hx]; simp)]
  have hleft : (fun x => ζ x * w x * fderiv ℝ φ x v) =
      fun x => (ζ x * fderiv ℝ φ x v) * w x := by funext x; ring
  have hright : (fun x => φ x * (ζ x • F x + w x • gradient ζ x) i) =
      fun x => (ζ x * φ x) * F x i + (φ x * fderiv ℝ ζ x v) * w x := by
    funext x
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, gradient_apply_eq_fderiv_single]
    ring
  rw [hleft, hright, integral_add hiZ hiB]
  linarith

end LiquidDrop
