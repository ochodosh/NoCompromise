import NoCompromise.Elliptic.BoundaryNondivTrace
import NoCompromise.Elliptic.BoundaryHolderHalfScaling
import NoCompromise.Elliptic.NondivSchauderTests

/-!
# Boundary energy tests on arbitrary half balls

Even reflection supplies an H¹ extension, whose upper weak gradient is identified
by uniqueness. Actual zero flat trace makes every compact ambient cutoff of the
original function a genuine H¹₀ test on the half ball.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- An H¹ half-ball function has an H¹ extension to the ambient ball, with its
specified weak gradient unchanged almost everywhere on the original half ball. -/
theorem HasH1GradientOn.boundary_nondiv_even_extension {R : ℝ} (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {D : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hu : HasH1GradientOn u D (boundaryHalfBall R)) :
    ∃ (v : EuclideanSpace ℝ (Fin 3) → ℝ)
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      HasH1GradientOn v H (ball 0 R) ∧ EqOn v u (boundaryHalfBall R) ∧
      H =ᵐ[volume.restrict (boundaryHalfBall R)] D := by
  let e := frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hR
  have hmap : MapsTo e (boundaryHalfBall 1) (boundaryHalfBall R) := by
    intro x hx
    simpa only [mul_one] using (boundary_halfBall_scaling_mem hR x 1).mpr hx
  have hmapinv : MapsTo e.symm (ball 0 R) (ball 0 1) := by
    intro x hx
    apply (frozenBallScaling_mem_ball_iff 0 (e.symm x) hR 1).mp
    change e (e.symm x) ∈ ball 0 (R * 1)
    simpa only [mul_one, e.apply_symm_apply] using hx
  have hhalf (x) (hx : x ∈ boundaryHalfBall R) : e.symm x ∈ boundaryHalfBall 1 := by
    apply (boundary_halfBall_scaling_mem hR (e.symm x) 1).mp
    change e (e.symm x) ∈ boundaryHalfBall (R * 1)
    simpa only [mul_one, e.apply_symm_apply] using hx
  have hforward := (hu.comp_homeomorph_on (isOpen_boundaryHalfBall 1)
    (isOpen_boundaryHalfBall R) e (quasilinear_ballScaling_lipschitz 0 hR)
    (quasilinear_ballScaling_symm_lipschitz 0 hR) hmap).1
  have hreflect := hforward.boundary_even_h1
  have hback := (hreflect.comp_homeomorph_on isOpen_ball isOpen_ball e.symm
    (quasilinear_ballScaling_symm_lipschitz 0 hR)
    (quasilinear_ballScaling_lipschitz 0 hR) hmapinv).1
  have he : EqOn (boundaryEvenFunction (u ∘ e) ∘ e.symm) u (boundaryHalfBall R) := by
    intro x hx
    simp only [Function.comp_def, boundaryEvenFunction_eq_upper _ (hhalf x hx),
      e.apply_symm_apply]
  refine ⟨_, _, hback, he, ?_⟩
  have heae : (boundaryEvenFunction (u ∘ e) ∘ e.symm) =ᵐ[
      volume.restrict (boundaryHalfBall R)] u := by
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall R).measurableSet] with x hx
    exact he hx
  exact ((hback.mono inter_subset_left).congr_ae heae EventuallyEq.rfl).toHasWeakGradientOn.unique
    (isOpen_boundaryHalfBall R) hu.toHasWeakGradientOn

/-- A compact ambient cutoff times a zero-flat-trace H¹ function is an actual
H¹₀ function on the half ball. This justifies tests meeting the flat face. -/
theorem HasH1GradientOn.boundary_nondiv_cutoff_mem_h1Zero {R : ℝ} (hR : 0 < R)
    {u η : EuclideanSpace ℝ (Fin 3) → ℝ}
    {D : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hu : HasH1GradientOn u D (boundaryHalfBall R))
    (hT : HasZeroFlatTraceOn u D (ball 0 R))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ ball 0 R) :
    ∃ hv : HasH1GradientOn (fun x => η x * u x)
        (fun x => η x • D x + u x • gradient η x) (boundaryHalfBall R),
      H1Space.ofFunction _ _ hv ∈ h1ZeroSubmodule (isOpen_boundaryHalfBall R) := by
  obtain ⟨v, H, hv, he, heH⟩ := hu.boundary_nondiv_even_extension hR
  have heae : v =ᵐ[volume.restrict (boundaryHalfBall R)] u := by
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall R).measurableSet] with x hx
    exact he hx
  have hg := hv.locallyH1.mul_compact_cutoff (hη.of_le (by simp)) hcη hsη
  have htrace : flatTraceFunction (fun x => η x * v x)
      (fun x => η x • H x + v x • gradient η x) =ᵐ[volume] 0 :=
    (boundaryLocalizedFlatTrace_congr_ae measurableSet_ball hsη heae heH).trans
      (hT η hη hcη hsη)
  have hmem := hg.boundary_mem_h1Zero_inter_upper isOpen_ball hcη.mul_right
    (tsupport_mul_subset_left.trans hsη) htrace
  have hfun : (fun x => η x * v x) =ᵐ[volume.restrict (boundaryHalfBall R)]
      (fun x => η x * u x) := by
    filter_upwards [heae] with x hx
    rw [hx]
  have hgrad : (fun x => η x • H x + v x • gradient η x) =ᵐ[
      volume.restrict (boundaryHalfBall R)] (fun x => η x • D x + u x • gradient η x) := by
    filter_upwards [heae, heH] with x hx hy
    rw [hx, hy]
  have hresult := (hg.mono (subset_univ (boundaryHalfBall R))).congr_ae hfun hgrad
  refine ⟨hresult, ?_⟩
  have heq : H1Space.ofFunction _ _ (hg.mono (subset_univ (boundaryHalfBall R))) =
      H1Space.ofFunction _ _ hresult := by
    apply H1Space.ext_ae (isOpen_boundaryHalfBall R)
    filter_upwards [H1Space.coeFn_ofFunction _ _ (hg.mono (subset_univ (boundaryHalfBall R))),
      H1Space.coeFn_ofFunction _ _ hresult, hfun] with x hx hy hz
    rw [hx, hy, hz]
  exact heq ▸ hmem

/-- The original compact-test equation may be tested with `η²u` up to the flat
boundary. Its admissibility follows from the actual zero trace and H¹ density. -/
theorem boundary_nondiv_integral_inner_cutoff_sq_eq_zero {R : ℝ} (hR : 0 < R)
    {u η : EuclideanSpace ℝ (Fin 3) → ℝ}
    {D F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hu : HasH1GradientOn u D (boundaryHalfBall R))
    (hT : HasZeroFlatTraceOn u D (ball 0 R))
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall R)))
    (he : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ →
      HasCompactSupport φ → tsupport φ ⊆ boundaryHalfBall R →
      (∫ x, inner ℝ (F x) (gradient φ x)) = 0)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ ball 0 R) :
    (∫ x in boundaryHalfBall R, inner ℝ (F x)
      (η x ^ 2 • D x + (2 * η x * u x) • gradient η x)) = 0 := by
  have hs2 : tsupport (fun x => η x ^ 2) ⊆ tsupport η := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η))
  obtain ⟨hv, hmem⟩ := hu.boundary_nondiv_cutoff_mem_h1Zero hR hT (hη.pow 2)
    (hcη.of_isClosed_subset (isClosed_tsupport _) hs2) (hs2.trans hsη)
  let v : H1ZeroSpace (isOpen_boundaryHalfBall R) := ⟨H1Space.ofFunction _ _ hv, hmem⟩
  have ht := campanato_integral_inner_gradient_eq_zero_of_smooth_tests
    (isOpen_boundaryHalfBall R) hF (fun φ hφ hcφ hsφ => by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [gradient_eq_zero_of_notMem_tsupport (fun hh => hx (hsφ hh)), inner_zero_right])]
      exact he φ (hφ.of_le (by simp)) hcφ hsφ) v
  have hg (x) : gradient (fun y => η y ^ 2) x = (2 * η x) • gradient η x := by
    simpa only [pow_two, two_mul, add_smul] using
      gradient_mul (hη.of_le (by simp)) (hη.of_le (by simp)) x
  rw [← ht]
  apply integral_congr_ae
  filter_upwards [H1Space.gradientLp_ofFunction _ _ hv] with x hx
  change inner ℝ (F x) _ = inner ℝ (F x) ((H1Space.ofFunction _ _ hv).gradientLp x)
  rw [hx, hg, smul_smul]
  rw [show 2 * η x * u x = u x * (2 * η x) by ring]

end LiquidDrop
