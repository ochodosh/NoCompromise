module

public import NoCompromise.Elliptic.BoundaryNeumann

@[expose] public section

/-!
# Evenness of the homogeneous conormal representative

A sharpened form of Layer 1 of blueprint `thm:boundary-neumann`: the C¹
representative produced by even reflection is itself even on the ball, so its
normal derivative vanishes on the flat face. This is the pointwise
homogeneous conormal condition `∂₃ w = 0` used by the tangential
difference-quotient step of the second assertion.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_reflection_preimage_ball (r : ℝ) :
    coordinateReflection (Fin.last 2) ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 3)) r = ball 0 r := by
  ext x
  simp only [mem_preimage, mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]

/-- A function continuous on a centred ball which agrees almost everywhere there with a
reflection-even function is itself reflection-even on the ball. -/
lemma boundary_reflect_eq_of_ae_even {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {r : ℝ}
    (hv : ContinuousOn v (ball 0 r))
    (hg : ∀ x, g (coordinateReflection (Fin.last 2) x) = g x)
    (hgv : g =ᵐ[volume.restrict (ball 0 r)] v) :
    ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) r,
      v (coordinateReflection (Fin.last 2) x) = v x := by
  let R := coordinateReflection (Fin.last 2)
  have hmp : MeasurePreserving R (volume.restrict (ball 0 r)) (volume.restrict (ball 0 r)) := by
    have h := R.measurePreserving.restrict_preimage
      (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin 3))) (ε := r))
    rwa [boundary_reflection_preimage_ball] at h
  have hcomp : g ∘ R =ᵐ[volume.restrict (ball 0 r)] v ∘ R :=
    hmp.quasiMeasurePreserving.ae_eq_comp hgv
  have hgR : g ∘ R = g := funext hg
  rw [hgR] at hcomp
  have hae : v ∘ R =ᵐ[volume.restrict (ball 0 r)] v := hcomp.symm.trans hgv
  have hmaps : MapsTo R (ball 0 r) (ball 0 r) := fun x hx => by
    rwa [← boundary_reflection_preimage_ball] at hx
  have hvR : ContinuousOn (v ∘ R) (ball 0 r) := hv.comp R.continuous.continuousOn hmaps
  exact fun x hx => Measure.eqOn_open_of_ae_eq hae isOpen_ball hvR hv hx

/-- An even function differentiable at a flat point has zero normal derivative there. -/
lemma boundary_even_gradient_normal_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {r : ℝ}
    (heven : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) r,
      v (coordinateReflection (Fin.last 2) x) = v x)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 r) (hx3 : x (Fin.last 2) = 0)
    (hd : DifferentiableAt ℝ v x) :
    gradient v x (Fin.last 2) = 0 := by
  let R := coordinateReflection (Fin.last 2)
  have hRx : R x = x := by
    ext j
    simp only [R, coordinateReflection_apply]
    split_ifs with hj
    · subst hj; rw [hx3, neg_zero]
    · rfl
  have hev : v ∘ R =ᶠ[𝓝 x] v :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) (fun y hy => heven y hy)
  have hchain : fderiv ℝ (v ∘ R) x = (fderiv ℝ v x).comp (R : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) := by
    have hdR : DifferentiableAt ℝ v (R x) := by rwa [hRx]
    rw [fderiv_comp x hdR R.toContinuousLinearEquiv.differentiableAt, hRx]
    congr 1
    exact R.toContinuousLinearEquiv.fderiv
  have heq : fderiv ℝ v x = (fderiv ℝ v x).comp (R : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) := by
    rw [← hchain, hev.fderiv_eq]
  have hRe : R (EuclideanSpace.single (Fin.last 2) 1) = -EuclideanSpace.single (Fin.last 2) 1 := by
    ext j
    simp only [R, coordinateReflection_apply, PiLp.neg_apply]
    split_ifs with hj
    · rfl
    · have hj' : j ≠ (2 : Fin 3) := hj
      simp [hj']
  have happ := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ =>
    L (EuclideanSpace.single (Fin.last 2) 1)) heq
  simp only [ContinuousLinearMap.comp_apply] at happ
  change fderiv ℝ v x (EuclideanSpace.single (Fin.last 2) 1) =
    fderiv ℝ v x (R (EuclideanSpace.single (Fin.last 2) 1)) at happ
  rw [hRe, map_neg] at happ
  rw [gradient_apply_eq_fderiv_single]
  linarith

/-- Layer 1 of `thm:boundary-neumann` with the additional conclusions that the C¹
representative is even on `ball 0 (1/2)` and that its normal derivative vanishes on the
flat face. Hypotheses and constant are exactly those of
`boundary_neumann_homogeneous_c1_holder`. -/
theorem boundary_neumann_homogeneous_c1_holder_even {a lam cap HA HH M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHH : 0 ≤ HH) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (H F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (w : EuclideanSpace ℝ (Fin 3) → ℝ),
        ContinuousOn A (closure (boundaryHalfBall 1)) →
        ContinuousOn H (closure (boundaryHalfBall 1)) →
        (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖H x - H y‖ ≤ HH * dist x y ^ a) →
        (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → ∀ i : Fin 3, i ≠ Fin.last 2 →
          A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
          A x (EuclideanSpace.single (Fin.last 2) 1) i = 0) →
        (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0) →
        HasH1GradientOn w F (boundaryHalfBall 1) →
        (∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          tsupport φ ⊆ ball 0 1 →
          (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x) - H x) (gradient φ x)) = 0) →
        (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M →
        ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiffOn ℝ 1 v (ball 0 (1 / 2 : ℝ)) ∧
          w =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] v ∧
          F =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] gradient v ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient v x‖ ≤ C) ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
            ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ a) ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), v (coordinateReflection (Fin.last 2) x) = v x) ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), x (Fin.last 2) = 0 → gradient v x (Fin.last 2) = 0) := by
  obtain ⟨C, hC, hregularity⟩ := campanato_c1_holder (n := 3) (by norm_num) (by norm_num)
    (HA := 2 * HA) (HG := 2 * HH) (M := 2 * M)
    ha ha1 hlam hcap (by positivity) (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro A H F w hA hH hbA hell hholderA hholderH hcross hzero hw hweak henergy
  have hflux := boundary_neumann_flux_memLp ha.le hHH hA hH hbA hholderH hw.memLp_gradient
  have henergy' : (∫ x in ball 0 1, ‖boundaryEvenField F x‖ ^ 2) ≤ 2 * M := by
    rw [boundaryEvenField_energy hw.memLp_gradient]
    linarith
  obtain ⟨v, hv, hwv, hFv, hbound, hholder, _⟩ := hregularity
    (boundaryNeumannCoefficient A) (boundaryNeumannDatum H) (boundaryEvenField F)
    (boundaryEvenFunction w)
    (boundaryNeumannCoefficient_continuousOn ha hHA A hholderA hcross)
    (boundaryNeumannDatum_continuousOn ha hHH H hholderH hzero)
    (boundaryNeumannCoefficient_bound A hbA) (boundaryNeumannCoefficient_elliptic A hell)
    (boundaryNeumannCoefficient_holder ha.le hHA A hholderA hcross)
    (boundaryNeumannDatum_holder ha.le hHH H hholderH hzero)
    hw.boundary_even_h1 (boundary_neumann_even_weak_equation A F H hflux hweak) henergy'
  have hsub : boundaryHalfBall (1 / 2 : ℝ) ⊆ ball 0 (1 / 2 : ℝ) := inter_subset_left
  have hsub1 : boundaryHalfBall (1 / 2 : ℝ) ⊆ boundaryHalfBall 1 :=
    inter_subset_inter_left _ (ball_subset_ball (by norm_num))
  have heven := boundary_reflect_eq_of_ae_even hv.continuousOn
    (boundaryEvenFunction_reflect w) hwv
  refine ⟨v, hv, ?_, ?_, hbound, hholder, heven, ?_⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hwv,
      ae_restrict_mem (isOpen_boundaryHalfBall (1 / 2 : ℝ)).measurableSet] with x hx hxb
    rwa [boundaryEvenFunction_eq_upper w (hsub1 hxb)] at hx
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hFv,
      ae_restrict_mem (isOpen_boundaryHalfBall (1 / 2 : ℝ)).measurableSet] with x hx hxb
    rwa [boundaryEvenField_eq_upper F (hsub1 hxb)] at hx
  · intro x hx hx3
    exact boundary_even_gradient_normal_eq_zero heven hx hx3
      ((hv.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hx))

end LiquidDrop
