import NoCompromise.Elliptic.BoundaryHolderTests
import NoCompromise.Elliptic.FrozenDecayChange

/-!
# Weak reflection of a frozen boundary equation

The original constant coefficient need not be symmetric. Its skew part cancels
against scalar weak gradients, and genuine H¹₀ density permits antisymmetric
smooth tests meeting the flat boundary.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_holder_gradient_sub {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => f y - g y) x = gradient f x - gradient g x := by
  ext i
  simp only [gradient_apply_eq_fderiv_single, PiLp.sub_apply,
    fderiv_fun_sub (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x),
    sub_apply]

/-- Compact C¹ tests vanishing on the flat face are justified from the original
interior weak equation, including cancellation of a nonsymmetric frozen skew part. -/
theorem HasH1GradientOn.boundary_frozen_test {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : IsOpen W)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G (W ∩ {x | 0 < x (Fin.last k)}))
    (A : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0)
      (W ∩ {x | 0 < x (Fin.last k)}))
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ W)
    (hz : ∀ x : EuclideanSpace ℝ (Fin k), φ (graphAppendN x 0) = 0) :
    (∫ x in W ∩ {x | 0 < x (Fin.last k)},
      inner ℝ (frozenSymmetricPart A (G x)) (gradient φ x)) = 0 := by
  let D := W ∩ {x : EuclideanSpace ℝ (Fin (k + 1)) | 0 < x (Fin.last k)}
  have hD : IsOpen D := hW.inter boundary_holder_open_upper
  obtain ⟨hψ, hmψ⟩ := boundary_holder_smooth_test_mem_h1Zero hW hφ hcφ hsφ hz
  let v : H1ZeroSpace hD := ⟨H1Space.ofFunction φ (gradient φ)
    (hψ.mono (subset_univ D)), hmψ⟩
  have hh := campanato_integral_inner_gradient_eq_zero_of_smooth_tests hD
    ((frozenSymmetricPart A).comp_memLp' hf.memLp_gradient) (fun τ hτ hcτ hsτ => by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsτ ht)), inner_zero_right])]
      exact hf.integral_frozenSymmetricPart_gradient_eq_zero A hw hτ hcτ hsτ) v
  calc
    _ = ∫ x in D, inner ℝ (frozenSymmetricPart A (G x)) (v.val.gradientLp x) := by
      apply integral_congr_ae
      filter_upwards [H1Space.gradientLp_ofFunction φ (gradient φ)
        (hψ.mono (subset_univ D))] with x hx
      change _ = inner ℝ (frozenSymmetricPart A (G x))
        ((H1Space.ofFunction φ (gradient φ) (hψ.mono (subset_univ D))).gradientLp x)
      rw [hx]
    _ = 0 := hh

/-- The adapted odd extension has its actual weak gradient. -/
theorem HasH1GradientOn.boundary_odd_extension {m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hf : HasH1GradientOn f G univ)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (n : EuclideanSpace ℝ (Fin m))
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0) :
    HasH1GradientOn (fun x => f x - f (boundaryFrozenReflection A n x))
      (fun x => G x - (boundaryFrozenReflection A n).adjoint
        (G (boundaryFrozenReflection A n x))) univ := by
  let R := boundaryFrozenReflectionEquiv A n hn
  have hc := (hf.comp_homeomorph R.toHomeomorph R.lipschitzWith R.symm.lipschitzWith).1
  have hh : HasH1GradientOn (fun x => f (R x))
      (fun x => R.toContinuousLinearMap.adjoint (G (R x))) univ := by
    change HasH1GradientOn (f ∘ R)
      (fun x => (fderiv ℝ R x).adjoint (G (R x))) univ at hc
    simpa only [Function.comp_def, ContinuousLinearEquiv.fderiv] using hc
  exact hf.sub hh

lemma boundary_holder_reflected_pairing {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (n : EuclideanSpace ℝ (Fin m))
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    {φ : EuclideanSpace ℝ (Fin m) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    (∫ x, inner ℝ (frozenSymmetricPart A ((boundaryFrozenReflection A n).adjoint
      (G (boundaryFrozenReflection A n x)))) (gradient φ x)) =
      ∫ x, inner ℝ (frozenSymmetricPart A (G x))
        (gradient (φ ∘ boundaryFrozenReflection A n) x) := by
  let R := boundaryFrozenReflectionEquiv A n hn
  have hm := (boundaryFrozenReflection_measurePreserving A n hn).integral_comp
    R.toHomeomorph.measurableEmbedding
    (fun x => inner ℝ (frozenSymmetricPart A ((boundaryFrozenReflection A n).adjoint
      (G (boundaryFrozenReflection A n x)))) (gradient φ x))
  rw [← hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [boundaryFrozenReflection_involutive A n hn,
    ← boundaryFrozenReflection_intertwine,
    ← ContinuousLinearMap.adjoint_inner_right]
  have hg := frozen_gradient_comp_linear R (hφ.differentiable one_ne_zero) x
  exact congrArg (fun y => inner ℝ (frozenSymmetricPart A (G x)) y) hg.symm

/-- A genuine zero extension of a frozen upper-domain solution reflects to a
whole-neighborhood weak solution. Both the H¹ chain rule and the boundary test
passage are proved inputs, and no regularity of the original solution is assumed. -/
theorem HasH1GradientOn.boundary_odd_weak_equation {k : ℕ}
    {W V : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : IsOpen W)
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ)
    (hGzero : ∀ x, x (Fin.last k) ≤ 0 → G x = 0)
    (A : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hn : inner ℝ (frozenSymmetricPart A (EuclideanSpace.single (Fin.last k) 1))
      (EuclideanSpace.single (Fin.last k) 1) ≠ 0)
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0)
      (W ∩ {x | 0 < x (Fin.last k)}))
    (hVW : V ⊆ W)
    (hRVW : MapsTo (boundaryFrozenReflection A (EuclideanSpace.single (Fin.last k) 1)) V W) :
    IsWeakDivergenceEquationOn (fun _ => frozenSymmetricPart A)
      (fun x => G x - (boundaryFrozenReflection A (EuclideanSpace.single (Fin.last k) 1)).adjoint
        (G (boundaryFrozenReflection A (EuclideanSpace.single (Fin.last k) 1) x)))
      (fun _ => 0) V := by
  let n := EuclideanSpace.single (Fin.last k) (1 : ℝ)
  let R := boundaryFrozenReflectionEquiv A n hn
  let S := frozenSymmetricPart A
  have hmG : MemLp G 2 volume := by
    simpa only [Measure.restrict_univ] using hf.memLp_gradient
  intro φ hφ hcφ hsφ
  let ψ := fun x => φ x - φ (R x)
  have hψ : ContDiff ℝ 1 ψ := hφ.sub (hφ.comp R.contDiff)
  have hcψ : HasCompactSupport ψ := hcφ.sub (hcφ.comp_homeomorph R.toHomeomorph)
  have hsR : R ⁻¹' tsupport φ ⊆ W := by
    intro x hx
    have h := hRVW (hsφ hx)
    change boundaryFrozenReflection A n (boundaryFrozenReflection A n x) ∈ W at h
    rwa [boundaryFrozenReflection_involutive A n hn] at h
  have hsψ : tsupport ψ ⊆ W := (tsupport_sub _ _).trans
    (union_subset (hsφ.trans hVW) ((tsupport_comp_subset_preimage φ R.continuous).trans hsR))
  have hzψ (x : EuclideanSpace ℝ (Fin k)) : ψ (graphAppendN x 0) = 0 := by
    have hx : inner ℝ n (graphAppendN x 0) = 0 := by
      simp only [n, EuclideanSpace.inner_single_left, graphAppendN_last, mul_zero]
    change φ (graphAppendN x 0) - φ (boundaryFrozenReflection A n (graphAppendN x 0)) = 0
    rw [boundaryFrozenReflection_eq_self A n _ hx, sub_self]
  have hgr : MemLp (gradient φ) 2 volume :=
    (continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ))
  have hφR : ContDiff ℝ 1 (φ ∘ R) := hφ.comp R.contDiff
  have hcφR := hcφ.comp_homeomorph R.toHomeomorph
  have hgrR : MemLp (gradient (φ ∘ R)) 2 volume :=
    (continuous_gradient_of_contDiff hφR).memLp_of_hasCompactSupport
      (hcφR.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset (φ ∘ R)))
  have hmRG := R.toContinuousLinearMap.adjoint.comp_memLp'
    (hmG.comp_measurePreserving (boundaryFrozenReflection_measurePreserving A n hn))
  have hi1 := integrable_inner_of_memLp_two (S.comp_memLp' hmG) hgr
  have hi2 := integrable_inner_of_memLp_two (S.comp_memLp' hmRG) hgr
  have hi3 := integrable_inner_of_memLp_two (S.comp_memLp' hmG) hgrR
  change Integrable (fun x => inner ℝ (S (G x)) (gradient φ x)) at hi1
  change Integrable (fun x => inner ℝ (S (R.toContinuousLinearMap.adjoint (G (R x))))
    (gradient φ x)) at hi2
  change Integrable (fun x => inner ℝ (S (G x)) (gradient (φ ∘ R) x)) at hi3
  have hp := boundary_holder_reflected_pairing A n hn G hφ
  change (∫ x, inner ℝ (S (R.toContinuousLinearMap.adjoint (G (R x)))) (gradient φ x)) =
    ∫ x, inner ℝ (S (G x)) (gradient (φ ∘ R) x) at hp
  have htest := (hf.mono (subset_univ _)).boundary_frozen_test hW A hw hψ hcψ hsψ hzψ
  have heq : (∫ x, inner ℝ (S (G x)) (gradient ψ x)) = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := W ∩ {x | 0 < x (Fin.last k)}) (fun x hx => by
        by_cases hxW : x ∈ W
        · have hx0 : x (Fin.last k) ≤ 0 := le_of_not_gt (fun hp => hx ⟨hxW, hp⟩)
          rw [hGzero x hx0, map_zero, inner_zero_left]
        · rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hxW (hsψ ht)), inner_zero_right])]
    exact htest
  change (∫ x, inner ℝ (S (G x - R.toContinuousLinearMap.adjoint (G (R x))) - 0)
    (gradient φ x)) = 0
  simp_rw [sub_zero, map_sub, inner_sub_left]
  rw [integral_sub hi1 hi2, hp, ← integral_sub hi1 hi3]
  convert heq using 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change _ = inner ℝ (S (G x)) (gradient (fun y => φ y - (φ ∘ R) y) x)
  rw [boundary_holder_gradient_sub hφ hφR, inner_sub_right]

end LiquidDrop
