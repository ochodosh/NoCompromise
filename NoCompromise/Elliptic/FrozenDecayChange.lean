module

public import NoCompromise.Elliptic.FrozenDecayLinear
public import NoCompromise.Elliptic.FrozenDecaySkew
public import NoCompromise.Elliptic.WeakMaximumCore
public import NoCompromise.Sobolev.H1Chain

@[expose] public section

/-! Genuine weak harmonicity after the quantitative linear normalization.
The weak gradient chain rule, scalar-test skew cancellation, and Haar
change of variables are all used explicitly. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma frozen_integral_comp_linear {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f (L x)) = |(LinearMap.det L.toLinearEquiv.toLinearMap)⁻¹| * ∫ x, f x := by
  have h := integral_map_equiv (μ := volume) L.toHomeomorph.toMeasurableEquiv f
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    L.toLinearEquiv.isUnit_det'.ne_zero
  change Measure.map L volume = _ at hm
  change (∫ y, f y ∂Measure.map L volume) = ∫ x, f (L x) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul] at h
  exact h.symm

lemma frozen_gradient_comp_linear {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Differentiable ℝ φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (φ ∘ L) x = L.toContinuousLinearMap.adjoint (gradient φ (L x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    fderiv_comp x (hφ _) L.differentiableAt, L.fderiv]
  rfl

lemma frozen_inner_factor {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (G v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (L (L.toContinuousLinearMap.adjoint G))
      (L.symm.toContinuousLinearMap.adjoint v) =
      inner ℝ (L.toContinuousLinearMap.adjoint G) v := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (L.symm (L (L.toContinuousLinearMap.adjoint G))) v = _
  rw [L.symm_apply_apply]

/-- Smooth tests for the symmetric part follow from the original nonsymmetric
constant-coefficient weak equation. -/
lemma HasH1GradientOn.integral_frozenSymmetricPart_gradient_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasH1GradientOn u G U)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) U)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    (∫ x, inner ℝ (frozenSymmetricPart A (G x)) (gradient φ x)) = 0 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by simp)
  have hgr : MemLp (gradient φ) 2 (volume.restrict U) :=
    ((continuous_gradient_of_contDiff hφ1).memLp_of_hasCompactSupport
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ))).mono_measure
      Measure.restrict_le_self
  have hi (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      Integrable (fun x => inner ℝ (B (G x)) (gradient φ x)) (volume.restrict U) :=
    integrable_inner_of_memLp_two (B.comp_memLp' hu.memLp_gradient) hgr
  have hset (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      (∫ x in U, inner ℝ (B (G x)) (gradient φ x)) =
        ∫ x, inner ℝ (B (G x)) (gradient φ x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right])
  have hA : (∫ x in U, inner ℝ (A (G x)) (gradient φ x)) = 0 := by
    rw [hset]
    simpa only [sub_zero] using hw φ hφ1 hcφ hsφ
  have hadj := hu.toHasWeakGradientOn.integral_adjoint_gradient A hφ2 hcφ hsφ
  rw [← hset]
  have hp (x) : inner ℝ (frozenSymmetricPart A (G x)) (gradient φ x) =
      (1 / 2 : ℝ) * (inner ℝ (A (G x)) (gradient φ x) +
        inner ℝ (A.adjoint (G x)) (gradient φ x)) := by
    change inner ℝ ((1 / 2 : ℝ) • (A (G x) + A.adjoint (G x))) (gradient φ x) = _
    rw [real_inner_smul_left, inner_add_left]
  simp_rw [hp]
  rw [integral_const_mul, integral_add (hi A) (hi A.adjoint), hadj, hA]
  ring

/-- A genuine H¹ frozen solution becomes genuinely distributionally harmonic
under a factor of the symmetric coefficient. -/
theorem HasH1GradientOn.harmonic_comp_frozen_linear {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasH1GradientOn u G U)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) U)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hfactor : L.toContinuousLinearMap.comp L.toContinuousLinearMap.adjoint =
      frozenSymmetricPart A) :
    HasH1GradientOn (u ∘ L) (fun x => L.toContinuousLinearMap.adjoint (G (L x))) (L ⁻¹' U) ∧
      HasDistributionalLaplacianOn (u ∘ L) (fun _ => 0) (L ⁻¹' U) := by
  have hV : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hchain := (hu.comp_homeomorph_on hV hU L.toHomeomorph
    L.lipschitzWith L.symm.lipschitzWith (fun _ hx => hx)).1
  have hH : HasH1GradientOn (u ∘ L)
      (fun x => L.toContinuousLinearMap.adjoint (G (L x))) (L ⁻¹' U) := by
    change HasH1GradientOn (u ∘ L)
      (fun x => (fderiv ℝ L x).adjoint (G (L x))) (L ⁻¹' U) at hchain
    simpa only [ContinuousLinearEquiv.fderiv] using hchain
  refine ⟨hH, hH.locallyIntegrable_function, ?_, ?_⟩
  · exact continuous_const.locallyIntegrable.locallyIntegrableOn _
  · intro ψ hψ hcψ hsψ
    rw [hH.toHasWeakGradientOn.integral_mul_laplacianN (hψ.of_le (by simp)) hcψ hsψ]
    simp only [zero_mul, integral_zero, neg_eq_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsψ ht)), inner_zero_right])]
    let φ := ψ ∘ L.symm
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp L.symm.contDiff
    have hcφ : HasCompactSupport φ := hcψ.comp_homeomorph L.symm.toHomeomorph
    have hsφ : tsupport φ ⊆ U := by
      change tsupport (ψ ∘ L.symm.toHomeomorph) ⊆ U
      rw [tsupport_comp_eq_preimage ψ L.symm.toHomeomorph]
      intro x hx
      have hh := hsψ hx
      change L (L.symm x) ∈ U at hh
      simpa only [L.apply_symm_apply] using hh
    have hz := hu.integral_frozenSymmetricPart_gradient_eq_zero A hw hφ hcφ hsφ
    calc
      _ = ∫ x, inner ℝ (frozenSymmetricPart A (G (L x))) (gradient φ (L x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hg := frozen_gradient_comp_linear L.symm (hψ.differentiable (by simp)) (L x)
        change gradient φ (L x) = _ at hg
        rw [hg, L.symm_apply_apply, ← hfactor, ContinuousLinearMap.comp_apply]
        exact (frozen_inner_factor L (G (L x)) (gradient ψ x)).symm
      _ = 0 := by
        rw [frozen_integral_comp_linear L
          (fun x => inner ℝ (frozenSymmetricPart A (G x)) (gradient φ x)), hz, mul_zero]

/-- The normalized equation and both operator bounds are obtained from the
original ellipticity assumptions, without a symmetry hypothesis. -/
theorem exists_frozen_harmonic_coordinates {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasH1GradientOn u G U)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) U)
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hell : ∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x) (hbound : ‖A‖ ≤ cap) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ‖L.toContinuousLinearMap‖ ≤ Real.sqrt cap ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ ∧
      HasH1GradientOn (u ∘ L) (fun x => L.toContinuousLinearMap.adjoint (G (L x)))
        (L ⁻¹' U) ∧ HasDistributionalLaplacianOn (u ∘ L) (fun _ => 0) (L ⁻¹' U) := by
  obtain ⟨L, hadj, hsquare, hL, hiL⟩ :=
    exists_frozen_normalizing_equiv A hlam hcap hell hbound
  exact ⟨L, hL, hiL, hu.harmonic_comp_frozen_linear hU A hw L (by rw [hadj, hsquare])⟩

end LiquidDrop
