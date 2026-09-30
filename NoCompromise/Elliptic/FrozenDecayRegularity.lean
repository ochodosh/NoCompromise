module

public import NoCompromise.Elliptic.FrozenDecayChange
public import NoCompromise.Elliptic.HarmonicDerivative

@[expose] public section

/-! Smooth representatives and quantitative gradient pullback for frozen
solutions. The representative is obtained from the genuine transformed weak
Laplacian; its classical gradient is identified by weak-gradient uniqueness. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma frozen_gradient_pullback_lpNorm_le {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasH1GradientOn u G V)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (hL : LipschitzWith C L) (hiL : LipschitzWith K L.symm)
    (hmaps : MapsTo L U V) :
    lpNorm (fun x => L.toContinuousLinearMap.adjoint (G (L x))) 2 (volume.restrict U) ≤
      (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2) * lpNorm G 2 (volume.restrict V) := by
  obtain ⟨hh, _, hb⟩ := hu.comp_homeomorph_on hU hV L.toHomeomorph hL hiL hmaps
  change HasH1GradientOn (u ∘ L)
    (fun x => (fderiv ℝ L x).adjoint (G (L x))) U at hh
  change eLpNorm (fun x => (fderiv ℝ L x).adjoint (G (L x))) 2 (volume.restrict U) ≤ _ at hb
  simp only [ContinuousLinearEquiv.fderiv] at hh hb
  have hGf := hu.memLp_gradient.eLpNorm_ne_top
  have hh' := ENNReal.toReal_mono (by finiteness) hb
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal,
    toReal_eLpNorm, toReal_eLpNorm] using hh'

/-- A distributionally harmonic H¹ function has a smooth representative with
the same actual weak gradient. -/
theorem exists_harmonic_smooth_representative_with_gradient {n : ℕ} (hn : n < 4)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasH1GradientOn u G U) (h : HasDistributionalLaplacianOn u (fun _ => 0) U) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v U ∧ v =ᵐ[volume.restrict U] u ∧
      gradient v =ᵐ[volume.restrict U] G ∧ HasH1GradientOn v (gradient v) U ∧
      HasDistributionalLaplacianOn v (fun _ => 0) U := by
  obtain ⟨v, hv, he, _, _⟩ := h.exists_smooth_mean_value hn hU (fun x hx => by
    obtain ⟨r, hr, hs⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    exact ⟨r, hr, hs, hu.memLp_function.mono_measure (Measure.restrict_mono hs le_rfl)⟩)
  have hvw := hasWeakGradientOn_of_contDiffOn hU (hv.of_le (by simp))
  have hg := hvw.unique hU (hu.toHasWeakGradientOn.congr_ae he.symm EventuallyEq.rfl)
  exact ⟨v, hv, he, hg, ⟨hvw, hu.memLp_function.ae_eq he.symm,
    hu.memLp_gradient.ae_eq hg.symm⟩, h.congr_ae he.symm EventuallyEq.rfl⟩

lemma frozen_ae_comp_linear_inverse {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {v u : EuclideanSpace ℝ (Fin n) → ℝ}
    (he : v =ᵐ[volume.restrict (L ⁻¹' U)] (u ∘ L)) :
    (v ∘ L.symm) =ᵐ[volume.restrict U] u := by
  have hq := Measure.LinearMap.quasiMeasurePreserving volume L.symm.toLinearEquiv.toLinearMap
    L.symm.toLinearEquiv.isUnit_det'.ne_zero
  have hm : MapsTo L.symm U (L ⁻¹' U) := by
    intro x hx
    change L (L.symm x) ∈ U
    simpa only [L.apply_symm_apply] using hx
  have hq' : Measure.QuasiMeasurePreserving L.symm (volume.restrict U)
      (volume.restrict (L ⁻¹' U)) := hq.restrict hm
  filter_upwards [hq'.ae he] with x hx
  simpa only [Function.comp_apply, L.apply_symm_apply] using hx

/-- Frozen elliptic H¹ functions admit smooth representatives in dimensions
two and three, retaining the original weak gradient almost everywhere. -/
theorem exists_frozen_smooth_representative {n : ℕ} (hn : n < 4)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasH1GradientOn u G U)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hw : IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) U)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) w U ∧ w =ᵐ[volume.restrict U] u ∧
      gradient w =ᵐ[volume.restrict U] G := by
  obtain ⟨L, _, _, hH, hΔ⟩ := exists_frozen_harmonic_coordinates hU hu A hw
    hlam (norm_nonneg A) hell le_rfl
  have hV : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  obtain ⟨v, hv, he, _, _, _⟩ :=
    exists_harmonic_smooth_representative_with_gradient hn hV hH hΔ
  let w := v ∘ L.symm
  have hmaps : MapsTo L.symm U (L ⁻¹' U) := by
    intro x hx
    change L (L.symm x) ∈ U
    simpa only [L.apply_symm_apply] using hx
  have hwc : ContDiffOn ℝ (⊤ : ℕ∞) w U :=
    hv.comp L.symm.contDiff.contDiffOn hmaps
  have hew : w =ᵐ[volume.restrict U] u := frozen_ae_comp_linear_inverse L he
  refine ⟨w, hwc, hew, ?_⟩
  exact (hasWeakGradientOn_of_contDiffOn hU (hwc.of_le (by simp))).unique hU
    (hu.toHasWeakGradientOn.congr_ae hew.symm EventuallyEq.rfl)

end LiquidDrop
