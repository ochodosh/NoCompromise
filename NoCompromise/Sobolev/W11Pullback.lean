import NoCompromise.Sobolev.H1Chain
import NoCompromise.Sobolev.W11Calculus

/-!
# L¹ estimates for bi-Lipschitz pullback

Both the scalar pullback and adjoint-gradient pullback have explicit L¹ bounds.
The constants are the inverse-Lipschitz volume factor and derivative bound.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Gradient
namespace LiquidDrop

lemma integrable_comp_homeomorph_on {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {K : ℝ≥0} (he : LipschitzWith K e.symm) (hmaps : MapsTo e U V)
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : IntegrableOn g V) :
    IntegrableOn (g ∘ e) U ∧
      (∫ x in U, ‖g (e x)‖) ≤ (K : ℝ) ^ n * ∫ x in V, ‖g x‖ := by
  obtain ⟨hm, hb⟩ := memLp_comp_of_lipschitz_leftInverse hU e.continuous.continuousOn
    he.lipschitzOnWith hmaps (fun x _ => e.symm_apply_apply x)
    (memLp_one_iff_integrable.mpr hg)
  simp only [div_one, ENNReal.toReal_one, ENNReal.rpow_one] at hb
  refine ⟨memLp_one_iff_integrable.mp hm, ?_⟩
  have hfin := (memLp_one_iff_integrable.mpr hg).eLpNorm_ne_top
  have hh := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    toReal_eLpNorm, toReal_eLpNorm, lpNorm_one_eq_integral_norm hm.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hg.1] at hh
  exact hh

lemma integrable_fderiv_adjoint_apply {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {C : ℝ≥0}
    (hΦ : LipschitzWith C Φ)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hG : Integrable G μ) :
    Integrable (fun x => (fderiv ℝ Φ x).adjoint (G x)) μ ∧
      (∫ x, ‖(fderiv ℝ Φ x).adjoint (G x)‖ ∂μ) ≤ C * ∫ x, ‖G x‖ ∂μ := by
  obtain ⟨hm, hb⟩ := memLp_fderiv_adjoint_apply hΦ (memLp_one_iff_integrable.mpr hG)
  refine ⟨memLp_one_iff_integrable.mp hm, ?_⟩
  have hfin := (memLp_one_iff_integrable.mpr hG).eLpNorm_ne_top
  have hh := ENNReal.toReal_mono (by finiteness) hb
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_eLpNorm,
    toReal_eLpNorm, lpNorm_one_eq_integral_norm hm.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hG.1] using hh

lemma integrable_adjoint_comp_homeomorph_on {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    (hmaps : MapsTo e U V)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hG : IntegrableOn G V) :
    IntegrableOn (fun x => (fderiv ℝ e x).adjoint (G (e x))) U ∧
      (∫ x in U, ‖(fderiv ℝ e x).adjoint (G (e x))‖) ≤
        C * (K : ℝ) ^ n * ∫ x in V, ‖G x‖ := by
  obtain ⟨hm, hb⟩ := integrable_comp_homeomorph_on hU e hi hmaps hG
  obtain ⟨hm', hb'⟩ := integrable_fderiv_adjoint_apply he hm
  refine ⟨hm', hb'.trans ?_⟩
  simpa only [mul_assoc, Function.comp_def] using mul_le_mul_of_nonneg_left hb C.coe_nonneg

lemma integrable_comp_homeomorph {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {K : ℝ≥0} (he : LipschitzWith K e.symm)
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : Integrable g) :
    Integrable (g ∘ e) ∧ (∫ x, ‖g (e x)‖) ≤ (K : ℝ) ^ n * ∫ x, ‖g x‖ := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    integrable_comp_homeomorph_on MeasurableSet.univ e he (mapsTo_univ _ _) hg.integrableOn

lemma integrable_adjoint_comp_homeomorph {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hG : Integrable G) :
    Integrable (fun x => (fderiv ℝ e x).adjoint (G (e x))) ∧
      (∫ x, ‖(fderiv ℝ e x).adjoint (G (e x))‖) ≤
        C * (K : ℝ) ^ n * ∫ x, ‖G x‖ := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    integrable_adjoint_comp_homeomorph_on MeasurableSet.univ e he hi
      (mapsTo_univ _ _) hG.integrableOn

end LiquidDrop
