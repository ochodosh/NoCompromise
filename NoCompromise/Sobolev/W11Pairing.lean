module

public import NoCompromise.Sobolev.W11Space

@[expose] public section

/-!
# Continuous integration against bounded vector fields

The actual integral pairing of an L¹ class with a bounded measurable field is
a continuous linear functional. The W¹,¹ gradient projection is continuous.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure X}

lemma integrable_inner_of_ae_bound {G V : X → E} (hG : Integrable G μ)
    (hV : AEStronglyMeasurable V μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖V x‖ ≤ C) :
    Integrable (fun x => inner ℝ (G x) (V x)) μ := by
  apply (hG.norm.mul_const C).mono' (hG.1.inner hV)
  filter_upwards [hC] with x hx
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left hx (norm_nonneg _))

def lpOneInnerPairingLinear {V : X → E} (hV : AEStronglyMeasurable V μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖V x‖ ≤ C) : Lp E 1 μ →ₗ[ℝ] ℝ where
  toFun f := ∫ x, inner ℝ (f x) (V x) ∂μ
  map_add' f g := by
    have hf := memLp_one_iff_integrable.mp (Lp.memLp f)
    have hg := memLp_one_iff_integrable.mp (Lp.memLp g)
    calc
      _ = ∫ x, inner ℝ (f x) (V x) + inner ℝ (g x) (V x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with x hx
        rw [hx, Pi.add_apply, inner_add_left]
      _ = _ := integral_add (integrable_inner_of_ae_bound hf hV hC)
        (integrable_inner_of_ae_bound hg hV hC)
  map_smul' c f := by
    calc
      _ = ∫ x, c • inner ℝ (f x) (V x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [hx, Pi.smul_apply, real_inner_smul_left, smul_eq_mul]
      _ = _ := integral_smul c _

lemma norm_lpOneInnerPairingLinear_le {V : X → E} (hV : AEStronglyMeasurable V μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖V x‖ ≤ C) (f : Lp E 1 μ) :
    ‖lpOneInnerPairingLinear hV hC f‖ ≤ C * ‖f‖ := by
  have hf := memLp_one_iff_integrable.mp (Lp.memLp f)
  calc
    _ ≤ ∫ x, ‖inner ℝ (f x) (V x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * ‖f x‖ ∂μ := by
      apply integral_mono_ae (integrable_inner_of_ae_bound hf hV hC).norm
        (hf.norm.const_mul C)
      filter_upwards [hC] with x hx
      exact (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (f x)])
    _ = C * ‖f‖ := by
      rw [integral_const_mul, Lp.norm_def, toReal_eLpNorm,
        lpNorm_one_eq_integral_norm (Lp.aestronglyMeasurable f)]

def lpOneInnerPairing {V : X → E} (hV : AEStronglyMeasurable V μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖V x‖ ≤ C) : Lp E 1 μ →L[ℝ] ℝ :=
  (lpOneInnerPairingLinear hV hC).mkContinuous C (norm_lpOneInnerPairingLinear_le hV hC)

lemma lpOneInnerPairing_apply {V : X → E} (hV : AEStronglyMeasurable V μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖V x‖ ≤ C) (f : Lp E 1 μ) :
    lpOneInnerPairing hV hC f = ∫ x, inner ℝ (f x) (V x) ∂μ := rfl

def W11Space.gradientCLM {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} :
    W11Space U →L[ℝ] Lp (EuclideanSpace ℝ (Fin n)) 1 (volume.restrict U) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (w11Submodule U).subtypeL

lemma W11Space.gradientCLM_apply {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (u : W11Space U) : gradientCLM u = u.gradientLp := rfl

end LiquidDrop
