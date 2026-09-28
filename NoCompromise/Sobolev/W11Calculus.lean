import NoCompromise.Sobolev.H1Calculus
import NoCompromise.Sobolev.W11TraceFlat

/-!
# Elementary W¹,¹ calculus

Representative changes and compact cutoff multiplication preserve the actual
weak-gradient identity. The cutoff proof only uses the distributional product
rule and compactly supported integrable factors.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Gradient
namespace LiquidDrop

lemma HasW11GradientOn.memLp_function {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hf : HasW11GradientOn f G U) :
    MemLp f 1 (volume.restrict U) := memLp_one_iff_integrable.mpr hf.integrable_function

lemma HasW11GradientOn.memLp_gradient {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hf : HasW11GradientOn f G U) :
    MemLp G 1 (volume.restrict U) := memLp_one_iff_integrable.mpr hf.integrable_gradient

lemma HasW11GradientOn.congr_ae {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) (hfg : f =ᵐ[volume.restrict U] g)
    (hGH : G =ᵐ[volume.restrict U] H) : HasW11GradientOn g H U :=
  ⟨hf.toHasWeakGradientOn.congr_ae hfg hGH,
    hf.integrable_function.congr hfg, hf.integrable_gradient.congr hGH⟩

theorem HasWeakGradientOn.w11_mul_compact_cutoff {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    HasW11GradientOn (fun x => ζ x * f x)
      (fun x => ζ x • G x + f x • gradient ζ x) univ := by
  refine ⟨hf.mul_compact_cutoff hζ hcζ hsζ, ?_, ?_⟩
  · exact (integrable_mul_compact_factor hf.locallyIntegrable_function
      hζ.continuous hcζ hsζ).integrableOn
  · exact ((integrable_smul_compact_factor_vector hf.locallyIntegrable_gradient
      hζ.continuous hcζ hsζ).add
        (integrable_smul_gradient hf.locallyIntegrable_function hζ hcζ hsζ)).integrableOn

end LiquidDrop
