module

public import NoCompromise.Sobolev.H1ChartExtension
public import NoCompromise.Sobolev.H1Algebra

@[expose] public section

/-!
# Restriction and cutoff operators on genuine H¹ spaces
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma HasH1GradientOn.restrict_lpNorm_le {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hVU : V ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) :
    lpNorm f 2 (volume.restrict V) + lpNorm G 2 (volume.restrict V) ≤
      lpNorm f 2 (volume.restrict U) + lpNorm G 2 (volume.restrict U) := by
  have h := hf.mono hVU
  rw [← toReal_eLpNorm, ← toReal_eLpNorm,
    ← toReal_eLpNorm, ← toReal_eLpNorm]
  exact add_le_add
    (ENNReal.toReal_mono hf.memLp_function.eLpNorm_ne_top
      (eLpNorm_mono_measure f (Measure.restrict_mono hVU le_rfl)))
    (ENNReal.toReal_mono hf.memLp_gradient.eLpNorm_ne_top
      (eLpNorm_mono_measure G (Measure.restrict_mono hVU le_rfl)))

namespace H1Space

def restrictionCLM {n : ℕ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) : H1Space U →L[ℝ] H1Space V :=
  liftBoundedLinearMap hV LinearMap.id 1 zero_le_one
    (fun _ _ hf => ⟨_, hf.mono hVU, by
      simpa only [LinearMap.id_apply, one_mul] using hf.restrict_lpNorm_le hVU⟩) hU

lemma restrictionCLM_ofFunction {n : ℕ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) :
    restrictionCLM hU hV hVU (ofFunction f G hf) = ofFunction f G (hf.mono hVU) := by
  rw [restrictionCLM, liftBoundedLinearMap_ofFunction]
  apply ext_ae hV
  exact (coeFn_ofH1Function _ _).trans (coeFn_ofFunction _ _ _).symm

end H1Space

def h1CutoffLinearMap {n : ℕ} (ζ : EuclideanSpace ℝ (Fin n) → ℝ) :
    (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ) where
  toFun f x := ζ x * f x
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' c f := by ext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma h1CutoffLinearMap_bound {n : ℕ} {ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : HasH1GradientOn f G univ) :
    ∃ H, HasH1GradientOn (h1CutoffLinearMap ζ f) H univ ∧
      lpNorm (h1CutoffLinearMap ζ f) 2 (volume.restrict univ) +
        lpNorm H 2 (volume.restrict univ) ≤ (A + B) *
          (lpNorm f 2 (volume.restrict univ) + lpNorm G 2 (volume.restrict univ)) := by
  have h := hf.mul_compact_cutoff_lpNorm MeasurableSet.univ hζ hcζ
    (subset_univ _) hA hB hbζ hbgrad
  exact ⟨_, h.1, by simpa only [Measure.restrict_univ, h1CutoffLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk] using h.2⟩

namespace H1Space

def cutoffCLM {n : ℕ} {ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    H1Space (univ : Set (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      H1Space (univ : Set (EuclideanSpace ℝ (Fin n))) :=
  liftBoundedLinearMap isOpen_univ (h1CutoffLinearMap ζ) (A + B) (add_nonneg hA hB)
    (h1CutoffLinearMap_bound hζ hcζ hA hB hbζ hbgrad) isOpen_univ

lemma cutoffCLM_ofFunction {n : ℕ} {ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) :
    cutoffCLM hζ hcζ hA hB hbζ hbgrad (ofFunction f G hf) =
      ofFunction (fun x => ζ x * f x) (fun x => ζ x • G x + f x • gradient ζ x)
        (hf.mul_compact_cutoff MeasurableSet.univ hζ hcζ (subset_univ _) hbζ hbgrad).1 := by
  rw [cutoffCLM, liftBoundedLinearMap_ofFunction]
  apply ext_ae isOpen_univ
  exact (coeFn_ofH1Function _ _).trans (coeFn_ofFunction _ _ _).symm

end H1Space
end LiquidDrop
