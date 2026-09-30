module

public import NoCompromise.Elliptic.BoundaryHolderTrace
public import NoCompromise.Elliptic.CampanatoGrowthComparison

@[expose] public section

/-! Tangential translation preserves the actual localized flat trace and the
original compact-test weak equation. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_graphAppend_translate {k : ℕ} (x z : EuclideanSpace ℝ (Fin k)) (t : ℝ) :
    graphAppendN x t + graphAppendN z 0 = graphAppendN (x + z) t := by
  simp only [graphAppendN, zero_smul, add_zero, map_add]
  abel

lemma boundary_flatTrace_translate {k : ℕ}
    (f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)))
    (z x : EuclideanSpace ℝ (Fin k)) :
    flatTraceFunction (fun y => f (y + graphAppendN z 0))
      (fun y => G (y + graphAppendN z 0)) x = flatTraceFunction f G (x + z) := by
  simp only [flatTraceFunction, flatTraceIntegrand, boundary_graphAppend_translate]

lemma boundary_gradient_translate {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (a x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => φ (y + a)) x = gradient φ (x + a) := by
  simp only [gradient, fderiv_comp_add_right]

/-- This trace translation is an identity of the original normal-average trace,
not an assumed boundary restriction law. -/
theorem HasZeroFlatTraceOn.translate {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    {W V : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hT : HasZeroFlatTraceOn f G W) (z : EuclideanSpace ℝ (Fin k))
    (hmap : ∀ x ∈ V, x + graphAppendN z 0 ∈ W) :
    HasZeroFlatTraceOn (fun y => f (y + graphAppendN z 0))
      (fun y => G (y + graphAppendN z 0)) V := by
  let c := graphAppendN z 0
  intro ζ hζ hcζ hsζ
  let η := fun x => ζ (x + -c)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := hζ.comp (contDiff_id.add contDiff_const)
  have hcη : HasCompactSupport η := hcζ.comp_homeomorph (Homeomorph.addRight (-c))
  have hsη : tsupport η ⊆ W := by
    intro x hx
    change x ∈ tsupport (ζ ∘ Homeomorph.addRight (-c)) at hx
    rw [tsupport_comp_eq_preimage] at hx
    have hxV : x + -c ∈ V := hsζ hx
    simpa only [c, add_assoc, neg_add_cancel, add_zero] using hmap (x + -c) hxV
  have ht := (measurePreserving_add_right volume z).quasiMeasurePreserving.ae_eq_comp
    (hT η hη hcη hsη)
  have hgrad (x : EuclideanSpace ℝ (Fin (k + 1))) : gradient η (x + c) = gradient ζ x := by
    rw [boundary_gradient_translate]
    simp only [add_neg_cancel_right]
  have he (x : EuclideanSpace ℝ (Fin k)) :
      boundaryLocalizedFlatTrace (fun y => f (y + c)) (fun y => G (y + c)) ζ x =
        boundaryLocalizedFlatTrace f G η (x + z) := by
    have hh := boundary_flatTrace_translate (fun y => η y * f y)
      (fun y => η y • G y + f y • gradient η y) z x
    have hfE : (fun y => η (y + c) * f (y + c)) = fun y => ζ y * f (y + c) := by
      funext y
      simp only [η, add_neg_cancel_right]
    have hGE : (fun y => η (y + c) • G (y + c) + f (y + c) • gradient η (y + c)) =
        fun y => ζ y • G (y + c) + f (y + c) • gradient ζ y := by
      funext y
      rw [hgrad]
      simp only [η, add_neg_cancel_right]
    change flatTraceFunction _ _ x = _ at hh
    change flatTraceFunction _ _ x = _
    rw [← hfE, ← hGE]
    exact hh
  filter_upwards [ht] with x hx
  rw [he]
  exact hx

/-- Translation of the genuine C¹ compact-test divergence equation. -/
theorem IsWeakDivergenceEquationOn.boundary_translate {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {F G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hw : IsWeakDivergenceEquationOn A F G U) (c : EuclideanSpace ℝ (Fin n))
    (hmap : ∀ x ∈ V, x + c ∈ U) :
    IsWeakDivergenceEquationOn (fun x => A (x + c)) (fun x => F (x + c))
      (fun x => G (x + c)) V := by
  intro φ hφ hcφ hsφ
  let ψ := fun x => φ (x + -c)
  have hψ : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph (Homeomorph.addRight (-c))
  have hsψ : tsupport ψ ⊆ U := by
    intro x hx
    change x ∈ tsupport (φ ∘ Homeomorph.addRight (-c)) at hx
    rw [tsupport_comp_eq_preimage] at hx
    simpa only [add_assoc, neg_add_cancel, add_zero] using hmap (x + -c) (hsφ hx)
  have ht := hw ψ hψ hcψ hsψ
  have hgrad (x) : gradient ψ x = gradient φ (x + -c) := boundary_gradient_translate φ (-c) x
  simp_rw [hgrad] at ht
  rw [← integral_add_right_eq_self
    (fun x => inner ℝ (A x (F x) - G x) (gradient φ (x + -c))) c] at ht
  simpa only [add_neg_cancel_right] using ht

end LiquidDrop
