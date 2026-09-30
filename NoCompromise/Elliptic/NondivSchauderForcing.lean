module

public import NoCompromise.Elliptic.NondivSchauderDifferenceEquation
public import NoCompromise.Elliptic.NondivSchauderTests

@[expose] public section

/-!
# The actual difference-quotient vector datum

After representing δₕg as the divergence of H, the differentiated equation has
vector datum H−(δₕA)D. The lemmas here establish the product Hölder bound and
combine the two actual distributional identities. The primitive H is supplied
separately by the segment-integral construction.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_holder_clm_apply {E F G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} {A : E → F →L[ℝ] G} {D : E → F} {U : Set E}
    (hA : HasFiniteHolderNormOn α A U) (hD : HasFiniteHolderNormOn α D U) :
    HasFiniteHolderNormOn α (fun x => A x (D x)) U ∧
      holderNorm α (fun x => A x (D x)) U ≤ 3 * holderNorm α A U * holderNorm α D U := by
  obtain ⟨hh, hb⟩ := nondiv_holder_bilinear hA hD (ContinuousLinearMap.id ℝ (F →L[ℝ] G))
  refine ⟨hh, hb.trans ?_⟩
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := F →L[ℝ] G))
      (by norm_num : (0 : ℝ) ≤ 3)) hA.norm_nonneg) hD.norm_nonneg
  simpa only [mul_one] using h

/-- The exact vector correction obtained from the discrete coefficient product rule. -/
def nondivDifferenceForcing {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (i : Fin n) (h : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  H x - coordinateDifferenceQuotient i h A x (D x)

/-- Uniform Hölder control of the vector datum: the coefficient quotient costs
only DA, and introduces no negative power of the step size. -/
theorem nondivDifferenceForcing_holder {n : ℕ} {α : ℝ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hA : HasC1HolderOn α A U) (hD : HasFiniteHolderNormOn α D U)
    (hH : HasFiniteHolderNormOn α H V) (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (h • EuclideanSpace.single i 1) ∈ U) :
    HasFiniteHolderNormOn α (nondivDifferenceForcing H A D i h) V ∧
      holderNorm α (nondivDifferenceForcing H A D i h) V ≤ holderNorm α H V +
        3 * holderNorm α (fderiv ℝ A) U * holderNorm α D U := by
  have hVU : V ⊆ U := by
    intro x hx
    simpa only [zero_smul, add_zero] using hseg x hx 0 (by simp)
  obtain ⟨hδ, hδb⟩ := nondiv_coordinateDifferenceQuotient_holder hU hA i hh hseg
  obtain ⟨hDV, hDVb⟩ := schauder_holder_mono hD hVU
  obtain ⟨hP, hPb⟩ := nondiv_holder_clm_apply hδ hDV
  obtain ⟨hF, hFb⟩ := nondiv_holder_sub hH hP
  refine ⟨hF, hFb.trans (add_le_add le_rfl (hPb.trans ?_))⟩
  exact mul_le_mul (mul_le_mul_of_nonneg_left hδb (by norm_num)) hDVb
    hDV.norm_nonneg (mul_nonneg (by norm_num) hA.derivative_holder.norm_nonneg)

/-- Combining the discrete equation with the actual divergence primitive gives
precisely the weak equation required by Caccioppoli and Campanato. -/
theorem nondiv_difference_weakDivergenceEquation {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (he : IsWeakScalarDivergenceEquationOn A D g U) (hU : IsOpen U) (hV : IsOpen V)
    (hA : ContinuousOn A U) (hD : ContinuousOn D U) (hg : ContinuousOn g U)
    (hH : ContinuousOn H V) (hVU : V ⊆ U) (i : Fin n) (h : ℝ)
    (hmap : ∀ x ∈ V, x + h • EuclideanSpace.single i 1 ∈ U)
    (hprimitive : IsWeakScalarDivergenceEquationOn
      (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) H
      (coordinateDifferenceQuotient i h g) V)
    (hF : MemLp (fun x => A (x + h • EuclideanSpace.single i 1)
      (coordinateDifferenceQuotient i h D x) - nondivDifferenceForcing H A D i h x)
      2 (volume.restrict V)) :
    IsWeakDivergenceEquationOn (fun x => A (x + h • EuclideanSpace.single i 1))
      (coordinateDifferenceQuotient i h D) (nondivDifferenceForcing H A D i h) V := by
  apply nondiv_weakDivergenceEquationOn_of_smooth_tests hV hF
  intro φ hφ hcφ hsφ
  have heq := he.coordinateDifferenceQuotient hU hV hA hD hg hVU i h hmap φ hφ hcφ hsφ
  have hp := hprimitive φ hφ hcφ hsφ
  simp only [ContinuousLinearMap.id_apply] at hp
  let δF := coordinateDifferenceQuotient i h (fun x => A x (D x))
  have hcδ : ContinuousOn δF V := by
    have ht := ((hA.clm_apply hD).comp
      (continuous_id.add continuous_const).continuousOn hmap).sub
        ((hA.clm_apply hD).mono hVU)
    simpa only [δF, coordinateDifferenceQuotient] using! ht.const_smul h⁻¹
  have hiδ := nondiv_integrable_flux_test hV hcδ (hφ.of_le (by simp)) hcφ hsφ
  have hiH := nondiv_integrable_flux_test hV hH (hφ.of_le (by simp)) hcφ hsφ
  have hflux (x : EuclideanSpace ℝ (Fin n)) :
      A (x + h • EuclideanSpace.single i 1) (coordinateDifferenceQuotient i h D x) -
        nondivDifferenceForcing H A D i h x = δF x - H x := by
    dsimp [nondivDifferenceForcing, δF]
    rw [nondiv_differenceQuotient_product]
    abel
  have hδeq : (∫ x, inner ℝ (δF x) (gradient φ x)) =
      -(∫ x, φ x * coordinateDifferenceQuotient i h g x) := by
    simpa only [δF, nondiv_differenceQuotient_product] using heq
  simp_rw [hflux, inner_sub_left]
  rw [integral_sub hiδ hiH, hδeq, hp, sub_self]

end LiquidDrop
