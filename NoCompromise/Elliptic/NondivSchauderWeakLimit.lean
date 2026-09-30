module

public import NoCompromise.Sobolev.WeakCompactness
public import NoCompromise.Sobolev.H1Algebra
public import NoCompromise.Elliptic.Caccioppoli

@[expose] public section

/-!
# Identification of bounded H¹ approximants

Genuine Hilbert weak compactness supplies a weak gradient for the strong L²
limit of a bounded H¹ sequence. Both the limiting gradient bound and the
extracted gradient convergence are retained for passing the weak equation.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Strong convergence of the function components identifies the actual H¹ limit;
no gradient, distributional derivative, or regularity of that limit is a premise. -/
theorem nondiv_hasH1GradientOn_of_bounded_approximants {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {D : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : ∀ j, HasH1GradientOn (u j) (D j) U) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) {C : ℝ}
    (hb : ∀ j, lpNorm (u j) 2 (volume.restrict U) + lpNorm (D j) 2 (volume.restrict U) ≤ C)
    (ht : Tendsto (fun j => eLpNorm (fun x => u j x - f x) 2 (volume.restrict U))
      atTop (𝓝 0)) :
    ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ∃ hG : HasH1GradientOn f G U, lpNorm G 2 (volume.restrict U) ≤ C ∧
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          ∀ ℓ : Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict U) →L[ℝ] ℝ,
            Tendsto (fun j => ℓ ((hu (σ j)).memLp_gradient.toLp (D (σ j)))) atTop
              (𝓝 (ℓ (hG.memLp_gradient.toLp G))) := by
  let v (j : ℕ) := H1Space.ofFunction (u j) (D j) (hu j)
  obtain ⟨w, σ, hσ, hwb, _, htf, htD⟩ := exists_subseq_weakly_tendsto_h1_components v
    (fun j => (H1Space.norm_ofFunction_le _ _ _).trans (hb j))
  have hstrong : Tendsto (fun j => (hu j).memLp_function.toLp (u j)) atTop (𝓝 (hf.toLp f)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u (fun j => (hu j).memLp_function) f hf).mpr
    simpa only [Pi.sub_apply] using! ht
  have he : w.toLp = hf.toLp f := by
    apply ext_inner_left ℝ
    intro q
    exact tendsto_nhds_unique (htf (innerSL ℝ q))
      (((innerSL ℝ q).continuous.tendsto (hf.toLp f)).comp (hstrong.comp hσ.tendsto_atTop))
  have hwe : (w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict U] f := by
    change (w.toLp : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict U] f
    rw [he]
    exact MemLp.coeFn_toLp hf
  have hwf : HasH1GradientOn f w.gradientLp U :=
    w.hasH1GradientOn.congr_ae hwe EventuallyEq.rfl
  refine ⟨w.gradientLp, hwf, ?_, σ, hσ, ?_⟩
  · rw [← H1Space.norm_gradientLp_eq_lpNorm]
    exact w.norm_gradientLp_le.trans hwb
  · intro ℓ
    have htD' := htD ℓ
    change Tendsto (fun j => ℓ ((hu (σ j)).memLp_gradient.toLp (D (σ j)))) atTop
      (𝓝 (ℓ w.gradientLp)) at htD'
    simpa only [Lp.toLp_coeFn] using! htD'


/-- Weak L² convergence is convergence of the actual integral pairing with every L² field. -/
lemma nondiv_tendsto_integral_inner_of_weakLp {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {D : ℕ → X → E} {G P : X → E}
    (hD : ∀ j, MemLp (D j) 2 μ) (hG : MemLp G 2 μ) (hP : MemLp P 2 μ)
    (ht : ∀ ℓ : Lp E 2 μ →L[ℝ] ℝ,
      Tendsto (fun j => ℓ ((hD j).toLp (D j))) atTop (𝓝 (ℓ (hG.toLp G)))) :
    Tendsto (fun j => ∫ x, inner ℝ (P x) (D j x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (P x) (G x) ∂μ)) := by
  have h := ht (innerSL ℝ (hP.toLp P))
  simpa only [innerSL_apply_apply, inner_toLp_eq_integral_inner] using h

/-- A weakly convergent bounded Hilbert sequence can be paired with strongly
convergent test vectors; this handles varying coefficients in weak equations. -/
lemma nondiv_tendsto_inner_of_weak_strong {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : ℕ → E} {u₀ v₀ : E} {C : ℝ} (hb : ∀ j, ‖u j‖ ≤ C)
    (hu : ∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun j => ℓ (u j)) atTop (𝓝 (ℓ u₀)))
    (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun j => inner ℝ (v j) (u j)) atTop (𝓝 (inner ℝ v₀ u₀)) := by
  have herr : Tendsto (fun j => inner ℝ (v j - v₀) (u j)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun j => norm_nonneg _))
      (Eventually.of_forall fun j => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hb j) (norm_nonneg _)))
    simpa only [sub_self, norm_zero, zero_mul] using
      ((hv.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => v₀) atTop (𝓝 v₀))).norm.mul_const C)
  have hfixed := hu (innerSL ℝ v₀)
  have h := herr.add hfixed
  simpa only [inner_sub_left, innerSL_apply_apply, sub_add_cancel, zero_add] using h

end LiquidDrop
