import NoCompromise.Regularity.HarmonicBlowupNormalizedCompactness
import NoCompromise.Regularity.HarmonicBlowupGeometry
import NoCompromise.Regularity.ApproxHarmonicEstimateBounds

/-!
# Harmonic blowup compactness of the actual graph approximations

The base-loss and Dirichlet constants are fixed before the sequence, as they
are for a fixed graph Lipschitz parameter. All phase, height and test-residual
facts are derived from genuine quasiminimality and small excess. The conclusion
is weak H¹ and strong L² convergence only; no gradient-energy convergence is
asserted. This is blueprint `lem:blowup-compactness` in a form that includes every
graph furnished by the approximation theorems, including clamped extensions.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

lemma harmonicBlowup_unit_excess_nonneg (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    0 ≤ cylindricalExcess E hE hmE 0 1 (EuclideanSpace.single 2 1) := by
  simpa only [cylindricalExcess, one_pow, div_one] using
    normalExcessIntegral_nonneg E hE hmE (cylinder 0 1 (EuclideanSpace.single 2 1))
      (EuclideanSpace.single 2 1)

/-- Blueprint `lem:blowup-compactness`, for every genuine graph with fixed
base-loss and Dirichlet constants. Those constants come from the proved graph
approximation theorem for each fixed Lipschitz parameter. -/
theorem harmonic_blowup_compactness {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ A > 0,
      ∀ (E : ℕ → Set AmbientSpace) (ω : ℕ → ℝ) (hE : ∀ j, IsOmegaMinimal (E j) (ω j)),
      (∀ j, (0 : AmbientSpace) ∈ frontier (densityOne (E j))) →
      ∀ (G : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (f : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ j, MeasurableSet (G j)) → (∀ j, G j ⊆ ball 0 (1 / 2)) →
      ∀ hf : ∀ j, LipschitzWith 1 (f j),
      (∀ j, (reducedBoundary (E j) (hE j).locallyFinite (hE j).nullMeasurable ∩
        standardCylinder (1 / 2)) ∩ graphProjectionN 2 ⁻¹' G j = graphMap (f j) '' G j) →
      (∀ j, volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G j) ≤
        B * cylindricalExcess (E j) (hE j).locallyFinite (hE j).nullMeasurable 0 1
          (EuclideanSpace.single 2 1)) →
      (∀ j, (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient (f j) x‖ ^ 2) ≤
        C * cylindricalExcess (E j) (hE j).locallyFinite (hE j).nullMeasurable 0 1
          (EuclideanSpace.single 2 1)) →
      let a := fun j => Real.sqrt (cylindricalExcess (E j) (hE j).locallyFinite
        (hE j).nullMeasurable 0 1 (EuclideanSpace.single 2 1) + ω j)
      (∀ j, 0 < a j) → Tendsto a atTop (𝓝 0) →
      ∃ (v : H1Space (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2))) (σ : ℕ → ℕ)
        (h : EuclideanSpace ℝ (Fin 2) → ℝ),
        StrictMono σ ∧ ‖v‖ ≤ A ∧
        (∀ ℓ : H1Space (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2)) →L[ℝ] ℝ,
          Tendsto (fun j => ℓ (harmonicBlowupClass (f (σ j)) (gradient (f (σ j)))
            (harmonicBlowup_hasH1_lipschitz (hf (σ j))) (a (σ j)))) atTop (𝓝 (ℓ v))) ∧
        Tendsto (fun j => (harmonicBlowupClass (f (σ j)) (gradient (f (σ j)))
          (harmonicBlowup_hasH1_lipschitz (hf (σ j))) (a (σ j))).toLp) atTop (𝓝 v.toLp) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) h (ball 0 (1 / 2)) ∧
        h =ᵐ[volume.restrict (ball 0 (1 / 2))] v ∧
        gradient h =ᵐ[volume.restrict (ball 0 (1 / 2))] v.gradientLp ∧
        HasH1GradientOn h (gradient h) (ball 0 (1 / 2)) ∧
        HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 2)) ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), laplacianN h x = 0) ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
          ‖h x‖ ^ 2 + ‖gradient h x‖ ^ 2) ≤ A ^ 2 ∧
        Tendsto (fun j => ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
          |harmonicBlowupFunction (f (σ j)) (a (σ j)) x - h x| ^ 2) atTop (𝓝 0) := by
  obtain ⟨A, hA, hnorm⟩ := harmonicBlowup_normalized_bound hC
  obtain ⟨ε, hε, _, hgeom⟩ := harmonicBlowup_geometry
  refine ⟨A, hA, fun E ω hE h0 G f hG hGB hf hgraph hbase henergy => ?_⟩
  dsimp only
  let a := fun j => Real.sqrt (cylindricalExcess (E j) (hE j).locallyFinite
    (hE j).nullMeasurable 0 1 (EuclideanSpace.single 2 1) + ω j)
  intro ha hta
  have hasq (j : ℕ) : (a j) ^ 2 = cylindricalExcess (E j) (hE j).locallyFinite
      (hE j).nullMeasurable 0 1 (EuclideanSpace.single 2 1) + ω j :=
    Real.sq_sqrt (add_nonneg (harmonicBlowup_unit_excess_nonneg _ _ _) (hE j).nonneg)
  have he (j : ℕ) : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
      ‖gradient (f j) x‖ ^ 2) ≤ C * (a j) ^ 2 := by
    rw [hasq]
    exact (henergy j).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hE j).nonneg) hC)
  let u (j : ℕ) := harmonicBlowupClass (f j) (gradient (f j))
    (harmonicBlowup_hasH1_lipschitz (hf j)) (a j)
  have hu (j : ℕ) : ‖u j‖ ≤ A := hnorm _ _ _ _ (ha j) (he j)
  have hsmall : ∀ᶠ j in atTop, cylindricalExcess (E j) (hE j).locallyFinite
      (hE j).nullMeasurable 0 1 (EuclideanSpace.single 2 1) + ω j ≤ ε := by
    have ht := hta.pow 2
    simp only [zero_pow (by norm_num : 2 ≠ 0)] at ht
    filter_upwards [ht.eventually (Iio_mem_nhds hε)] with j hj
    rw [← hasq]
    exact hj.le
  have htres (φ : EuclideanSpace ℝ (Fin 2) → ℝ) (hφ : ContDiff ℝ 1 φ)
      (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ ball 0 (1 / 2)) :
      Tendsto (fun j => ∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
        inner ℝ ((u j).gradientLp x) (gradient φ x)) atTop (𝓝 0) := by
    have hcg : HasCompactSupport (gradient φ) :=
      hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset _)
    obtain ⟨M, hMb⟩ := hcg.exists_bound_of_continuous (continuous_gradient_of_contDiff hφ)
    have hM : 0 ≤ M := (norm_nonneg (gradient φ 0)).trans (hMb 0)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (show Tendsto (fun j => ((C + 2 * B + 2 + Real.pi) * a j) * M) atTop (𝓝 0) by
        simpa only [mul_zero, zero_mul] using (hta.const_mul _).mul_const M)
    filter_upwards [hsmall] with j hj
    obtain ⟨hphase, hheight, hexcess⟩ := hgeom (E j) (ω j) (hE j) (h0 j) hj
    have hr := approxHarmonic_residual_of_bounds (hE j) hphase hheight (hf j) (by norm_num)
      (hG j) (hGB j) (hgraph j) hB hC (hbase j) (henergy j) hexcess hφ hcφ hsφ hM hMb
    rw [← hasq] at hr
    simpa only [Real.norm_eq_abs] using
      harmonicBlowup_normalized_residual_bound (harmonicBlowup_hasH1_lipschitz (hf j))
        (ha j) (C + 2 * B + 2 + Real.pi) M φ hr
  obtain ⟨v, σ, h, hσ, hv, hw, ht, hc, heq, hg, hh1, hd, hz, henergyh, herr⟩ :=
    harmonicBlowup_compactness 0 (by norm_num : (0 : ℝ) < 1 / 2) u hu htres
  refine ⟨v, σ, h, hσ, hv, hw, ht, hc, heq, hg, hh1, hd, hz, henergyh, ?_⟩
  apply herr.congr'
  apply Eventually.of_forall
  intro j
  apply integral_congr_ae
  filter_upwards [harmonicBlowupClass_coeFn (f (σ j)) (gradient (f (σ j)))
    (harmonicBlowup_hasH1_lipschitz (hf (σ j))) (a (σ j))] with x hx
  rw [hx]

end LiquidDrop
