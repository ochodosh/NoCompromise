import NoCompromise.Elliptic.SobolevChainBounds

/-!
# Quantitative higher weak derivatives of harmonic functions

The proved interior H¹ energy estimate is iterated on harmonic gradient
coordinates. This constructs the genuine Sobolev derivative tree with uniform
L² bounds, after which the quantitative Sobolev estimate controls classical
iterated derivative operator norms.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma harmonicDerivative_lpNorm_component_le {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : MemLp G 2 μ) (i : Fin n) : lpNorm (fun x => G x i) 2 μ ≤ lpNorm G 2 μ := by
  calc
    _ ≤ lpNorm (fun x => ‖G x‖) 2 μ :=
      lpNorm_mono_real hG.norm (fun x => PiLp.norm_apply_le (G x) i)
    _ = lpNorm G 2 μ := lpNorm_norm hG.aestronglyMeasurable 2

/-- Iterating the quantitative interior energy estimate constructs the actual
weak derivative tree with a uniform L² bound of every finite order. -/
theorem interior_harmonic_derivative_data_bound {n : ℕ} (k : ℕ)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ),
      HasDistributionalLaplacianOn u (fun _ => 0) (ball z R) →
      MemLp u 2 (volume.restrict (ball z R)) →
      ∃ d : SobolevDerivativeData (ball z r) k u,
        d.norm ≤ C * lpNorm u 2 (volume.restrict (ball z R)) := by
  classical
  induction k generalizing r R with
  | zero =>
    refine ⟨1, zero_lt_one, fun u _ hu => ?_⟩
    refine ⟨.zero (hu.mono_measure (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl)), ?_⟩
    simpa only [SobolevDerivativeData.norm, one_mul] using
      poisson_lpNorm_mono_measure hu (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl)
  | succ k ih =>
    let s := (r + R) / 2
    have hrs : r < s := by dsimp [s]; linarith
    have hsR : s < R := by dsimp [s]; linarith
    obtain ⟨C₀, hC₀, hb₀⟩ := exists_poisson_interior_h1_bound z hsR
    obtain ⟨C₁, hC₁, hb₁⟩ := ih hrs
    refine ⟨(1 + (n : ℝ) * C₁) * C₀, by positivity, fun u h hu => ?_⟩
    obtain ⟨G, hG, hbG⟩ := hb₀ u (fun _ => 0) h hu
      (HasH1GradientOn.zero (ball z R)).memLp_function
    simp only [show (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)) = 0 from rfl,
      lpNorm_zero, add_zero] at hbG
    have hi (i : Fin n) : MemLp (fun x => G x i) 2 (volume.restrict (ball z s)) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hG.memLp_gradient
    have hhi (i : Fin n) : HasDistributionalLaplacianOn (fun x => G x i)
        (fun _ => 0) (ball z s) := by
      simpa using (h.mono (ball_subset_ball hsR.le)).gradient_component
        hG.toHasWeakGradientOn (HasH1GradientOn.zero (ball z s)).toHasWeakGradientOn i
    choose d hd using fun i => hb₁ (fun x => G x i) (hhi i) (hi i)
    refine ⟨.succ G (hG.mono (ball_subset_ball hrs.le)) d, ?_⟩
    have hfirst : lpNorm u 2 (volume.restrict (ball z r)) +
        lpNorm G 2 (volume.restrict (ball z r)) ≤
        C₀ * lpNorm u 2 (volume.restrict (ball z R)) :=
      (add_le_add
        (poisson_lpNorm_mono_measure hG.memLp_function
          (Measure.restrict_mono (ball_subset_ball hrs.le) le_rfl))
        (poisson_lpNorm_mono_measure hG.memLp_gradient
          (Measure.restrict_mono (ball_subset_ball hrs.le) le_rfl))).trans hbG
    have hGbound : lpNorm G 2 (volume.restrict (ball z s)) ≤
        C₀ * lpNorm u 2 (volume.restrict (ball z R)) := by
      linarith only [hbG, (lpNorm_nonneg : 0 ≤ lpNorm u 2 (volume.restrict (ball z s)))]
    have htail : (∑ i, (d i).norm) ≤ (n : ℝ) * C₁ *
        (C₀ * lpNorm u 2 (volume.restrict (ball z R))) := by
      calc
        _ ≤ ∑ _ : Fin n, C₁ * (C₀ * lpNorm u 2 (volume.restrict (ball z R))) := by
          apply Finset.sum_le_sum
          intro i _
          exact (hd i).trans (mul_le_mul_of_nonneg_left
            ((harmonicDerivative_lpNorm_component_le hG.memLp_gradient i).trans hGbound) hC₁.le)
        _ = _ := by simp [mul_assoc]
    change lpNorm u 2 (volume.restrict (ball z r)) + lpNorm G 2 (volume.restrict (ball z r)) +
      ∑ i, (d i).norm ≤ _
    nlinarith only [hfirst, htail]

/-- Genuine higher weak derivatives control all classical harmonic derivatives,
with constants chosen from dimension, order, center and the two radii alone. -/
theorem interior_harmonic_classical_derivative_bound {n k : ℕ} (hn : n < 4)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u w : EuclideanSpace ℝ (Fin n) → ℝ),
      HasDistributionalLaplacianOn u (fun _ => 0) (ball z R) →
      MemLp u 2 (volume.restrict (ball z R)) → ContDiff ℝ k w →
      w =ᵐ[volume.restrict (ball z R)] u →
      ∀ j ≤ k, ∀ x ∈ ball z r,
        ‖iteratedFDeriv ℝ j w x‖ ≤ C * lpNorm u 2 (volume.restrict (ball z R)) := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  obtain ⟨C₀, hC₀, hb₀⟩ := interior_harmonic_derivative_data_bound (k + 2) z hsR
  obtain ⟨C₁, hC₁, hb₁⟩ := sobolevChain_classical_derivative_bound (k := k) hn z hrs
  refine ⟨C₁ * C₀, mul_pos hC₁ hC₀, fun u w h hu hw he j hj x hx => ?_⟩
  obtain ⟨d, hd⟩ := hb₀ u h hu
  exact (hb₁ u w d hw
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hsR.le) he) j hj x hx).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hd hC₁.le])

end LiquidDrop
