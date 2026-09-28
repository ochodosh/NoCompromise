import NoCompromise.Sobolev.W11Chain
import NoCompromise.Sobolev.W11FlatExtension

/-!
# Quantitative W¹,¹ cutoff, pullback and reflection bounds

The ordinary sum of the L¹ norms is controlled explicitly at each step of the
boundary-chart extension. All constants are independent of the input function.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem HasW11GradientOn.mul_compact_cutoff {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U)
    {A B : ℝ} (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    HasW11GradientOn (fun x => ζ x * f x)
      (fun x => ζ x • G x + f x • gradient ζ x) univ ∧
      HasCompactSupport (fun x => ζ x * f x) ∧
      eLpNorm (fun x => ζ x * f x) 1 volume ≤
        ENNReal.ofReal A * eLpNorm f 1 (volume.restrict U) ∧
      eLpNorm (fun x => ζ x • G x + f x • gradient ζ x) 1 volume ≤
        ENNReal.ofReal A * eLpNorm G 1 (volume.restrict U) +
          ENNReal.ofReal B * eLpNorm f 1 (volume.restrict U) := by
  have hmf := memLp_smul_supported_scalar hU hf.memLp_function hζ.continuous hsζ hbζ
  have hmG := memLp_smul_supported_scalar hU hf.memLp_gradient hζ.continuous hsζ hbζ
  have hmgrad := memLp_smul_supported_vector hU hf.memLp_function
    (continuous_gradient_of_contDiff hζ) ((tsupport_gradient_subset ζ).trans hsζ) hbgrad
  have hmadd := hmG.1.add hmgrad.1
  refine ⟨⟨hf.toHasWeakGradientOn.mul_compact_cutoff hζ hcζ hsζ, ?_, ?_⟩,
    hcζ.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left, hmf.2, ?_⟩
  · simpa only [smul_eq_mul, IntegrableOn, Measure.restrict_univ] using
      memLp_one_iff_integrable.mp hmf.1
  · exact (memLp_one_iff_integrable.mp hmadd).integrableOn
  · exact (eLpNorm_add_le (by norm_num)).trans
      (add_le_add hmG.2 hmgrad.2)

theorem HasW11GradientOn.mul_compact_cutoff_lpNorm {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    HasW11GradientOn (fun x => ζ x * f x)
      (fun x => ζ x • G x + f x • gradient ζ x) univ ∧
      lpNorm (fun x => ζ x * f x) 1 volume +
          lpNorm (fun x => ζ x • G x + f x • gradient ζ x) 1 volume ≤
        (A + B) * (lpNorm f 1 (volume.restrict U) + lpNorm G 1 (volume.restrict U)) := by
  have hc := hf.mul_compact_cutoff hU hζ hcζ hsζ hbζ hbgrad
  have hff := hf.memLp_function.eLpNorm_ne_top
  have hfg := hf.memLp_gradient.eLpNorm_ne_top
  have hm : MemLp (fun x => ζ x * f x) 1 volume := by
    simpa only [Measure.restrict_univ] using hc.1.memLp_function
  have hmG : MemLp (fun x => ζ x • G x + f x • gradient ζ x) 1 volume := by
    simpa only [Measure.restrict_univ] using hc.1.memLp_gradient
  have hAfin : ENNReal.ofReal A * eLpNorm G 1 (volume.restrict U) ≠ ∞ := by finiteness
  have hBfin : ENNReal.ofReal B * eLpNorm f 1 (volume.restrict U) ≠ ∞ := by finiteness
  have hbf := ENNReal.toReal_mono
    (by finiteness : ENNReal.ofReal A * eLpNorm f 1 (volume.restrict U) ≠ ∞) hc.2.2.1
  have hbG := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩) hc.2.2.2
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
    toReal_eLpNorm, toReal_eLpNorm] at hbf
  rw [ENNReal.toReal_add hAfin hBfin] at hbG
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB,
    toReal_eLpNorm, toReal_eLpNorm,
    toReal_eLpNorm] at hbG
  refine ⟨hc.1, ?_⟩
  nlinarith [mul_nonneg hB (lpNorm_nonneg (f := G) (p := 1) (μ := volume.restrict U))]

theorem HasW11GradientOn.comp_homeomorph_on_lpNorm {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G V)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {C K : ℝ≥0} (he : LipschitzWith C e) (hi : LipschitzWith K e.symm)
    (hmaps : MapsTo e U V) :
    HasW11GradientOn (f ∘ e) (fun x => (fderiv ℝ e x).adjoint (G (e x))) U ∧
      lpNorm (f ∘ e) 1 (volume.restrict U) +
        lpNorm (fun x => (fderiv ℝ e x).adjoint (G (e x))) 1 (volume.restrict U) ≤
      max 1 (C : ℝ) * (K : ℝ) ^ n *
        (lpNorm f 1 (volume.restrict V) + lpNorm G 1 (volume.restrict V)) := by
  obtain ⟨hh, hbf, hbG⟩ := hf.comp_homeomorph_on hU hV e he hi hmaps
  change (∫ x in U, ‖(f ∘ e) x‖) ≤ _ at hbf
  rw [← lpNorm_one_eq_integral_norm hh.integrable_function.1,
    ← lpNorm_one_eq_integral_norm hf.integrable_function.1] at hbf
  rw [← lpNorm_one_eq_integral_norm hh.integrable_gradient.1,
    ← lpNorm_one_eq_integral_norm hf.integrable_gradient.1] at hbG
  refine ⟨hh, (add_le_add hbf hbG).trans ?_⟩
  have hK : 0 ≤ (K : ℝ) ^ n := pow_nonneg K.coe_nonneg _
  have h1 : (K : ℝ) ^ n ≤ max 1 (C : ℝ) * (K : ℝ) ^ n := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 (C : ℝ)) hK
  have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 (C : ℝ)) hK
  calc
    _ ≤ max 1 (C : ℝ) * (K : ℝ) ^ n * lpNorm f 1 (volume.restrict V) +
        max 1 (C : ℝ) * (K : ℝ) ^ n * lpNorm G 1 (volume.restrict V) :=
      add_le_add (mul_le_mul_of_nonneg_right h1 lpNorm_nonneg)
        (mul_le_mul_of_nonneg_right h2 lpNorm_nonneg)
    _ = _ := by ring

theorem HasW11GradientOn.coordinateFold_halfCube_lpNorm {n : ℕ} (i : Fin n)
    {r R : ℝ} (hrR : r < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G (coordinateHalfCube i R)) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasW11GradientOn (f ∘ coordinateFold i) H (coordinateCube n r) ∧
      lpNorm (f ∘ coordinateFold i) 1 (volume.restrict (coordinateCube n r)) +
        lpNorm H 1 (volume.restrict (coordinateCube n r)) ≤
      2 * (lpNorm f 1 (volume.restrict (coordinateHalfCube i R)) +
        lpNorm G 1 (volume.restrict (coordinateHalfCube i R))) := by
  obtain ⟨hh, hbf, hbG⟩ := hf.coordinateFold_halfCube i hrR
  change (∫ x in coordinateCube n r, ‖(f ∘ coordinateFold i) x‖) ≤ _ at hbf
  rw [← lpNorm_one_eq_integral_norm hh.integrable_function.1,
    ← lpNorm_one_eq_integral_norm hf.integrable_function.1] at hbf
  rw [← lpNorm_one_eq_integral_norm hh.integrable_gradient.1,
    ← lpNorm_one_eq_integral_norm hf.integrable_gradient.1] at hbG
  exact ⟨_, hh, by simpa only [mul_add] using add_le_add hbf hbG⟩

end LiquidDrop
