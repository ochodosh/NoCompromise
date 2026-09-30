module

public import NoCompromise.Sobolev.H1FlatExtension
public import NoCompromise.Sobolev.H1Calculus
public import NoCompromise.Sobolev.H1Chain

@[expose] public section

/-!
# Compact H¹ extension pieces on Lipschitz boundary charts

Pullback, flat reflection, pushforward, and compact cutoff produce the actual
linear extension pieces used in a finite partition of unity.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Pointwise
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma exists_smaller_chart_cube_of_compact_support {n : ℕ} (i : Fin n)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {R : ℝ} {ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ e '' coordinateCube n R) :
    ∃ r : ℝ, r < R ∧ tsupport ζ ⊆ e '' coordinateCube n r := by
  have hs : e.symm '' tsupport ζ ⊆ coordinateCube n R := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, heq⟩ := hsζ hy
    simpa only [← heq, e.symm_apply_apply] using hz
  obtain ⟨r, hrR, hsr⟩ := exists_smaller_coordinateCube_of_isCompact i
    (hcζ.image e.symm.continuous) hs
  refine ⟨r, hrR, fun x hx => ?_⟩
  exact ⟨e.symm x, hsr (mem_image_of_mem _ hx), e.apply_symm_apply x⟩

/-- The compact-cutoff product estimate in the ordinary sum of the two L² norms. -/
theorem HasH1GradientOn.mul_compact_cutoff_lpNorm {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    HasH1GradientOn (fun x => ζ x * f x)
      (fun x => ζ x • G x + f x • gradient ζ x) univ ∧
      lpNorm (fun x => ζ x * f x) 2 volume +
          lpNorm (fun x => ζ x • G x + f x • gradient ζ x) 2 volume ≤
        (A + B) * (lpNorm f 2 (volume.restrict U) + lpNorm G 2 (volume.restrict U)) := by
  have hc := hf.mul_compact_cutoff hU hζ hcζ hsζ hbζ hbgrad
  have hff := hf.memLp_function.eLpNorm_ne_top
  have hfg := hf.memLp_gradient.eLpNorm_ne_top
  have hm : MemLp (fun x => ζ x * f x) 2 volume := by
    simpa only [Measure.restrict_univ] using hc.1.memLp_function
  have hmG : MemLp (fun x => ζ x • G x + f x • gradient ζ x) 2 volume := by
    simpa only [Measure.restrict_univ] using hc.1.memLp_gradient
  have hAfin : ENNReal.ofReal A * eLpNorm G 2 (volume.restrict U) ≠ ∞ := by finiteness
  have hBfin : ENNReal.ofReal B * eLpNorm f 2 (volume.restrict U) ≠ ∞ := by finiteness
  have hbf := ENNReal.toReal_mono
    (by finiteness : ENNReal.ofReal A * eLpNorm f 2 (volume.restrict U) ≠ ∞) hc.2.2.1
  have hbG := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩) hc.2.2.2
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
    toReal_eLpNorm, toReal_eLpNorm] at hbf
  rw [ENNReal.toReal_add hAfin hBfin] at hbG
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB,
    toReal_eLpNorm, toReal_eLpNorm,
    toReal_eLpNorm] at hbG
  refine ⟨hc.1, ?_⟩
  nlinarith [mul_nonneg hB (lpNorm_nonneg (f := G) (p := 2) (μ := volume.restrict U))]

/-- Smaller-cube reflection in the ordinary sum of function and gradient L² norms. -/
theorem HasH1GradientOn.coordinateFold_halfCube_lpNorm {n : ℕ} (i : Fin n)
    {r R : ℝ} (hrR : r < R)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G (coordinateHalfCube i R)) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasH1GradientOn (f ∘ coordinateFold i) H (coordinateCube n r) ∧
        lpNorm (f ∘ coordinateFold i) 2 (volume.restrict (coordinateCube n r)) +
          lpNorm H 2 (volume.restrict (coordinateCube n r)) ≤
        Real.sqrt 2 * (lpNorm f 2 (volume.restrict (coordinateHalfCube i R)) +
          lpNorm G 2 (volume.restrict (coordinateHalfCube i R))) := by
  obtain ⟨H, hH, hbf, hbG⟩ := hf.coordinateFold_halfCube i hrR
  have hff := hf.memLp_function.eLpNorm_ne_top
  have hfg := hf.memLp_gradient.eLpNorm_ne_top
  have hbf' := ENNReal.toReal_mono
    (by finiteness : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
      eLpNorm f 2 (volume.restrict (coordinateHalfCube i R)) ≠ ∞) hbf
  have hbG' := ENNReal.toReal_mono
    (by finiteness : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
      eLpNorm G 2 (volume.restrict (coordinateHalfCube i R)) ≠ ∞) hbG
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat,
    ← Real.sqrt_eq_rpow, toReal_eLpNorm,
    toReal_eLpNorm] at hbf'
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat,
    ← Real.sqrt_eq_rpow, toReal_eLpNorm,
    toReal_eLpNorm] at hbG'
  exact ⟨H, hH, by simpa only [mul_add] using add_le_add hbf' hbG'⟩

/-- A compact local chart extension is globally H¹, with a fixed bound depending
only on the chart and cutoff. The construction is the existing raw linear map. -/
theorem h1_local_chart_extension {n : ℕ} (i : Fin n) (R : ℝ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) {C K : ℝ≥0}
    (he : LipschitzWith C e) (heinverse : LipschitzWith K e.symm)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hchart : e '' coordinateHalfCube i R = D ∩ e '' coordinateCube n R)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G D)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ e '' coordinateCube n R)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasH1GradientOn (cutoffChartReflectionLinearMap i e ζ f) H univ ∧
      EqOn (cutoffChartReflectionLinearMap i e ζ f) (fun x => ζ x * f x) D ∧
      tsupport (cutoffChartReflectionLinearMap i e ζ f) ⊆ tsupport ζ ∧
      lpNorm (cutoffChartReflectionLinearMap i e ζ f) 2 volume + lpNorm H 2 volume ≤
        ((A + B) * (Real.sqrt 2 * (max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2)) *
          (max 1 (K : ℝ) * (C : ℝ) ^ ((n : ℝ) / 2)))) *
            (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) := by
  obtain ⟨r, hrR, hsr⟩ := exists_smaller_chart_cube_of_compact_support i e hcζ hsζ
  have hpull := hf.comp_homeomorph_on_lpNorm (isOpen_coordinateHalfCube i R) hD e he
    heinverse (fun x hx => by
      have : e x ∈ e '' coordinateHalfCube i R := mem_image_of_mem e hx
      rw [hchart] at this
      exact this.1)
  obtain ⟨Hflat, hflat, hbflat⟩ := hpull.1.coordinateFold_halfCube_lpNorm i hrR
  have hpush := hflat.comp_homeomorph_on_lpNorm
    (e.isOpenMap _ (isOpen_coordinateCube n r)) (isOpen_coordinateCube n r)
    e.symm heinverse he (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      simpa only [e.symm_apply_apply] using hy)
  have hcut := hpush.1.mul_compact_cutoff_lpNorm
    (e.isOpenMap _ (isOpen_coordinateCube n r)).measurableSet hζ hcζ hsr hA hB hbζ hbgrad
  refine ⟨_, hcut.1, cutoffChartReflection_eq_on_domain i R e hchart hsζ f,
    tsupport_mul_subset_left, ?_⟩
  apply hcut.2.trans
  calc
    _ ≤ (A + B) * ((max 1 (K : ℝ) * (C : ℝ) ^ ((n : ℝ) / 2)) *
        (Real.sqrt 2 * ((max 1 (C : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2)) *
          (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D))))) := by
      apply mul_le_mul_of_nonneg_left _ (add_nonneg hA hB)
      apply hpush.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hbflat.trans (mul_le_mul_of_nonneg_left hpull.2 (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- A finite, input-independent H¹ bound for one interior or boundary partition piece. -/
noncomputable def h1BoundaryExtensionPieceBound {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D}) (B : ℝ) : ℝ :=
  match i with
  | none => 1 + B
  | some c => (1 + B) * (Real.sqrt 2 *
      (max 1 ((1 + c.val.lip : ℝ≥0) : ℝ) *
        ((1 + c.val.lip : ℝ≥0) : ℝ) ^ ((n : ℝ) / 2)) *
      (max 1 ((1 + c.val.lip : ℝ≥0) : ℝ) *
        ((1 + c.val.lip : ℝ≥0) : ℝ) ^ ((n : ℝ) / 2)))

lemma h1BoundaryExtensionPieceBound_nonneg {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D}) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ h1BoundaryExtensionPieceBound i B := by
  cases i <;> simp only [h1BoundaryExtensionPieceBound] <;> positivity

/-- Each fixed smooth partition piece gives a compact global H¹ extension of its
cutoff times the original function, with a bound uniform over all H¹ inputs. -/
theorem h1_boundaryExtensionPiece {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D})
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G D)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ boundaryExtensionRegion D i)
    (hbζ : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasH1GradientOn (boundaryExtensionPiece D i ζ f) H univ ∧
      EqOn (boundaryExtensionPiece D i ζ f) (fun x => ζ x * f x) D ∧
      tsupport (boundaryExtensionPiece D i ζ f) ⊆ tsupport ζ ∧
      lpNorm (boundaryExtensionPiece D i ζ f) 2 volume + lpNorm H 2 volume ≤
        h1BoundaryExtensionPieceBound i B *
          (lpNorm f 2 (volume.restrict D) + lpNorm G 2 (volume.restrict D)) := by
  have hnorm : ∀ x, ‖ζ x‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hbζ x).1]
    exact (hbζ x).2
  cases i with
  | none =>
    have hb := hf.mul_compact_cutoff_lpNorm hD.measurableSet hζ hcζ hsζ
      (by norm_num : (0 : ℝ) ≤ 1) hB hnorm hbgrad
    exact ⟨_, hb.1, fun _ _ => rfl, tsupport_mul_subset_left, hb.2⟩
  | some c =>
    exact h1_local_chart_extension c.val.normal c.val.radius c.val.homeomorph
      c.val.lipschitz c.val.lipschitz_symm hD c.property hf hζ hcζ hsζ
      (by norm_num) hB hnorm hbgrad

end LiquidDrop
