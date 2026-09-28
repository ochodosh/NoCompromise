import NoCompromise.Elliptic.QuasilinearCampanatoInterior
import NoCompromise.Elliptic.NondivSchauderNorm

/-!
# Homogeneous interior Campanato estimates

Normalizing by a positive upper bound for the datum size makes the constant
independent of the solution. Letting that upper bound decrease to the actual
size includes the zero-size case without dividing by zero.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma IsWeakDivergenceEquationOn.nondiv_const_mul {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {F G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (he : IsWeakDivergenceEquationOn A F G U) (c : ℝ) :
    IsWeakDivergenceEquationOn A (fun x => c • F x) (fun x => c • G x) U := by
  intro φ hφ hcφ hsφ
  simp only [map_smul, ← smul_sub, inner_smul_left]
  rw [integral_const_mul, he φ hφ hcφ hsφ, mul_zero]

lemma nondiv_gradient_smul_recover {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) {s : ℝ} (hs : s ≠ 0)
    (hu : ContDiffOn ℝ 1 (fun x => s⁻¹ * u x) U) :
    ContDiffOn ℝ 1 u U ∧ ∀ x ∈ U,
      gradient u x = s • gradient (fun y => s⁻¹ * u y) x := by
  have he : u = fun x => s * (s⁻¹ * u x) := by
    funext x
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  refine ⟨by rw [he]; exact contDiffOn_const.mul hu, ?_⟩
  intro x hx
  have hd := (hu.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hf : fderiv ℝ u x = s • fderiv ℝ (fun y => s⁻¹ * u y) x := by
    conv_lhs => rw [he]
    simpa only [Pi.smul_apply, smul_eq_mul] using! (hd.hasFDerivAt.const_smul s).fderiv
  simp only [gradient, hf, map_smul]

/-- A genuine homogeneous Campanato bound, with a constant before all data and
before their nonnegative size T. -/
theorem nondiv_campanato_interior_homogeneous {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {α lam cap HA HG M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (u : EuclideanSpace ℝ (Fin n) → ℝ) (T : ℝ), 0 ≤ T →
      ContinuousOn A (ball 0 (3 / 4 : ℝ)) → ContinuousOn G (ball 0 (3 / 4 : ℝ)) →
      ContinuousOn u (ball 0 (3 / 4 : ℝ)) →
      (∀ x ∈ ball 0 (3 / 4 : ℝ), ‖A x‖ ≤ cap) →
      (∀ x ∈ ball 0 (3 / 4 : ℝ), ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
      (∀ x ∈ ball 0 (3 / 4 : ℝ), ∀ y ∈ ball 0 (3 / 4 : ℝ),
        ‖A x - A y‖ ≤ HA * dist x y ^ α) →
      (∀ x ∈ ball 0 (3 / 4 : ℝ), ∀ y ∈ ball 0 (3 / 4 : ℝ),
        ‖G x - G y‖ ≤ HG * T * dist x y ^ α) →
      HasH1GradientOn u F (ball 0 (3 / 4 : ℝ)) →
      IsWeakDivergenceEquationOn A F G (ball 0 (3 / 4 : ℝ)) →
      (∫ x in ball 0 (3 / 4 : ℝ), ‖F x‖ ^ 2) ≤ M * T ^ 2 →
      ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
        (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient u x‖ ≤ C * T) ∧
        ∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
          ‖gradient u x - gradient u y‖ ≤ C * T * dist x y ^ α := by
  obtain ⟨C, hC, hcamp⟩ := quasilinear_campanato_interior hn0 hn hα hα1
    hlam hcap hHA hHG hM
  refine ⟨C, hC, ?_⟩
  intro A G F u T hT hA hG huc hbA hell hAh hGh hu hw henergy
  have hscaled (s : ℝ) (hs : 0 < s) (hTs : T ≤ s) :
      ContDiffOn ℝ 1 u (ball 0 (1 / 2 : ℝ)) ∧
        (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient u x‖ ≤ C * s) ∧
        ∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
          ‖gradient u x - gradient u y‖ ≤ C * s * dist x y ^ α := by
    have hr : s⁻¹ * T ≤ 1 := by rw [inv_mul_eq_div]; exact (div_le_one hs).mpr hTs
    have hGs : ∀ x ∈ ball 0 (3 / 4 : ℝ), ∀ y ∈ ball 0 (3 / 4 : ℝ),
        ‖s⁻¹ • G x - s⁻¹ • G y‖ ≤ HG * dist x y ^ α := by
      intro x hx y hy
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
      apply (mul_le_mul_of_nonneg_left (hGh x hx y hy) (inv_nonneg.mpr hs.le)).trans
      have ht := mul_le_mul_of_nonneg_right hr
        (mul_nonneg hHG (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α))
      nlinarith only [ht]
    have hes : (∫ x in ball 0 (3 / 4 : ℝ), ‖s⁻¹ • F x‖ ^ 2) ≤ M := by
      simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [integral_const_mul]
      apply (mul_le_mul_of_nonneg_left henergy (sq_nonneg _)).trans
      have hr₀ : 0 ≤ s⁻¹ * T := mul_nonneg (inv_nonneg.mpr hs.le) hT
      have hr₂ : (s⁻¹ * T) ^ 2 ≤ 1 := by nlinarith only [hr, hr₀]
      have ht := mul_le_mul_of_nonneg_left hr₂ hM
      nlinarith only [ht]
    have hGc : ContinuousOn (fun x => s⁻¹ • G x) (ball 0 (3 / 4 : ℝ)) := by
      simpa only [Pi.smul_apply] using! hG.const_smul s⁻¹
    obtain ⟨hus, _, hbs, hhs⟩ := hcamp A (fun x => s⁻¹ • G x) (fun x => s⁻¹ • F x)
      (fun x => s⁻¹ * u x) hA hGc (continuousOn_const.mul huc)
      hbA hell hAh hGs (hu.const_mul _) (hw.nondiv_const_mul _) hes
    obtain ⟨hureg, hgrad⟩ := nondiv_gradient_smul_recover isOpen_ball hs.ne' hus
    refine ⟨hureg, ?_, ?_⟩
    · intro x hx
      rw [hgrad x hx, norm_smul, Real.norm_of_nonneg hs.le]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbs x hx) hs.le
    · intro x hx y hy
      rw [hgrad x hx, hgrad y hy, ← smul_sub, norm_smul, Real.norm_of_nonneg hs.le]
      simpa only [mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left (hhs x hx y hy) hs.le
  have hnorm (x) (hx : x ∈ ball 0 (1 / 2 : ℝ)) : ‖gradient u x‖ ≤ C * T := by
    have ht : Tendsto (fun j : ℕ => C * (T + 1 / ((j : ℝ) + 1))) atTop (𝓝 (C * T)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
    apply ge_of_tendsto ht
    exact Eventually.of_forall fun j =>
      (hscaled (T + 1 / ((j : ℝ) + 1)) (by positivity)
      (le_add_of_nonneg_right (by positivity))).2.1 x hx
  refine ⟨(hscaled (T + 1) (by positivity) (by linarith)).1, hnorm, ?_⟩
  intro x hx y hy
  have ht : Tendsto (fun j : ℕ => C * (T + 1 / ((j : ℝ) + 1)) * dist x y ^ α)
      atTop (𝓝 (C * T * dist x y ^ α)) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C).mul_const _
  apply ge_of_tendsto ht
  exact Eventually.of_forall fun j =>
    (hscaled (T + 1 / ((j : ℝ) + 1)) (by positivity)
      (le_add_of_nonneg_right (by positivity))).2.2 x hx y hy

end LiquidDrop
