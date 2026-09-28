import NoCompromise.Elliptic.FrozenDecayEstimates

/-!
# Frozen derivative estimates on a prescribed boundary-reflection ball

The radius is fixed before the coefficient and solution. This version of the
interior estimate supplies the quantitative derivative bounds on the small
whole ball obtained by the genuine boundary reflection construction.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

theorem boundary_frozen_derivative_ball_bound {n k : ℕ} (hn : n < 4)
    {r : ℝ} (hr : 0 < r)
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        HasH1GradientOn u G (ball 0 r) →
        IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) (ball 0 r) →
        (∀ x, lam * ‖x‖ ^ 2 ≤ inner ℝ (A x) x) → ‖A‖ ≤ cap →
        ContDiffOn ℝ (⊤ : ℕ∞) u (ball 0 r) →
        ∀ x ∈ ball 0 (r / 2), ‖iteratedFDeriv ℝ (k + 1) u x‖ ≤
          C * lpNorm G 2 (volume.restrict (ball 0 r)) := by
  let M : ℝ≥0 := ⟨max 1 (Real.sqrt cap), le_trans (by norm_num) (le_max_left _ _)⟩
  let K : ℝ≥0 := ⟨max 1 (Real.sqrt lam)⁻¹, le_trans (by norm_num) (le_max_left _ _)⟩
  have hM : 0 < (M : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hK : 0 < (K : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let R : ℝ := r / (4 * (M : ℝ))
  have hR : 0 < R := by positivity
  have hMR : (M : ℝ) * R = r / 4 := by dsimp [R]; field_simp
  obtain ⟨B, hB, hb⟩ := harmonic_derivative_gradient_l2_bound (k := k) hn (half_lt_self hR)
  refine ⟨B * (M : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2) * (K : ℝ) ^ (k + 1),
    by positivity, ?_⟩
  intro A u G hu hw hell hbound hc x hx
  obtain ⟨L, hL, hiL, hH, hΔ⟩ := exists_frozen_harmonic_coordinates isOpen_ball hu A hw
    hlam hcap hell hbound
  let V : Set (EuclideanSpace ℝ (Fin n)) := L ⁻¹' ball 0 r
  let v := u ∘ L
  have hV : IsOpen V := isOpen_ball.preimage L.continuous
  have hLc : ‖L.toContinuousLinearMap‖ ≤ (M : ℝ) := hL.trans (le_max_right _ _)
  have hiLc : ‖L.symm.toContinuousLinearMap‖ ≤ (K : ℝ) := hiL.trans (le_max_right _ _)
  have hLip : LipschitzWith M L := L.lipschitzWith.weaken (by exact_mod_cast hLc)
  have hiLip : LipschitzWith K L.symm := L.symm.lipschitzWith.weaken (by exact_mod_cast hiLc)
  have hcv : ContDiffOn ℝ (⊤ : ℕ∞) v V :=
    hc.comp L.contDiff.contDiffOn (fun _ hy => hy)
  have heG : gradient v =ᵐ[volume.restrict V]
      (fun y => L.toContinuousLinearMap.adjoint (G (L y))) :=
    (hasWeakGradientOn_of_contDiffOn hV (hcv.of_le (by simp))).unique hV hH.toHasWeakGradientOn
  have hg : MemLp (gradient v) 2 (volume.restrict V) :=
    hH.memLp_gradient.ae_eq heG.symm
  have hgLp : lpNorm (gradient v) 2 (volume.restrict V) ≤
      (M : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2) * lpNorm G 2 (volume.restrict (ball 0 r)) := by
    have he : lpNorm (gradient v) 2 (volume.restrict V) =
        lpNorm (fun y => L.toContinuousLinearMap.adjoint (G (L y))) 2
          (volume.restrict V) := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm,
        eLpNorm_congr_ae heG]
    rw [he]
    exact frozen_gradient_pullback_lpNorm_le hV isOpen_ball hu L hLip hiLip (fun _ hy => hy)
  have hs : ball (L.symm x) R ⊆ V := by
    intro y hy
    change dist (L y) 0 < r
    have hdist := hLip.dist_le_mul y (L.symm x)
    rw [L.apply_symm_apply] at hdist
    have hy' : dist y (L.symm x) < R := hy
    have hx' : dist x 0 < r / 2 := hx
    calc
      dist (L y) 0 ≤ dist (L y) x + dist x 0 := dist_triangle _ _ _
      _ ≤ (M : ℝ) * dist y (L.symm x) + dist x 0 := add_le_add hdist le_rfl
      _ < (M : ℝ) * R + r / 2 := add_lt_add (mul_lt_mul_of_pos_left hy' hM) hx'
      _ < r := by rw [hMR]; linarith
  have hsmall : L.symm x ∈ ball (L.symm x) (R / 2) := mem_ball_self (half_pos hR)
  have hvbound := hb (L.symm x) v (hΔ.mono hs)
    (hg.mono_measure (Measure.restrict_mono hs le_rfl)) (hcv.mono hs) _ hsmall
  have he : v ∘ L.symm = u := by funext y; simp [v]
  calc
    ‖iteratedFDeriv ℝ (k + 1) u x‖ = ‖iteratedFDeriv ℝ (k + 1) (v ∘ L.symm) x‖ := by rw [he]
    _ ≤ ‖iteratedFDeriv ℝ (k + 1) v (L.symm x)‖ * ‖L.symm.toContinuousLinearMap‖ ^ (k + 1) :=
      frozen_norm_iteratedFDeriv_comp_linear_le L.symm v x
    _ ≤ (B * lpNorm (gradient v) 2 (volume.restrict V)) * (K : ℝ) ^ (k + 1) := by
      apply mul_le_mul
      · exact hvbound.trans (mul_le_mul_of_nonneg_left
          (poisson_lpNorm_mono_measure hg (Measure.restrict_mono hs le_rfl)) hB.le)
      · exact pow_le_pow_left₀ (norm_nonneg _) hiLc _
      · positivity
      · exact mul_nonneg hB.le lpNorm_nonneg
    _ ≤ (B * ((M : ℝ) * (K : ℝ) ^ ((n : ℝ) / 2) *
        lpNorm G 2 (volume.restrict (ball 0 r)))) * (K : ℝ) ^ (k + 1) := by
      gcongr
    _ = _ := by ring


end LiquidDrop
