module

public import NoCompromise.Elliptic.BoundaryNondivTests

@[expose] public section

/-!
# Boundary Caccioppoli for nondivergence quotients

The cutoff may meet the flat face. Its squared solution product is justified by
the actual H¹₀ test theorem, so no boundary weak-equation premise is added.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Boundary Caccioppoli with a compact ambient cutoff and an explicit constant. -/
theorem boundary_nondiv_caccioppoli_cutoff_bound {R : ℝ} (hR : 0 < R)
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : MeasurableSet V)
    (hVU : V ⊆ boundaryHalfBall R)
    {A : EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {u η : EuclideanSpace ℝ (Fin 3) → ℝ}
    {D G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {lam cap B : ℝ} (hlam : 0 < lam)
    (hA : AEStronglyMeasurable A (volume.restrict (boundaryHalfBall R)))
    (hell : ∀ᵐ x ∂volume.restrict (boundaryHalfBall R), ∀ v,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (hbA : ∀ᵐ x ∂volume.restrict (boundaryHalfBall R), ‖A x‖ ≤ cap)
    (hu : HasH1GradientOn u D (boundaryHalfBall R))
    (hT : HasZeroFlatTraceOn u D (ball 0 R))
    (hG : MemLp G 2 (volume.restrict (boundaryHalfBall R)))
    (he : IsWeakDivergenceEquationOn A D G (boundaryHalfBall R))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ ball 0 R)
    (hvη : ∀ x, 0 ≤ η x ∧ η x ≤ 1) (hbη : ∀ x, ‖gradient η x‖ ≤ B)
    (hηone : EqOn η (fun _ => 1) V) :
    (∫ x in V, ‖D x‖ ^ 2) ≤ ((8 * cap ^ 2 + 2 * lam + 2) / lam ^ 2) *
      (B ^ 2 * (∫ x in boundaryHalfBall R, u x ^ 2) +
        ∫ x in boundaryHalfBall R, ‖G x‖ ^ 2) := by
  let U := boundaryHalfBall R
  let v (x : EuclideanSpace ℝ (Fin 3)) := η x • D x
  let w (x : EuclideanSpace ℝ (Fin 3)) := u x • gradient η x
  let z (x : EuclideanSpace ℝ (Fin 3)) := η x • G x
  let P (x : EuclideanSpace ℝ (Fin 3)) := η x • (A x (D x) - G x)
  let Q (x : EuclideanSpace ℝ (Fin 3)) := v x + (2 : ℝ) • w x
  have hηnorm (x) : ‖η x‖ ≤ 1 := by rw [Real.norm_of_nonneg (hvη x).1]; exact (hvη x).2
  have hmul (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (hF : MemLp F 2 (volume.restrict U)) :
      MemLp (fun x => η x • F x) 2 (volume.restrict U) :=
    hF.of_le_mul (c := 1) (hη.continuous.aestronglyMeasurable.smul hF.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hηnorm x) (norm_nonneg _))
  have hF := (campanato_memLp_apply_bounded hA hu.memLp_gradient hbA).sub hG
  have hv : MemLp v 2 (volume.restrict U) := hmul D hu.memLp_gradient
  have hz : MemLp z 2 (volume.restrict U) := hmul G hG
  have hw : MemLp w 2 (volume.restrict U) :=
    hu.memLp_function.of_le_mul (c := B)
      (hu.memLp_function.aestronglyMeasurable.smul
        (continuous_gradient_of_contDiff (hη.of_le (by simp))).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        change ‖u x • gradient η x‖ ≤ B * ‖u x‖
        rw [norm_smul, mul_comm B]
        exact mul_le_mul_of_nonneg_left (hbη x) (norm_nonneg _))
  have hP : MemLp P 2 (volume.restrict U) := hmul _ hF
  have hQ : MemLp Q 2 (volume.restrict U) := hv.add (hw.const_smul (2 : ℝ))
  have hiV := hv.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiW := hw.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiZ := hz.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiPQ := integrable_inner_of_memLp_two hP hQ
  have heqP (x) : A x (v x) - z x = P x := by
    simp only [v, z, P, map_smul, smul_sub]
  have htest : (∫ x in U, inner ℝ (P x) (Q x)) = 0 := by
    convert boundary_nondiv_integral_inner_cutoff_sq_eq_zero hR hu hT hF he hη hcη hsη using 1
    congr 1
    ext x
    simp only [P, Q, v, w, Pi.sub_apply, real_inner_smul_left, inner_add_right, inner_smul_right]
    ring
  have hpoint : ∀ᵐ x ∂volume.restrict U, lam ^ 2 * ‖v x‖ ^ 2 ≤
      (8 * cap ^ 2 + 2 * lam + 2) * (‖w x‖ ^ 2 + ‖z x‖ ^ 2) +
        2 * lam * inner ℝ (P x) (Q x) := by
    filter_upwards [hell, hbA] with x hxell hxb
    simpa only [heqP, Q] using caccioppoli_vector_energy hlam hxell hxb (v x) (w x) (z x)
  have hint := integral_mono_ae (hiV.const_mul (lam ^ 2))
    (((hiW.add hiZ).const_mul (8 * cap ^ 2 + 2 * lam + 2)).add
      (hiPQ.const_mul (2 * lam))) hpoint
  change (∫ x in U, lam ^ 2 * ‖v x‖ ^ 2) ≤
    ∫ x in U, (8 * cap ^ 2 + 2 * lam + 2) * (‖w x‖ ^ 2 + ‖z x‖ ^ 2) +
      2 * lam * inner ℝ (P x) (Q x) at hint
  rw [integral_const_mul,
    integral_add (f := fun x => (8 * cap ^ 2 + 2 * lam + 2) * (‖w x‖ ^ 2 + ‖z x‖ ^ 2))
      (g := fun x => 2 * lam * inner ℝ (P x) (Q x))
      ((hiW.add hiZ).const_mul _) (hiPQ.const_mul _),
    integral_const_mul, integral_add hiW hiZ, integral_const_mul, htest,
    mul_zero, add_zero] at hint
  have henergy : (∫ x in U, ‖v x‖ ^ 2) ≤ ((8 * cap ^ 2 + 2 * lam + 2) / lam ^ 2) *
      ((∫ x in U, ‖w x‖ ^ 2) + ∫ x in U, ‖z x‖ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hlam)]
    nlinarith [hint]
  have hDb : (∫ x in V, ‖D x‖ ^ 2) ≤ ∫ x in U, ‖v x‖ ^ 2 := by
    calc
      _ = ∫ x in V, ‖v x‖ ^ 2 := by
        apply setIntegral_congr_fun hV
        intro x hx
        simp only [v, hηone hx, one_smul]
      _ ≤ _ := integral_mono_measure (Measure.restrict_mono hVU le_rfl)
        (Eventually.of_forall fun _ => sq_nonneg _) hiV
  have hiu : Integrable (fun x => u x ^ 2) (volume.restrict U) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hu.memLp_function.integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)
  have hWb : (∫ x in U, ‖w x‖ ^ 2) ≤ B ^ 2 * ∫ x in U, u x ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono hiW (hiu.const_mul _)
    intro x
    simp only [w, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbη x) 2) (sq_nonneg (u x))
    simpa only [mul_comm] using hh
  have hZb : (∫ x in U, ‖z x‖ ^ 2) ≤ ∫ x in U, ‖G x‖ ^ 2 := by
    apply integral_mono hiZ (hG.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    intro x
    have hh : ‖z x‖ ≤ ‖G x‖ := by
      simpa only [one_mul, z, norm_smul] using
        mul_le_mul_of_nonneg_right (hηnorm x) (norm_nonneg (G x))
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  exact hDb.trans (henergy.trans
    (mul_le_mul_of_nonneg_left (add_le_add hWb hZb) (by positivity)))

/-- Fixed nested-half-ball Caccioppoli, with the constant chosen before all
coefficient fields, solutions, and sources. -/
theorem boundary_nondiv_caccioppoli_nested_halfBalls {lam cap : ℝ} (hlam : 0 < lam) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) →
        EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
      (u : EuclideanSpace ℝ (Fin 3) → ℝ)
      (D G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      AEStronglyMeasurable A (volume.restrict (boundaryHalfBall (7 / 8))) →
      (∀ᵐ x ∂volume.restrict (boundaryHalfBall (7 / 8)), ∀ v,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      (∀ᵐ x ∂volume.restrict (boundaryHalfBall (7 / 8)), ‖A x‖ ≤ cap) →
      HasH1GradientOn u D (boundaryHalfBall (7 / 8)) →
      HasZeroFlatTraceOn u D (ball 0 (7 / 8)) →
      MemLp G 2 (volume.restrict (boundaryHalfBall (7 / 8))) →
      IsWeakDivergenceEquationOn A D G (boundaryHalfBall (7 / 8)) →
      (∫ x in boundaryHalfBall (3 / 4), ‖D x‖ ^ 2) ≤ C *
        ((∫ x in boundaryHalfBall (7 / 8), u x ^ 2) +
          ∫ x in boundaryHalfBall (7 / 8), ‖G x‖ ^ 2) := by
  let η : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) :=
    ⟨3 / 4, 13 / 16, by norm_num, by norm_num⟩
  have hcη := η.hasCompactSupport
  have hcgrad : HasCompactSupport (gradient η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset η)
  obtain ⟨B₀, hB₀⟩ := hcgrad.exists_bound_of_continuous
    (continuous_gradient_of_contDiff (η.contDiff : ContDiff ℝ 1 η))
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbη (x : EuclideanSpace ℝ (Fin 3)) : ‖gradient η x‖ ≤ B :=
    (hB₀ x).trans (le_max_left _ _)
  have hsη : tsupport η ⊆ ball 0 (7 / 8 : ℝ) := by
    rw [η.tsupport_eq]
    exact closedBall_subset_ball (by norm_num : (13 / 16 : ℝ) < 7 / 8)
  let K := (8 * cap ^ 2 + 2 * lam + 2) / lam ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K * (B ^ 2 + 1), by positivity, ?_⟩
  intro A u D G hA hell hbA hu hT hG he
  have ht := boundary_nondiv_caccioppoli_cutoff_bound (by norm_num : (0 : ℝ) < 7 / 8)
    (isOpen_boundaryHalfBall (3 / 4)).measurableSet
    (boundaryHalfBall_mono (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8))
    hlam hA hell hbA hu hT hG he η.contDiff hcη hsη
    (fun _ => ⟨η.nonneg, η.le_one⟩) hbη
    (show EqOn η (fun _ => 1) (boundaryHalfBall (3 / 4)) from
      fun _ hx => η.one_of_mem_closedBall (ball_subset_closedBall hx.1))
  apply ht.trans
  have hI : 0 ≤ ∫ x in boundaryHalfBall (7 / 8), u x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hJ : 0 ≤ ∫ x in boundaryHalfBall (7 / 8), ‖G x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  change K * _ ≤ (K * (B ^ 2 + 1)) * _
  have hh := mul_le_mul_of_nonneg_left
    (show B ^ 2 * (∫ x in boundaryHalfBall (7 / 8), u x ^ 2) +
        (∫ x in boundaryHalfBall (7 / 8), ‖G x‖ ^ 2) ≤
      (B ^ 2 + 1) * ((∫ x in boundaryHalfBall (7 / 8), u x ^ 2) +
        ∫ x in boundaryHalfBall (7 / 8), ‖G x‖ ^ 2) by nlinarith [sq_nonneg B]) hK.le
  simpa only [mul_assoc] using hh

end LiquidDrop
