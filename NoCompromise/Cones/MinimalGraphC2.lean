import NoCompromise.Stationary.BootstrapC2
import NoCompromise.Elliptic.NondivSchauderScalingInverse
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Interior C²,½ regularity for weak minimal graphs on disks of arbitrary radius. -/

noncomputable section
open Metric MeasureTheory InnerProductSpace Set
open scoped ContDiff RealInnerProductSpace

namespace LiquidDrop

/-- Uniform and square-root difference bounds give the actual finite Hölder norm. -/
lemma mc_finiteHolder_of_sqrt_bounds {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} {U : Set E} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ x ∈ U, ‖f x‖ ≤ A)
    (hh : ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ B * Real.sqrt ‖x - y‖) :
    HasFiniteHolderNormOn (1 / 2) f U := by
  apply HasFiniteHolderNormOn.of_bounds hA hB hb
  intro x hx y hy
  rw [← Real.sqrt_eq_rpow]
  by_cases he : x = y
  · subst y
    simpa using hB
  · exact (div_le_iff₀ (Real.sqrt_pos.2 (norm_pos_iff.2 (sub_ne_zero.2 he)))).2
      (hh x hx y hy)

/-- C¹ regularity and a square-root bound for the derivative imply C¹,½ on a disk. -/
lemma mc_C1_holder_of_derivative_sqrt {ρ K : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hC1 : ContDiffOn ℝ 1 f (ball 0 ρ))
    (hhol : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
        ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ K * Real.sqrt ‖x - y‖) :
    HasC1HolderOn (1 / 2) f (ball 0 ρ) := by
  have hz : (0 : EuclideanSpace ℝ (Fin 2)) ∈ ball 0 ρ := by simpa using hρ
  let M := ‖fderiv ℝ f 0‖ + max K 0 * Real.sqrt ρ
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hh (x) (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)
      (y) (hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ) :
      ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ max K 0 * Real.sqrt ‖x - y‖ :=
    (hhol x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _))
  have hb (x) (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ) :
      ‖fderiv ℝ f x‖ ≤ M := by
    have hxρ : ‖x‖ ≤ ρ := (mem_ball_zero_iff.1 hx).le
    calc
      ‖fderiv ℝ f x‖ ≤ ‖fderiv ℝ f x - fderiv ℝ f 0‖ + ‖fderiv ℝ f 0‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ max K 0 * Real.sqrt ‖x‖ + ‖fderiv ℝ f 0‖ := by
        simpa using add_le_add (hh x hx 0 hz) (le_refl ‖fderiv ℝ f 0‖)
      _ ≤ M := by
        dsimp [M]
        linarith [mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxρ) (le_max_right K 0)]
  have hl (x) (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ)
      (y) (hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ) :
      ‖f x - f y‖ ≤ M * ‖x - y‖ :=
    (convex_ball (0 : EuclideanSpace ℝ (Fin 2)) ρ).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hC1.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt one_ne_zero)
      hb hy hx
  refine ⟨hC1, ?_, mc_finiteHolder_of_sqrt_bounds hM (le_max_right K 0) hb hh⟩
  apply mc_finiteHolder_of_sqrt_bounds (A := M * ρ + ‖f 0‖)
    (B := M * Real.sqrt (2 * ρ)) (by positivity) (by positivity)
  · intro x hx
    calc
      ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
      _ ≤ M * ‖x‖ + ‖f 0‖ := by simpa using add_le_add (hl x hx 0 hz) (le_refl ‖f 0‖)
      _ ≤ M * ρ + ‖f 0‖ := add_le_add
        (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.1 hx).le hM) le_rfl
  · intro x hx y hy
    have hd : ‖x - y‖ ≤ 2 * ρ :=
      (norm_sub_le x y).trans (by linarith [mem_ball_zero_iff.1 hx, mem_ball_zero_iff.1 hy])
    have hs := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hd)
      (Real.sqrt_nonneg ‖x - y‖)
    rw [Real.mul_self_sqrt (norm_nonneg _)] at hs
    exact (hl x hx y hy).trans (by nlinarith [mul_le_mul_of_nonneg_left hs hM])

/-- The zero-right-hand-side unit-disk consequence with only the original C¹ hypotheses. -/
theorem mc_graph_C2_holder_unit_of_weak_zero {K : ℝ}
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hC1 : ContDiffOn ℝ 1 f (ball 0 1))
    (hhol : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ K * Real.sqrt ‖x - y‖)
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = 0) :
    HasC2HolderOn (1 / 2) f (ball 0 (1 / 2)) := by
  apply mc_graph_C2_holder_unit (G := fun _ => 0) (by norm_num) (by norm_num)
    (mc_C1_holder_of_derivative_sqrt (by norm_num) hC1 hhol)
  · exact HasFiniteHolderNormOn.of_bounds (A := 0) (B := 0) le_rfl le_rfl
      (by simp) (by simp)
  · simpa using he

/-- Scalar changes in both variables commute with the total derivative, everywhere. -/
lemma mc_fderiv_smul_comp_smul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c d : ℝ) (f : E → F) (x : E) :
    fderiv ℝ (fun y => c • f (d • y)) x = (c * d) • fderiv ℝ f (d • x) := by
  change fderiv ℝ (c • (fun y => f (d • y))) x = _
  rw [fderiv_const_smul_field]
  change c • fderiv ℝ (fun y => f (d • y)) x = _
  rw [fderiv_comp_smul, smul_smul]

/-- The height-and-domain normalization leaves the gradient unchanged. -/
lemma mc_graph_rescale_fderiv {ρ : ℝ} (hρ : ρ ≠ 0)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun y => f (ρ • y) / ρ) x = fderiv ℝ f (ρ • x) := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm, inv_mul_cancel₀ hρ,
    mul_inv_cancel₀ hρ, one_smul] using
    mc_fderiv_smul_comp_smul ρ⁻¹ ρ f x

lemma mc_graph_rescale_gradient {ρ : ℝ} (hρ : ρ ≠ 0)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    gradient (fun y => f (ρ • y) / ρ) x = gradient f (ρ • x) := by
  simp only [gradient, mc_graph_rescale_fderiv hρ]

/-- Positive dilation maps a disk of radius r into the disk of radius ρ * r. -/
lemma mc_smul_mem_ball {ρ r : ℝ} (hρ : 0 < ρ)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ ball 0 r) :
    ρ • x ∈ ball 0 (ρ * r) := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hρ.le]
  exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hx) hρ

/-- The C¹ and derivative Hölder hypotheses after normalizing a disk to radius one. -/
lemma mc_graph_rescale_C1 {ρ K : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hC1 : ContDiffOn ℝ 1 f (ball 0 ρ))
    (hhol : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
        ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ K * Real.sqrt ‖x - y‖) :
    ContDiffOn ℝ 1 (fun x => f (ρ • x) / ρ) (ball 0 1) ∧
    ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ‖fderiv ℝ (fun z => f (ρ • z) / ρ) x -
          fderiv ℝ (fun z => f (ρ • z) / ρ) y‖ ≤
            (K * Real.sqrt ρ) * Real.sqrt ‖x - y‖ := by
  have hm : MapsTo (fun x => ρ • x) (ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (ball 0 ρ) := fun x hx => by simpa using mc_smul_mem_ball hρ hx
  refine ⟨(hC1.comp (contDiff_id.const_smul ρ).contDiffOn hm).div_const ρ, ?_⟩
  intro x hx y hy
  rw [mc_graph_rescale_fderiv hρ.ne', mc_graph_rescale_fderiv hρ.ne']
  have hh := hhol (ρ • x) (hm hx) (ρ • y) (hm hy)
  simpa only [← smul_sub, norm_smul, Real.norm_of_nonneg hρ.le,
    Real.sqrt_mul hρ.le, mul_assoc] using hh

/-- Composition with a dilation preserves finite Hölder norms for exponents in [0,1]. -/
lemma mc_finiteHolder_comp_smul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (d : ℝ)
    {f : E → F} {U V : Set E} (hf : HasFiniteHolderNormOn a f U)
    (hm : MapsTo (fun x => d • x) V U) :
    HasFiniteHolderNormOn a (fun x => f (d • x)) V := by
  apply (nondiv_holder_comp_expansion ha ha1 (le_max_right ‖d‖ 1) hf hm ?_).1
  intro x hx y hy
  rw [← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- Scalar changes of variables preserve C² Hölder regularity, with no radius restriction. -/
lemma mc_C2Holder_smul_comp_smul {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (c d : ℝ) {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin 2))} (hf : HasC2HolderOn a f U)
    (hm : MapsTo (fun x => d • x) V U) :
    HasC2HolderOn a (fun x => c • f (d • x)) V := by
  have hD : fderiv ℝ (fun x => c • f (d • x)) =
      fun x => (c * d) • fderiv ℝ f (d • x) := by
    funext x
    exact mc_fderiv_smul_comp_smul c d f x
  have hDD : fderiv ℝ (fderiv ℝ (fun x => c • f (d • x))) =
      fun x => (c * d * d) • fderiv ℝ (fderiv ℝ f) (d • x) := by
    rw [hD]
    funext x
    exact mc_fderiv_smul_comp_smul (c * d) d (fderiv ℝ f) x
  refine ⟨(hf.contDiff.comp (contDiff_id.const_smul d).contDiffOn hm).const_smul c,
    (nondiv_holder_const_smul (mc_finiteHolder_comp_smul ha ha1 d hf.function_holder hm) c).1,
    ?_, ?_⟩
  · rw [hD]
    exact (nondiv_holder_const_smul
      (mc_finiteHolder_comp_smul ha ha1 d hf.derivative_holder hm) (c * d)).1
  · rw [hDD]
    exact (nondiv_holder_const_smul
      (mc_finiteHolder_comp_smul ha ha1 d hf.hessian_holder hm) (c * d * d)).1

/-- The weak zero-mean-curvature equation is invariant under disk normalization.
The identity is global; it does not require regularity of f outside the disk. -/
lemma mc_graph_rescale_weak_zero {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 ρ →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = 0) :
    ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ y, inner ℝ (gradient (fun x => f (ρ • x) / ρ) y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient (fun x => f (ρ • x) / ρ) y‖ ^ 2)) = 0 := by
  intro φ hφ hcφ hsφ
  let ψ := fun y => φ (ρ⁻¹ • y)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.const_smul ρ⁻¹)
  have hcψ : HasCompactSupport ψ := hcφ.comp_smul (inv_ne_zero hρ.ne')
  have hsψ : tsupport ψ ⊆ ball 0 ρ := by
    change tsupport (φ ∘ Homeomorph.smulOfNeZero ρ⁻¹ (inv_ne_zero hρ.ne')) ⊆ _
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have hh := mc_smul_mem_ball hρ (hsφ hy)
    simpa only [Homeomorph.smulOfNeZero_apply, smul_inv_smul₀ hρ.ne', mul_one] using hh
  have hz := he ψ hψ hcψ hsψ
  have hgrad (y : EuclideanSpace ℝ (Fin 2)) :
      gradient ψ (ρ • y) = ρ⁻¹ • gradient φ y := by
    simp only [ψ, gradient, fderiv_comp_smul, inv_smul_smul₀ hρ.ne', map_smul]
  have hi (y : EuclideanSpace ℝ (Fin 2)) :
      inner ℝ (gradient (fun x => f (ρ • x) / ρ) y) (gradient φ y) /
          Real.sqrt (1 + ‖gradient (fun x => f (ρ • x) / ρ) y‖ ^ 2) =
        ρ * (inner ℝ (gradient f (ρ • y)) (gradient ψ (ρ • y)) /
          Real.sqrt (1 + ‖gradient f (ρ • y)‖ ^ 2)) := by
    rw [mc_graph_rescale_gradient hρ.ne', hgrad, real_inner_smul_right]
    field_simp
  simp_rw [hi]
  rw [integral_const_mul, Measure.integral_comp_smul volume
    (fun y => inner ℝ (gradient f y) (gradient ψ y) /
      Real.sqrt (1 + ‖gradient f y‖ ^ 2)) ρ, hz, smul_zero, mul_zero]

/-- C²,½ regularity on the normalized disk transfers back to the original disk. -/
lemma mc_graph_rescale_C2_recover {ρ : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hg : HasC2HolderOn (1 / 2) (fun x => f (ρ • x) / ρ) (ball 0 (1 / 2))) :
    HasC2HolderOn (1 / 2) f (ball 0 (ρ / 2)) := by
  have hm : MapsTo (fun x => ρ⁻¹ • x)
      (ball (0 : EuclideanSpace ℝ (Fin 2)) (ρ / 2)) (ball 0 (1 / 2)) := by
    intro x hx
    have hh := mc_smul_mem_ball (inv_pos.2 hρ) hx
    have hr : ρ⁻¹ * (ρ / 2) = 1 / 2 := by field_simp
    rwa [hr] at hh
  have hh := mc_C2Holder_smul_comp_smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) ρ ρ⁻¹ hg hm
  simpa only [smul_inv_smul₀ hρ.ne', smul_eq_mul, mul_div_cancel₀ _ hρ.ne'] using hh

/-- A C¹,½ weak minimal graph on a positive-radius disk is C²,½ on its half disk. -/
theorem mc_graph_C2_holder_of_weak_zero {ρ K : ℝ} (hρ : 0 < ρ)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : EuclideanSpace ℝ (Fin 2)) ρ))
    (hhol : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
      ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
        ‖fderiv ℝ f x' - fderiv ℝ f y'‖ ≤ K * Real.sqrt ‖x' - y'‖)
    (he : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ →
      (∫ y, inner ℝ (gradient f y) (gradient φ y) /
        Real.sqrt (1 + ‖gradient f y‖ ^ 2)) = 0) :
    HasC2HolderOn (1 / 2) f (ball (0 : EuclideanSpace ℝ (Fin 2)) (ρ / 2)) := by
  obtain ⟨hc, hh⟩ := mc_graph_rescale_C1 hρ hC1 hhol
  exact mc_graph_rescale_C2_recover hρ
    (mc_graph_C2_holder_unit_of_weak_zero hc hh (mc_graph_rescale_weak_zero hρ he))

end LiquidDrop
