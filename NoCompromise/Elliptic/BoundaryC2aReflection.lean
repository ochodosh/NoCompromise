import NoCompromise.Elliptic.BoundaryNeumannC2
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.ExtendFrom

/-!
# C² reflection across a flat face

A function which is C¹ near a flat disk and C² with uniformly continuous second
derivatives on the open upper slab above it extends, by a three-term higher-order
reflection, to a C² function on the full open slab around the disk.
-/

noncomputable section
open Filter Metric Set
open scoped Topology
namespace LiquidDrop

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The open slab around the flat disk of radius `a`, normal thickness `b` on both sides. -/
def boundaryReflectSlab (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {y | ‖graphProjectionN 2 y‖ < a ∧ |y (Fin.last 2)| < b}

/-- Its upper open half. -/
def boundaryReflectUpper (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {y | ‖graphProjectionN 2 y‖ < a ∧ 0 < y (Fin.last 2) ∧ y (Fin.last 2) < b}

/-- The upper half of the slab together with the flat disk. -/
def boundaryReflectClosedUpper (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {y | ‖graphProjectionN 2 y‖ < a ∧ 0 ≤ y (Fin.last 2) ∧ y (Fin.last 2) < b}

/-- The linear map multiplying the normal coordinate by `s`. -/
def boundaryReflectMap (s : ℝ) : E₃ →L[ℝ] E₃ :=
  ContinuousLinearMap.id ℝ E₃ + (s - 1) •
    (EuclideanSpace.proj (Fin.last 2) : E₃ →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single (Fin.last 2) (1 : ℝ))

/-- The normal scalings `-1, -1/2, -1/3` of the reflection. -/
def boundaryReflectScale : Fin 3 → ℝ := ![-1, -1 / 2, -1 / 3]

/-- The reflection coefficients `6, -32, 27`. -/
def boundaryReflectCoef : Fin 3 → ℝ := ![6, -32, 27]

lemma boundary_reflect_continuous_last : Continuous fun y : E₃ => y (Fin.last 2) :=
  (EuclideanSpace.proj (Fin.last 2) : E₃ →L[ℝ] ℝ).continuous

lemma boundaryReflectMap_apply (s : ℝ) (w : E₃) :
    boundaryReflectMap s w =
      w + ((s - 1) * w (Fin.last 2)) • EuclideanSpace.single (Fin.last 2) (1 : ℝ) := by
  simp [boundaryReflectMap, mul_smul]

lemma boundaryReflectMap_last (s : ℝ) (w : E₃) :
    boundaryReflectMap s w (Fin.last 2) = s * w (Fin.last 2) := by
  rw [boundaryReflectMap_apply]
  simp
  ring

lemma graphProjectionN_boundaryReflectMap (s : ℝ) (w : E₃) :
    graphProjectionN 2 (boundaryReflectMap s w) = graphProjectionN 2 w := by
  ext i
  rw [boundaryReflectMap_apply]
  fin_cases i <;> simp

lemma boundaryReflectMap_of_last_eq_zero (s : ℝ) {w : E₃} (h : w (Fin.last 2) = 0) :
    boundaryReflectMap s w = w := by
  rw [boundaryReflectMap_apply, h]
  simp

lemma boundary_reflect_moment_zero : ∑ k, boundaryReflectCoef k = 1 := by
  simp [Fin.sum_univ_three, boundaryReflectCoef]
  norm_num

lemma boundary_reflect_moment_one :
    ∑ k, boundaryReflectCoef k * (boundaryReflectScale k - 1) = 0 := by
  simp [Fin.sum_univ_three, boundaryReflectCoef, boundaryReflectScale]
  norm_num

lemma boundary_reflect_moment_two :
    ∑ k, boundaryReflectCoef k * (boundaryReflectScale k - 1) ^ 2 = 0 := by
  simp [Fin.sum_univ_three, boundaryReflectCoef, boundaryReflectScale]
  norm_num

lemma boundary_reflect_scale_bounds (k : Fin 3) :
    -1 ≤ boundaryReflectScale k ∧ boundaryReflectScale k < 0 := by
  fin_cases k <;> simp [boundaryReflectScale] <;> norm_num

lemma boundary_reflect_sum_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E₃ →L[ℝ] F) :
    ∑ k, boundaryReflectCoef k • L.comp (boundaryReflectMap (boundaryReflectScale k)) = L := by
  ext1 w
  simp [boundaryReflectMap_apply, Fin.sum_univ_three, boundaryReflectCoef,
    boundaryReflectScale, map_add, map_smul]
  module

lemma boundary_reflect_sum_bilin {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E₃ →L[ℝ] E₃ →L[ℝ] F) (w w' : E₃) :
    ∑ k, boundaryReflectCoef k • B (boundaryReflectMap (boundaryReflectScale k) w)
      (boundaryReflectMap (boundaryReflectScale k) w') = B w w' := by
  simp [boundaryReflectMap_apply, Fin.sum_univ_three, boundaryReflectCoef,
    boundaryReflectScale, map_add, map_smul]
  module

section Glue

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative coefficient operators `L ↦ A k ∘ L ∘ R_k`. -/
def boundaryReflectDerivOp (A : Fin 3 → F →L[ℝ] F) (k : Fin 3) :
    (E₃ →L[ℝ] F) →L[ℝ] (E₃ →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ E₃ F F (A k)).comp
    ((ContinuousLinearMap.compL ℝ E₃ E₃ F).flip (boundaryReflectMap (boundaryReflectScale k)))

@[simp] lemma boundaryReflectDerivOp_apply (A : Fin 3 → F →L[ℝ] F) (k : Fin 3)
    (L : E₃ →L[ℝ] F) :
    boundaryReflectDerivOp A k L =
      (A k).comp (L.comp (boundaryReflectMap (boundaryReflectScale k))) := rfl

/-- Keep `g` on the closed upper half and reflect it, with coefficient operators `A`,
on the open lower half. -/
def boundaryReflectGlue (A : Fin 3 → F →L[ℝ] F) (g : E₃ → F) (y : E₃) : F :=
  if 0 ≤ y (Fin.last 2) then g y
  else ∑ k, A k (g (boundaryReflectMap (boundaryReflectScale k) y))

end Glue

/-- The scalar reflection coefficients as operators on `ℝ`. -/
def boundaryReflectScalarOp : Fin 3 → ℝ →L[ℝ] ℝ :=
  fun k => boundaryReflectCoef k • ContinuousLinearMap.id ℝ ℝ

lemma boundary_reflect_scalarOp_sum (x : ℝ) : ∑ k, boundaryReflectScalarOp k x = x := by
  simp [boundaryReflectScalarOp, ← Finset.sum_mul, boundary_reflect_moment_zero]

lemma boundary_reflect_derivOp_sum (L : E₃ →L[ℝ] ℝ) :
    ∑ k, boundaryReflectDerivOp boundaryReflectScalarOp k L = L := by
  conv_rhs => rw [← boundary_reflect_sum_comp L]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext1 w
  simp [boundaryReflectScalarOp]

lemma boundary_reflect_derivOp_derivOp_sum (B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ) :
    ∑ k, boundaryReflectDerivOp (boundaryReflectDerivOp boundaryReflectScalarOp) k B = B := by
  ext w w'
  rw [← boundary_reflect_sum_bilin B w w']
  simp [boundaryReflectScalarOp]

/-- A point of an open set with `0 ≤ σ t` is a limit of points of the set with `0 < σ t`. -/
lemma boundary_reflect_mem_closure_half {s : Set E₃} (hs : IsOpen s) {y : E₃} (hy : y ∈ s)
    {σ : ℝ} (hσ : σ ≠ 0) (hy0 : 0 ≤ σ * y (Fin.last 2)) :
    y ∈ closure (s ∩ {z | 0 < σ * z (Fin.last 2)}) := by
  let p : ℝ → E₃ := fun ε => y + (ε * σ) • EuclideanSpace.single (Fin.last 2) (1 : ℝ)
  have hp : Continuous p := by fun_prop
  have ht : Tendsto p (𝓝[>] 0) (𝓝 y) := by
    have h := hp.tendsto 0
    simp only [p, zero_mul, zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), p ε ∈ s := ht (hs.mem_nhds hy)
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [h1, h2] with ε h1 h2
  refine ⟨h1, ?_⟩
  change 0 < σ * (p ε) (Fin.last 2)
  have hσ2 : 0 < σ * σ := mul_self_pos.mpr hσ
  simp only [p, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
    smul_eq_mul, mul_one]
  nlinarith

/-- Gluing of derivatives across the flat face: continuity everywhere, a continuous
candidate derivative, and actual derivatives off the face give actual derivatives
on the face. -/
theorem boundary_reflect_hasFDerivAt_of_off_face {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E₃ → F} {D : E₃ → E₃ →L[ℝ] F} {U : Set E₃} (hU : IsOpen U)
    {x : E₃} (hx : x ∈ U) (hf : ContinuousOn f U)
    (hfd : ∀ y ∈ U, y (Fin.last 2) ≠ 0 → HasFDerivAt f (D y) y)
    (hD : ContinuousAt D x) : HasFDerivAt f (D x) x := by
  by_cases hx0 : x (Fin.last 2) ≠ 0
  · exact hfd x hx hx0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hr : 0 < ε / 2 := by linarith
  have hcl : closure (ball x (ε / 2)) ⊆ U :=
    closure_ball_subset_closedBall.trans ((closedBall_subset_ball (by linarith)).trans hball)
  have key : ∀ σ : ℝ, σ ≠ 0 → HasFDerivWithinAt f (D x)
      (closure (ball x (ε / 2) ∩ {z | 0 < σ * z (Fin.last 2)})) x := by
    intro σ hσ
    have hs_open : IsOpen (ball x (ε / 2) ∩ {z : E₃ | 0 < σ * z (Fin.last 2)}) :=
      isOpen_ball.inter (isOpen_lt continuous_const
        (continuous_const.mul boundary_reflect_continuous_last))
    have hlin : IsLinearMap ℝ (fun z : E₃ => σ * z (Fin.last 2)) :=
      IsLinearMap.mk (fun z w => by simp; ring) (fun c z => by simp; ring)
    have hs_conv : Convex ℝ (ball x (ε / 2) ∩ {z : E₃ | 0 < σ * z (Fin.last 2)}) :=
      (convex_ball x (ε / 2)).inter (convex_halfSpace_gt hlin 0)
    have hsU : ball x (ε / 2) ∩ {z : E₃ | 0 < σ * z (Fin.last 2)} ⊆ U :=
      fun z hz => hcl (subset_closure hz.1)
    have hs_off : ∀ z ∈ ball x (ε / 2) ∩ {z : E₃ | 0 < σ * z (Fin.last 2)},
        z (Fin.last 2) ≠ 0 := by
      intro z hz h
      have h' : 0 < σ * z (Fin.last 2) := hz.2
      rw [h, mul_zero] at h'
      exact lt_irrefl _ h'
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    · intro z hz
      exact (hfd z (hsU hz) (hs_off z hz)).differentiableAt.differentiableWithinAt
    · exact hs_conv
    · exact hs_open
    · intro z hz
      exact (hf.continuousAt (hU.mem_nhds (hcl (closure_mono inter_subset_left hz))))
        |>.continuousWithinAt
    · have h : Tendsto D (𝓝[ball x (ε / 2) ∩ {z : E₃ | 0 < σ * z (Fin.last 2)}] x)
          (𝓝 (D x)) := hD.tendsto.mono_left nhdsWithin_le_nhds
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact ((hfd z (hsU hz) (hs_off z hz)).fderiv).symm
  have hunion := (key 1 one_ne_zero).union (key (-1) (by norm_num))
  apply hunion.hasFDerivAt
  apply Filter.mem_of_superset (ball_mem_nhds x hr)
  intro y hy
  by_cases h : 0 ≤ y (Fin.last 2)
  · left
    exact boundary_reflect_mem_closure_half isOpen_ball hy one_ne_zero (by simpa using h)
  · right
    exact boundary_reflect_mem_closure_half isOpen_ball hy (by norm_num) (by linarith)

lemma isOpen_boundaryReflectSlab (a b : ℝ) : IsOpen (boundaryReflectSlab a b) :=
  (isOpen_lt (continuous_norm.comp (graphProjectionN 2).continuous) continuous_const).inter
    (isOpen_lt boundary_reflect_continuous_last.abs continuous_const)

lemma isOpen_boundaryReflectUpper (a b : ℝ) : IsOpen (boundaryReflectUpper a b) :=
  (isOpen_lt (continuous_norm.comp (graphProjectionN 2).continuous) continuous_const).inter
    ((isOpen_lt continuous_const boundary_reflect_continuous_last).inter
      (isOpen_lt boundary_reflect_continuous_last continuous_const))

lemma boundary_reflect_map_mem_closedUpper {a b : ℝ} {y : E₃} (hy : y ∈ boundaryReflectSlab a b)
    (hy0 : y (Fin.last 2) ≤ 0) (k : Fin 3) :
    boundaryReflectMap (boundaryReflectScale k) y ∈ boundaryReflectClosedUpper a b := by
  obtain ⟨h1, h2⟩ := boundary_reflect_scale_bounds k
  have hb := (abs_lt.mp hy.2)
  refine ⟨by rw [graphProjectionN_boundaryReflectMap]; exact hy.1, ?_, ?_⟩ <;>
    rw [boundaryReflectMap_last] <;> nlinarith

lemma boundary_reflect_map_mem_upper {a b : ℝ} {y : E₃} (hy : y ∈ boundaryReflectSlab a b)
    (hy0 : y (Fin.last 2) < 0) (k : Fin 3) :
    boundaryReflectMap (boundaryReflectScale k) y ∈ boundaryReflectUpper a b := by
  obtain ⟨h1, h2⟩ := boundary_reflect_scale_bounds k
  have hb := (abs_lt.mp hy.2)
  refine ⟨by rw [graphProjectionN_boundaryReflectMap]; exact hy.1, ?_, ?_⟩ <;>
    rw [boundaryReflectMap_last] <;> nlinarith

lemma boundary_reflect_mem_closedUpper {a b : ℝ} {y : E₃} (hy : y ∈ boundaryReflectSlab a b)
    (hy0 : 0 ≤ y (Fin.last 2)) : y ∈ boundaryReflectClosedUpper a b :=
  ⟨hy.1, hy0, (abs_lt.mp hy.2).2⟩

lemma boundary_reflect_closedUpper_subset_closure {a b : ℝ} :
    boundaryReflectClosedUpper a b ⊆ closure (boundaryReflectUpper a b) := by
  intro y hy
  have hyS : y ∈ boundaryReflectSlab a b :=
    ⟨hy.1, abs_lt.mpr ⟨by linarith [hy.2.1, hy.2.2], hy.2.2⟩⟩
  have h := boundary_reflect_mem_closure_half (isOpen_boundaryReflectSlab a b) hyS one_ne_zero
    (by simpa using hy.2.1)
  refine closure_mono ?_ h
  rintro z ⟨hz, hz0⟩
  simp only [one_mul, mem_ofPred_eq] at hz0
  exact ⟨hz.1, hz0, (abs_lt.mp hz.2).2⟩

section GlueRegularity

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The glued function is continuous on the slab. -/
theorem boundary_reflect_glue_continuousOn {a b : ℝ} (A : Fin 3 → F →L[ℝ] F) {g : E₃ → F}
    (hgc : ContinuousOn g (boundaryReflectClosedUpper a b))
    (hgA : ∀ y ∈ boundaryReflectSlab a b, y (Fin.last 2) = 0 → ∑ k, A k (g y) = g y) :
    ContinuousOn (boundaryReflectGlue A g) (boundaryReflectSlab a b) := by
  have heq : boundaryReflectGlue A g = {y : E₃ | 0 ≤ y (Fin.last 2)}.piecewise g
      (fun y => ∑ k, A k (g (boundaryReflectMap (boundaryReflectScale k) y))) := by
    funext y
    simp [boundaryReflectGlue, Set.piecewise]
  rw [heq]
  apply ContinuousOn.piecewise
  · rintro y ⟨hyO, hyf⟩
    have h0 : (0 : ℝ) = y (Fin.last 2) :=
      frontier_le_subset_eq continuous_const boundary_reflect_continuous_last hyf
    simp only [boundaryReflectMap_of_last_eq_zero _ h0.symm, hgA y hyO h0.symm]
  · apply hgc.mono
    rintro y ⟨hyO, hycl⟩
    rw [(isClosed_le continuous_const boundary_reflect_continuous_last).closure_eq] at hycl
    exact boundary_reflect_mem_closedUpper hyO hycl
  · have hcl : closure {y : E₃ | 0 ≤ y (Fin.last 2)}ᶜ ⊆ {y : E₃ | y (Fin.last 2) ≤ 0} := by
      rw [compl_ofPred]
      simp only [not_le]
      exact closure_lt_subset_le boundary_reflect_continuous_last continuous_const
    refine continuousOn_finsetSum _ fun k _ => ?_
    refine (A k).continuous.comp_continuousOn (hgc.comp
      (boundaryReflectMap (boundaryReflectScale k)).continuous.continuousOn ?_)
    rintro y ⟨hyO, hycl⟩
    exact boundary_reflect_map_mem_closedUpper hyO (hcl hycl) k

/-- One C¹ gluing step: if `g` has derivative `T` on the open upper slab, both are
continuous up to the flat disk, and the coefficient operators reproduce `g` and `T` on
the disk, then the glued function has the glued derivative on the whole slab. -/
theorem boundary_reflect_glue_hasFDerivAt {a b : ℝ} (A : Fin 3 → F →L[ℝ] F) {g : E₃ → F}
    {T : E₃ → E₃ →L[ℝ] F}
    (hg : ∀ y ∈ boundaryReflectUpper a b, HasFDerivAt g (T y) y)
    (hgc : ContinuousOn g (boundaryReflectClosedUpper a b))
    (hTc : ContinuousOn T (boundaryReflectClosedUpper a b))
    (hgA : ∀ y ∈ boundaryReflectSlab a b, y (Fin.last 2) = 0 → ∑ k, A k (g y) = g y)
    (hTA : ∀ y ∈ boundaryReflectSlab a b, y (Fin.last 2) = 0 →
      ∑ k, boundaryReflectDerivOp A k (T y) = T y) :
    ∀ y ∈ boundaryReflectSlab a b,
      HasFDerivAt (boundaryReflectGlue A g) (boundaryReflectGlue (boundaryReflectDerivOp A) T y)
        y := by
  intro x hx
  refine boundary_reflect_hasFDerivAt_of_off_face (isOpen_boundaryReflectSlab a b) hx
    (boundary_reflect_glue_continuousOn A hgc hgA) ?_
    ((boundary_reflect_glue_continuousOn (boundaryReflectDerivOp A) hTc hTA).continuousAt
      ((isOpen_boundaryReflectSlab a b).mem_nhds hx))
  intro y hy hy0
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · have hev : boundaryReflectGlue A g =ᶠ[𝓝 y]
        fun z => ∑ k, A k (g (boundaryReflectMap (boundaryReflectScale k) z)) := by
      filter_upwards [(isOpen_lt boundary_reflect_continuous_last continuous_const).mem_nhds
        hneg] with z hz
      rw [boundaryReflectGlue, ite_eq_right (not_le.mpr (show z (Fin.last 2) < 0 from hz))]
    have hval : boundaryReflectGlue (boundaryReflectDerivOp A) T y =
        ∑ k, boundaryReflectDerivOp A k (T (boundaryReflectMap (boundaryReflectScale k) y)) := by
      rw [boundaryReflectGlue, ite_eq_right (not_le.mpr hneg)]
    rw [hval]
    refine HasFDerivAt.congr_of_eventuallyEq ?_ hev
    apply HasFDerivAt.fun_sum
    intro k _
    have hk := hg _ (boundary_reflect_map_mem_upper hy hneg k)
    exact (A k).hasFDerivAt.comp y
      (hk.comp y (boundaryReflectMap (boundaryReflectScale k)).hasFDerivAt)
  · have hyU : y ∈ boundaryReflectUpper a b := ⟨hy.1, hpos, (abs_lt.mp hy.2).2⟩
    have hev : boundaryReflectGlue A g =ᶠ[𝓝 y] g := by
      filter_upwards [(isOpen_lt continuous_const boundary_reflect_continuous_last).mem_nhds
        hpos] with z hz
      rw [boundaryReflectGlue, ite_eq_left (show 0 < z (Fin.last 2) from hz).le]
    have hval : boundaryReflectGlue (boundaryReflectDerivOp A) T y = T y := by
      rw [boundaryReflectGlue, ite_eq_left hpos.le]
    rw [hval]
    exact (hg y hyU).congr_of_eventuallyEq hev

end GlueRegularity

/-- Entrywise Hölder bounds for the coordinate second derivatives on the open upper
slab make the full second derivative uniformly continuous there, so it extends
continuously to the closure. -/
theorem boundary_reflect_second_deriv_extension {a b α C : ℝ} (hα : 0 < α)
    {v : E₃ → ℝ} (hv2 : ContDiffOn ℝ 2 v (boundaryReflectUpper a b))
    (hhol : ∀ i j : Fin 3, ∀ x ∈ boundaryReflectUpper a b, ∀ y ∈ boundaryReflectUpper a b,
      |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤ C * dist x y ^ α) :
    ∃ S : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ,
      EqOn S (fderiv ℝ (fderiv ℝ v)) (boundaryReflectUpper a b) ∧
      ContinuousOn S (closure (boundaryReflectUpper a b)) := by
  have hU := isOpen_boundaryReflectUpper a b
  have hbound : ∀ x ∈ boundaryReflectUpper a b, ∀ y ∈ boundaryReflectUpper a b,
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤
        3 * (3 * (max C 0 * dist x y ^ α)) := by
    intro x hx y hy
    have hc : 0 ≤ max C 0 * dist x y ^ α :=
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)
    have h3 := nondiv_norm_clm_le_coordinate_bound
      (fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y) (C := 3 * (max C 0 * dist x y ^ α))
      (by positivity) ?_
    · simpa using h3
    intro i
    have h3' := nondiv_norm_clm_le_coordinate_bound
      ((fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y) (EuclideanSpace.single i 1)) hc ?_
    · simpa using h3'
    intro j
    have hij := hhol i j x hx y hy
    unfold boundaryNeumannC2Entry at hij
    rw [nondiv_fderiv_coordinate_eq hU hv2 j hx, nondiv_fderiv_coordinate_eq hU hv2 j hy] at hij
    simp only [ContinuousLinearMap.flip_apply] at hij
    rw [Real.norm_eq_abs]
    simp only [sub_apply]
    exact hij.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  have huc : UniformContinuousOn (fderiv ℝ (fderiv ℝ v)) (boundaryReflectUpper a b) := by
    have ht : Tendsto (fun t : ℝ => 3 * (3 * (max C 0 * t ^ α))) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => 3 * (3 * (max C 0 * t ^ α))) :=
        continuous_const.mul (continuous_const.mul
          (continuous_const.mul (Real.continuous_rpow_const hα.le)))
      simpa [Real.zero_rpow hα.ne'] using hc.tendsto 0
    have hmain : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ boundaryReflectUpper a b,
        ∀ y ∈ boundaryReflectUpper a b, dist x y < δ →
          dist (fderiv ℝ (fderiv ℝ v) x) (fderiv ℝ (fderiv ℝ v) y) < ε := by
      intro ε hε
      obtain ⟨δ, hδ, hmod⟩ := Metric.tendsto_nhds_nhds.mp ht ε hε
      refine ⟨δ, hδ, ?_⟩
      intro x hx y hy hxy
      rw [show dist (fderiv ℝ (fderiv ℝ v) x) (fderiv ℝ (fderiv ℝ v) y) =
        ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ from
          dist_eq_norm (E := E₃ →L[ℝ] E₃ →L[ℝ] ℝ) _ _]
      apply (hbound x hx y hy).trans_lt
      have h := @hmod (dist x y) (by simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hxy)
      exact (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using h)
    exact Metric.uniformContinuousOn_iff.mpr hmain
  have hlim : ∀ x ∈ closure (boundaryReflectUpper a b), ∃ L,
      Tendsto (fderiv ℝ (fderiv ℝ v)) (𝓝[boundaryReflectUpper a b] x) (𝓝 L) := by
    intro x hx
    have : NeBot (𝓝[boundaryReflectUpper a b] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
    exact cauchy_map_iff_exists_tendsto.mp
      ((cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le huc inf_le_right)
  exact ⟨extendFrom (boundaryReflectUpper a b) (fderiv ℝ (fderiv ℝ v)),
    extendFrom_extends huc.continuousOn, continuousOn_extendFrom Subset.rfl hlim⟩

/-- **C² reflection across a flat face.** A function which is C¹ on an open set
containing the flat disk and C² on the open upper slab, with Hölder coordinate second
derivatives there, agrees on the closed upper half of the slab with a C² function on
the whole open slab. -/
theorem boundary_c2_reflection {a b α C : ℝ} (ha : 0 < a) (hb : 0 < b) (hα : 0 < α)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {W : Set (EuclideanSpace ℝ (Fin 3))}
    (hW : IsOpen W)
    (hface : ∀ y : EuclideanSpace ℝ (Fin 3), ‖graphProjectionN 2 y‖ < a →
      y (Fin.last 2) = 0 → y ∈ W)
    (hv1 : ContDiffOn ℝ 1 v W)
    (hv2 : ContDiffOn ℝ 2 v (boundaryReflectUpper a b))
    (hhol : ∀ i j : Fin 3, ∀ x ∈ boundaryReflectUpper a b, ∀ y ∈ boundaryReflectUpper a b,
      |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤ C * dist x y ^ α) :
    ∃ V : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiffOn ℝ 2 V (boundaryReflectSlab a b) ∧
      ∀ y ∈ boundaryReflectSlab a b, 0 ≤ y (Fin.last 2) → V y = v y := by
  -- The positivity of `a` and `b` is not used: for an empty slab the claim is vacuous.
  have _hpos : 0 < a ∧ 0 < b := ⟨ha, hb⟩
  have hO := isOpen_boundaryReflectSlab a b
  have hU := isOpen_boundaryReflectUpper a b
  have hsub : boundaryReflectClosedUpper a b ⊆ boundaryReflectUpper a b ∪ W := by
    intro y hy
    rcases hy.2.1.lt_or_eq with hpos | h0
    · exact Or.inl ⟨hy.1, hpos, hy.2.2⟩
    · exact Or.inr (hface y hy.1 h0.symm)
  have hvd : ∀ y ∈ boundaryReflectUpper a b, HasFDerivAt v (fderiv ℝ v y) y := fun y hy =>
    ((hv2.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)
      |>.hasFDerivAt
  have hdvd : ∀ y ∈ boundaryReflectUpper a b,
      HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) y) y := fun y hy =>
    (((hv2.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn (by norm_num)) y hy)
      |>.differentiableAt (hU.mem_nhds hy) |>.hasFDerivAt
  have hvc : ContinuousOn v (boundaryReflectClosedUpper a b) := by
    intro y hy
    rcases hsub hy with hyU | hyW
    · exact (hv2.continuousOn.continuousAt (hU.mem_nhds hyU)).continuousWithinAt
    · exact (hv1.continuousOn.continuousAt (hW.mem_nhds hyW)).continuousWithinAt
  have hdvc : ContinuousOn (fderiv ℝ v) (boundaryReflectClosedUpper a b) := by
    intro y hy
    rcases hsub hy with hyU | hyW
    · exact ((hv2.continuousOn_fderiv_of_isOpen hU (by norm_num)).continuousAt
        (hU.mem_nhds hyU)).continuousWithinAt
    · exact ((hv1.continuousOn_fderiv_of_isOpen hW le_rfl).continuousAt
        (hW.mem_nhds hyW)).continuousWithinAt
  obtain ⟨S, hSeq, hSc⟩ := boundary_reflect_second_deriv_extension hα hv2 hhol
  have hSc' : ContinuousOn S (boundaryReflectClosedUpper a b) :=
    hSc.mono boundary_reflect_closedUpper_subset_closure
  have hSd : ∀ y ∈ boundaryReflectUpper a b, HasFDerivAt (fderiv ℝ v) (S y) y := by
    intro y hy
    rw [hSeq hy]
    exact hdvd y hy
  -- First gluing step: the reflected function is C¹ with the reflected derivative.
  have step1 := boundary_reflect_glue_hasFDerivAt boundaryReflectScalarOp hvd hvc hdvc
    (fun y _ _ => boundary_reflect_scalarOp_sum (v y))
    (fun y _ _ => boundary_reflect_derivOp_sum (fderiv ℝ v y))
  -- Second gluing step: the reflected derivative is C¹ with the reflected Hessian.
  have step2 := boundary_reflect_glue_hasFDerivAt (boundaryReflectDerivOp boundaryReflectScalarOp)
    hSd hdvc hSc' (fun y _ _ => boundary_reflect_derivOp_sum (fderiv ℝ v y))
    (fun y _ _ => boundary_reflect_derivOp_derivOp_sum (S y))
  have step2c := boundary_reflect_glue_continuousOn
    (boundaryReflectDerivOp (boundaryReflectDerivOp boundaryReflectScalarOp)) hSc'
    (fun y _ _ => boundary_reflect_derivOp_derivOp_sum (S y))
  refine ⟨boundaryReflectGlue boundaryReflectScalarOp v, ?_, ?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun y hy => (step1 y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr ?_ (fun y hy => (step1 y hy).fderiv)
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun y hy => (step2 y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact step2c.congr fun y hy => (step2 y hy).fderiv
  · intro y _ hy0
    rw [boundaryReflectGlue, ite_eq_left hy0]

end LiquidDrop
