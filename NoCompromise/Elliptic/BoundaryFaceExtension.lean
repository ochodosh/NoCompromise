module

public import NoCompromise.Elliptic.BoundaryNeumannIterateC3
public import NoCompromise.Elliptic.BoundaryNeumannReflectC2Interface
public import Mathlib.Topology.ExtendFrom
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

/-!
# Cᵏ extension across the flat face by Hestenes reflection

Let `v` be Cᵏ on the open upper half ball `boundaryHalfBall R`, with all iterated
derivatives of order `≤ k` uniformly continuous there. For nodes `λⱼ ∈ [-1, 0)` and
coefficients `cⱼ` with `∑ⱼ cⱼ λⱼ^m = 1` for `m ≤ k`, the function equal to (the
continuous extension of) `v` for `x₃ > 0` and to `∑ⱼ cⱼ v̄(x₁, x₂, λⱼ x₃)` for
`x₃ ≤ 0` is Cᵏ on `ball 0 R`. The proof is by induction on `k`: the coordinate
partials of the extension are the same construction applied to `∂ᵢv`, with the
coefficients `cⱼ` (tangential `i`) or `cⱼ λⱼ` (normal `i`), and C¹ across the face
follows from `boundary_neumann_c1_glue`. Admissible nodes and coefficients exist for
every `k` (`λⱼ = -1/(j+1)`, Vandermonde system).
-/

noncomputable section
open Filter Metric Set
open scoped Topology
namespace LiquidDrop

/-- The linear map of `ℝ³` multiplying the last coordinate by `l`. -/
def boundaryFaceExtension_sigma (l : ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + (l - 1) •
    (EuclideanSpace.proj (Fin.last 2) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single (Fin.last 2) (1 : ℝ))

lemma boundaryFaceExtension_sigma_apply (l : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    boundaryFaceExtension_sigma l x i = if i = Fin.last 2 then l * x i else x i := by
  by_cases hi : i = Fin.last 2
  · subst hi
    simp [boundaryFaceExtension_sigma]
    ring
  · have hi2 : i ≠ (2 : Fin 3) := hi
    simp [boundaryFaceExtension_sigma, hi2]

lemma boundaryFaceExtension_sigma_face (l : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x (Fin.last 2) = 0) : boundaryFaceExtension_sigma l x = x := by
  ext i
  rw [boundaryFaceExtension_sigma_apply]
  split_ifs with hi
  · subst hi
    have hx2 : x (2 : Fin 3) = 0 := hx
    simp [hx2]
  · rfl

lemma boundaryFaceExtension_sigma_single (l : ℝ) (i : Fin 3) :
    boundaryFaceExtension_sigma l (EuclideanSpace.single i 1) =
      (if i = Fin.last 2 then l else 1) • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  rw [boundaryFaceExtension_sigma_apply]
  by_cases hj : j = i
  · subst hj
    split_ifs <;> simp
  · split_ifs <;> simp [hj]

lemma boundaryFaceExtension_norm_sigma_le {l : ℝ} (hl : -1 ≤ l ∧ l < 0)
    (x : EuclideanSpace ℝ (Fin 3)) : ‖boundaryFaceExtension_sigma l x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [boundaryFaceExtension_sigma_apply]
  split_ifs
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, mul_pow]
    have hl2 : l ^ 2 ≤ 1 := by nlinarith [hl.1, hl.2]
    exact mul_le_of_le_one_left (sq_nonneg _) hl2
  · exact le_rfl

/-- The open lower half ball. -/
def boundaryFaceExtension_lower (R : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ball 0 R ∩ {x | x (Fin.last 2) < 0}

lemma boundaryFaceExtension_isOpen_lower (R : ℝ) : IsOpen (boundaryFaceExtension_lower R) :=
  isOpen_ball.inter (isOpen_lt (EuclideanSpace.proj (Fin.last 2)).continuous continuous_const)

lemma boundaryFaceExtension_convex_lower (R : ℝ) :
    Convex ℝ (boundaryFaceExtension_lower R) := by
  refine (convex_ball 0 R).inter ?_
  have h : {x : EuclideanSpace ℝ (Fin 3) | x (Fin.last 2) < 0} =
      (EuclideanSpace.proj (Fin.last 2) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).toLinearMap ⁻¹'
        Iio 0 := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_Iio]
    rfl
  rw [h]
  exact (convex_Iio _).linear_preimage _

lemma boundaryFaceExtension_sigma_mapsTo {R l : ℝ} (hl : -1 ≤ l ∧ l < 0) :
    MapsTo (boundaryFaceExtension_sigma l) (boundaryFaceExtension_lower R)
      (boundaryHalfBall R) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff]
    exact (boundaryFaceExtension_norm_sigma_le hl x).trans_lt (mem_ball_zero_iff.1 hx.1)
  · change 0 < boundaryFaceExtension_sigma l x (Fin.last 2)
    simp only [boundaryFaceExtension_sigma_apply, ↓reduceIte]
    exact mul_pos_of_neg_of_neg hl.2 hx.2

lemma boundaryFaceExtension_ball_subset (R : ℝ) :
    ball (0 : EuclideanSpace ℝ (Fin 3)) R ⊆
      closure (boundaryHalfBall R) ∪ closure (boundaryFaceExtension_lower R) := by
  intro x hx
  by_cases hp : 0 ≤ x (Fin.last 2)
  · exact Or.inl (boundary_neumann_reflect_mem_closure hx hp)
  · exact Or.inr (subset_closure ⟨hx, lt_of_not_ge hp⟩)

/-- A function uniformly continuous on the half ball has a limit at every point of the
closure. -/
lemma boundaryFaceExtension_exists_tendsto {R : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : UniformContinuousOn v (boundaryHalfBall R)) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ closure (boundaryHalfBall R)) :
    ∃ y, Tendsto v (𝓝[boundaryHalfBall R] x) (𝓝 y) := by
  have := mem_closure_iff_nhdsWithin_neBot.mp hx
  apply cauchy_map_iff_exists_tendsto.mp
  refine ⟨inferInstance, ?_⟩
  rw [prod_map_map_eq]
  refine Tendsto.mono_left hu (le_inf ?_ ?_)
  · exact (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds).trans (cauchy_nhds (a := x)).2
  · rw [← prod_principal_principal]
    exact Filter.prod_mono (le_principal_iff.2 self_mem_nhdsWithin)
      (le_principal_iff.2 self_mem_nhdsWithin)

lemma boundaryFaceExtension_bar_continuousOn {R : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : UniformContinuousOn v (boundaryHalfBall R)) :
    ContinuousOn (extendFrom (boundaryHalfBall R) v) (closure (boundaryHalfBall R)) :=
  continuousOn_extendFrom subset_rfl fun _ hx => boundaryFaceExtension_exists_tendsto hu hx

lemma boundaryFaceExtension_bar_eq {R : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : UniformContinuousOn v (boundaryHalfBall R)) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ boundaryHalfBall R) : extendFrom (boundaryHalfBall R) v x = v x :=
  extendFrom_extends hu.continuousOn x hx

/-- The Hestenes extension of `v` across the flat face, with nodes `l` and
coefficients `c`. -/
def boundaryFaceExtension_ext (R : ℝ) {n : ℕ} (l c : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  if 0 < x (Fin.last 2) then extendFrom (boundaryHalfBall R) v x
  else ∑ j, c j * extendFrom (boundaryHalfBall R) v (boundaryFaceExtension_sigma (l j) x)

lemma boundaryFaceExtension_ext_eq {R : ℝ} {n : ℕ} {l c : Fin n → ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : UniformContinuousOn v (boundaryHalfBall R))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall R) :
    boundaryFaceExtension_ext R l c v x = v x := by
  have hp : 0 < x (Fin.last 2) := hx.2
  simp only [boundaryFaceExtension_ext, hp, ↓reduceIte, boundaryFaceExtension_bar_eq hu hx]

lemma boundaryFaceExtension_ext_eq_lower {R : ℝ} {n : ℕ} {l c : Fin n → ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hl : ∀ j, -1 ≤ l j ∧ l j < 0)
    (hu : UniformContinuousOn v (boundaryHalfBall R))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryFaceExtension_lower R) :
    boundaryFaceExtension_ext R l c v x = ∑ j, c j * v (boundaryFaceExtension_sigma (l j) x) := by
  have hp : ¬ 0 < x (Fin.last 2) := not_lt.2 (le_of_lt hx.2)
  simp only [boundaryFaceExtension_ext, hp, ↓reduceIte]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [boundaryFaceExtension_bar_eq hu (boundaryFaceExtension_sigma_mapsTo (hl j) hx)]

/-- Continuity of the extension on the two closed half balls. -/
lemma boundaryFaceExtension_continuousOn {R : ℝ} {n : ℕ} {l c : Fin n → ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hl : ∀ j, -1 ≤ l j ∧ l j < 0) (hc : ∑ j, c j = 1)
    (hu : UniformContinuousOn v (boundaryHalfBall R)) :
    ContinuousOn (boundaryFaceExtension_ext R l c v)
      (closure (boundaryHalfBall R) ∪ closure (boundaryFaceExtension_lower R)) := by
  have hvb := boundaryFaceExtension_bar_continuousOn hu
  have hup : ContinuousOn (boundaryFaceExtension_ext R l c v) (closure (boundaryHalfBall R)) := by
    refine hvb.congr fun x hx => ?_
    have hx0 : 0 ≤ x (Fin.last 2) :=
      closure_minimal (fun y hy => le_of_lt hy.2)
        (isClosed_le continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous) hx
    by_cases hp : 0 < x (Fin.last 2)
    · simp only [boundaryFaceExtension_ext, hp, ↓reduceIte]
    · have hz : x (Fin.last 2) = 0 := le_antisymm (not_lt.1 hp) hx0
      simp only [boundaryFaceExtension_ext, hp, ↓reduceIte, boundaryFaceExtension_sigma_face _ hz,
        ← Finset.sum_mul, hc, one_mul]
  have hlo : ContinuousOn (boundaryFaceExtension_ext R l c v)
      (closure (boundaryFaceExtension_lower R)) := by
    have hmaps : ∀ j, MapsTo (boundaryFaceExtension_sigma (l j))
        (closure (boundaryFaceExtension_lower R)) (closure (boundaryHalfBall R)) := fun j =>
      (boundaryFaceExtension_sigma_mapsTo (hl j)).closure
        (boundaryFaceExtension_sigma (l j)).continuous
    have hs : ContinuousOn (fun x => ∑ j, c j * extendFrom (boundaryHalfBall R) v
        (boundaryFaceExtension_sigma (l j) x)) (closure (boundaryFaceExtension_lower R)) :=
      continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
        (hvb.comp (boundaryFaceExtension_sigma (l j)).continuous.continuousOn (hmaps j))
    refine hs.congr fun x hx => ?_
    have hx0 : x (Fin.last 2) ≤ 0 :=
      closure_minimal (fun y hy => le_of_lt hy.2)
        (isClosed_le (EuclideanSpace.proj (Fin.last 2)).continuous continuous_const) hx
    simp only [boundaryFaceExtension_ext, not_lt.2 hx0, ↓reduceIte]
  exact hup.union_of_isClosed hlo isClosed_closure isClosed_closure

lemma boundaryFaceExtension_uc_zero {S : Set (EuclideanSpace ℝ (Fin 3))}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : UniformContinuousOn (iteratedFDeriv ℝ 0 v) S) :
    UniformContinuousOn v S := by
  have := (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin 3)) ℝ).isometry.uniformContinuous
    |>.comp_uniformContinuousOn h
  refine this.congr fun x _ => ?_
  simp [iteratedFDeriv_zero_eq_comp]

/-- The coefficients for the `i`-th partial: `cⱼ λⱼ` for the normal direction and
`cⱼ` for tangential directions. -/
def boundaryFaceExtension_coef {n : ℕ} (l c : Fin n → ℝ) (i : Fin 3) : Fin n → ℝ :=
  fun j => if i = Fin.last 2 then c j * l j else c j

lemma boundaryFaceExtension_coef_moments {n k : ℕ} {l c : Fin n → ℝ}
    (hc : ∀ m ≤ k + 1, ∑ j, c j * l j ^ m = 1) (i : Fin 3) :
    ∀ m ≤ k, ∑ j, boundaryFaceExtension_coef l c i j * l j ^ m = 1 := by
  intro m hm
  by_cases hi : i = Fin.last 2
  · simp only [boundaryFaceExtension_coef, hi, ↓reduceIte]
    rw [← hc (m + 1) (by omega)]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [boundaryFaceExtension_coef, hi, ↓reduceIte]
    exact hc m (by omega)

lemma boundaryFaceExtension_uc_compLeft {m : ℕ} (i : Fin 3)
    {A : EuclideanSpace ℝ (Fin 3) → ContinuousMultilinearMap ℝ
      (fun _ : Fin m => EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)}
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : UniformContinuousOn A S) :
    UniformContinuousOn (fun x => (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single i (1 : ℝ))).compContinuousMultilinearMap (A x)) S := by
  have := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin m => EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) ℝ
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))).uniformContinuous
    |>.comp_uniformContinuousOn h
  exact this

lemma boundaryFaceExtension_uc_fderiv {m : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin 3))}
    (h : UniformContinuousOn (iteratedFDeriv ℝ (m + 1) v) S) :
    UniformContinuousOn (iteratedFDeriv ℝ m (fun y => fderiv ℝ v y)) S := by
  have := (continuousMultilinearCurryRightEquiv' ℝ m (EuclideanSpace ℝ (Fin 3)) ℝ).isometry
    |>.uniformContinuous.comp_uniformContinuousOn h
  refine this.congr fun x _ => ?_
  simp only [Function.comp_apply, iteratedFDeriv_succ_eq_comp_right]
  simp

/-- Regularity of a coordinate partial of `v`. -/
lemma boundaryFaceExtension_partial_reg {R : ℝ} {k : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : ContDiffOn ℝ (k + 1) v (boundaryHalfBall R))
    (hu : ∀ m ≤ k + 1, UniformContinuousOn (iteratedFDeriv ℝ m v) (boundaryHalfBall R))
    (i : Fin 3) :
    ContDiffOn ℝ k (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)) (boundaryHalfBall R) ∧
      ∀ m ≤ k, UniformContinuousOn
        (iteratedFDeriv ℝ m (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)))
        (boundaryHalfBall R) := by
  have hS := isOpen_boundaryHalfBall R
  have hd : ContDiffOn ℝ k (fun y => fderiv ℝ v y) (boundaryHalfBall R) :=
    hv.fderiv_of_isOpen hS le_rfl
  refine ⟨hd.clm_apply contDiffOn_const, fun m hm => ?_⟩
  refine (boundaryFaceExtension_uc_compLeft i
    (boundaryFaceExtension_uc_fderiv (hu (m + 1) (by omega)))).congr fun x hx => ?_
  have := ContinuousLinearMap.iteratedFDerivWithin_comp_left
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))) (hd x hx)
    hS.uniqueDiffOn hx (i := m) (by exact_mod_cast hm)
  rw [iteratedFDerivWithin_of_isOpen m hS hx, iteratedFDerivWithin_of_isOpen m hS hx] at this
  exact this.symm

/-- The derivative of the extension on the two open half balls: its `i`-th entry is the
extension of `∂ᵢv` with the coefficients `boundaryFaceExtension_coef l c i`. -/
lemma boundaryFaceExtension_hasFDerivAt {R : ℝ} {n : ℕ} {l c : Fin n → ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hl : ∀ j, -1 ≤ l j ∧ l j < 0)
    (hvd : DifferentiableOn ℝ v (boundaryHalfBall R))
    (hu : UniformContinuousOn v (boundaryHalfBall R))
    (hup : ∀ i : Fin 3, UniformContinuousOn
      (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)) (boundaryHalfBall R))
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ boundaryHalfBall R ∪ boundaryFaceExtension_lower R) :
    HasFDerivAt (boundaryFaceExtension_ext R l c v)
      (∑ i, boundaryFaceExtension_ext R l (boundaryFaceExtension_coef l c i)
        (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)) x •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) x := by
  have hS := isOpen_boundaryHalfBall R
  have hT := boundaryFaceExtension_isOpen_lower R
  rcases hx with hx | hx
  · have heq : boundaryFaceExtension_ext R l c v =ᶠ[𝓝 x] v := by
      filter_upwards [hS.mem_nhds hx] with y hy
      exact boundaryFaceExtension_ext_eq hu hy
    have hv' : HasFDerivAt v (fderiv ℝ v x) x :=
      ((hvd x hx).differentiableAt (hS.mem_nhds hx)).hasFDerivAt
    have hD : fderiv ℝ v x = ∑ i, boundaryFaceExtension_ext R l (boundaryFaceExtension_coef l c i)
        (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)) x •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := by
      rw [boundaryNeumannIterateC3_functional_eq_sum (fderiv ℝ v x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [boundaryFaceExtension_ext_eq (hup i) hx]
    rw [← hD]
    exact hv'.congr_of_eventuallyEq heq
  · have heq : boundaryFaceExtension_ext R l c v =ᶠ[𝓝 x]
        fun y => ∑ j, c j * v (boundaryFaceExtension_sigma (l j) y) := by
      filter_upwards [hT.mem_nhds hx] with y hy
      exact boundaryFaceExtension_ext_eq_lower hl hu hy
    have hσ : ∀ j, boundaryFaceExtension_sigma (l j) x ∈ boundaryHalfBall R := fun j =>
      boundaryFaceExtension_sigma_mapsTo (hl j) hx
    have hvj : ∀ j, HasFDerivAt (fun y => v (boundaryFaceExtension_sigma (l j) y))
        ((fderiv ℝ v (boundaryFaceExtension_sigma (l j) x)).comp
          (boundaryFaceExtension_sigma (l j))) x := fun j =>
      (((hvd _ (hσ j)).differentiableAt (hS.mem_nhds (hσ j))).hasFDerivAt).comp x
        (boundaryFaceExtension_sigma (l j)).hasFDerivAt
    have hsum : HasFDerivAt (fun y => ∑ j, c j * v (boundaryFaceExtension_sigma (l j) y))
        (∑ j, c j • (fderiv ℝ v (boundaryFaceExtension_sigma (l j) x)).comp
          (boundaryFaceExtension_sigma (l j))) x :=
      HasFDerivAt.fun_sum fun j _ => (hvj j).const_mul (c j)
    have hD : (∑ j, c j • (fderiv ℝ v (boundaryFaceExtension_sigma (l j) x)).comp
          (boundaryFaceExtension_sigma (l j))) =
        ∑ i, boundaryFaceExtension_ext R l (boundaryFaceExtension_coef l c i)
        (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)) x •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := by
      rw [boundaryNeumannIterateC3_functional_eq_sum (∑ j, c j • _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [boundaryFaceExtension_ext_eq_lower hl (hup i) hx]
      congr 1
      simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
        Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        boundaryFaceExtension_sigma_single, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hi : i = Fin.last 2
      · simp only [boundaryFaceExtension_coef, hi, ↓reduceIte]
        ring
      · simp only [boundaryFaceExtension_coef, hi, ↓reduceIte, one_mul]
    rw [← hD]
    exact hsum.congr_of_eventuallyEq heq

/-- The Hestenes extension is Cᵏ on the ball, for any admissible nodes and
coefficients. -/
lemma boundaryFaceExtension_contDiffOn {R : ℝ} (k : ℕ) :
    ∀ {n : ℕ} {l c : Fin n → ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ},
      (∀ j, -1 ≤ l j ∧ l j < 0) → (∀ m ≤ k, ∑ j, c j * l j ^ m = 1) →
      ContDiffOn ℝ k v (boundaryHalfBall R) →
      (∀ m ≤ k, UniformContinuousOn (iteratedFDeriv ℝ m v) (boundaryHalfBall R)) →
      ContDiffOn ℝ k (boundaryFaceExtension_ext R l c v) (ball 0 R) := by
  induction k with
  | zero =>
    intro n l c v hl hc _ hu
    have hc0 : ∑ j, c j = 1 := by simpa using hc 0 le_rfl
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (boundaryFaceExtension_continuousOn hl hc0
      (boundaryFaceExtension_uc_zero (hu 0 le_rfl))).mono (boundaryFaceExtension_ball_subset R)
  | succ k ih =>
    intro n l c v hl hc hv hu
    have hv1 : ContDiffOn ℝ (k + 1) v (boundaryHalfBall R) := by exact_mod_cast hv
    have hvd : DifferentiableOn ℝ v (boundaryHalfBall R) := hv1.differentiableOn (by simp)
    have hu0 : UniformContinuousOn v (boundaryHalfBall R) :=
      boundaryFaceExtension_uc_zero (hu 0 (Nat.zero_le _))
    have hc0 : ∑ j, c j = 1 := by simpa using hc 0 (Nat.zero_le _)
    have hpi := boundaryFaceExtension_partial_reg hv1 hu
    have hup : ∀ i : Fin 3, UniformContinuousOn
        (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)) (boundaryHalfBall R) := fun i =>
      boundaryFaceExtension_uc_zero ((hpi i).2 0 (Nat.zero_le _))
    have hci := boundaryFaceExtension_coef_moments hc
    have hPk : ∀ i : Fin 3, ContDiffOn ℝ k (boundaryFaceExtension_ext R l
        (boundaryFaceExtension_coef l c i) (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)))
        (ball 0 R) := fun i => ih hl (hci i) (hpi i).1 (hpi i).2
    have hPc : ∀ i : Fin 3, ContinuousOn (boundaryFaceExtension_ext R l
        (boundaryFaceExtension_coef l c i) (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)))
        (closure (boundaryHalfBall R) ∪ closure (boundaryFaceExtension_lower R)) := fun i =>
      boundaryFaceExtension_continuousOn hl (by simpa using hci i 0 (Nat.zero_le _)) (hup i)
    have hD : ContinuousOn (fun x => ∑ i, boundaryFaceExtension_ext R l
        (boundaryFaceExtension_coef l c i) (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)) x •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ))
        (closure (boundaryHalfBall R) ∪ closure (boundaryFaceExtension_lower R)) :=
      continuousOn_finsetSum _ fun i _ => (hPc i).smul continuousOn_const
    obtain ⟨-, hder⟩ := boundary_neumann_c1_glue (isOpen_boundaryHalfBall R)
      (boundaryFaceExtension_isOpen_lower R) (convex_boundaryHalfBall R)
      (boundaryFaceExtension_convex_lower R) isOpen_ball (boundaryFaceExtension_ball_subset R)
      (boundaryFaceExtension_continuousOn hl hc0 hu0) hD
      (fun x hx => boundaryFaceExtension_hasFDerivAt hl hvd hu0 hup hx)
    have hpart : ∀ i : Fin 3, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) R,
        fderiv ℝ (boundaryFaceExtension_ext R l c v) x (EuclideanSpace.single i 1) =
          boundaryFaceExtension_ext R l (boundaryFaceExtension_coef l c i)
            (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)) x := by
      intro i x hx
      rw [(hder x hx).fderiv]
      simp
    have := boundaryNeumannIterateC3_contDiffOn_succ isOpen_ball
      (fun x hx => (hder x hx).differentiableAt.differentiableWithinAt)
      (fun i => (hPk i).congr fun x hx => hpart i x hx)
    exact_mod_cast this

/-- Admissible nodes and coefficients exist for every order: `λⱼ = -1/(j+1)` and `c`
solving the (invertible) transposed Vandermonde system. -/
lemma boundaryFaceExtension_exists_coeffs (k : ℕ) :
    ∃ l c : Fin (k + 1) → ℝ, (∀ j, -1 ≤ l j ∧ l j < 0) ∧ ∀ m ≤ k, ∑ j, c j * l j ^ m = 1 := by
  let l : Fin (k + 1) → ℝ := fun j => -1 / ((j : ℝ) + 1)
  have hinj : Function.Injective l := by
    intro a b hab
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    simp only [l, neg_div, neg_inj] at hab
    rw [div_eq_div_iff ha.ne' hb.ne', one_mul, one_mul] at hab
    exact Fin.ext (by exact_mod_cast (add_right_cancel hab).symm)
  let V : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := (Matrix.vandermonde l).transpose
  have hV : IsUnit V.det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    exact Matrix.det_vandermonde_ne_zero_iff.2 hinj
  refine ⟨l, V⁻¹.mulVec (fun _ => 1), fun j => ⟨?_, ?_⟩, fun m hm => ?_⟩
  · have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ j)]
    simp only [l, neg_div, neg_le_neg_iff]
    exact (div_le_one (by linarith)).2 hj
  · have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    simp only [l, neg_div, neg_lt_zero]
    exact div_pos one_pos hj
  · have h1 : V.mulVec (V⁻¹.mulVec (fun _ => (1 : ℝ))) = fun _ => 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V hV, Matrix.one_mulVec]
    have h2 := congrFun h1 ⟨m, by omega⟩
    refine Eq.trans ?_ h2
    simp only [Matrix.mulVec, dotProduct, V, Matrix.transpose_apply, Matrix.vandermonde_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Cᵏ extension across the flat face (Hestenes reflection): a function which is Cᵏ on
the open upper half ball, with uniformly continuous iterated derivatives of order
`≤ k`, agrees there with a function which is Cᵏ on the whole ball. -/
theorem boundary_face_extension {k : ℕ} {R : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : ContDiffOn ℝ k v (boundaryHalfBall R))
    (hu : ∀ m ≤ k, UniformContinuousOn (iteratedFDeriv ℝ m v) (boundaryHalfBall R)) :
    ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, EqOn w v (boundaryHalfBall R) ∧
      ContDiffOn ℝ k w (ball 0 R) := by
  obtain ⟨l, c, hl, hc⟩ := boundaryFaceExtension_exists_coeffs k
  exact ⟨boundaryFaceExtension_ext R l c v,
    fun x hx => boundaryFaceExtension_ext_eq
      (boundaryFaceExtension_uc_zero (hu 0 (Nat.zero_le _))) hx,
    boundaryFaceExtension_contDiffOn k hl hc hv hu⟩

/-- The Cᵏ extension across the flat face keeps a Hölder bound on the `k`-th
derivative on the closed upper half of the ball. -/
theorem boundary_face_extension_holder {k : ℕ} {R α C : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : ContDiffOn ℝ k v (boundaryHalfBall R))
    (hu : ∀ m ≤ k, UniformContinuousOn (iteratedFDeriv ℝ m v) (boundaryHalfBall R))
    (hhol : ∀ x ∈ boundaryHalfBall R, ∀ y ∈ boundaryHalfBall R,
      ‖iteratedFDeriv ℝ k v x - iteratedFDeriv ℝ k v y‖ ≤ C * dist x y ^ α) (hα : 0 < α) :
    ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, EqOn w v (boundaryHalfBall R) ∧
      ContDiffOn ℝ k w (ball 0 R) ∧
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) R, 0 ≤ x (Fin.last 2) →
        ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) R, 0 ≤ y (Fin.last 2) →
          ‖iteratedFDeriv ℝ k w x - iteratedFDeriv ℝ k w y‖ ≤ C * dist x y ^ α := by
  obtain ⟨w, hwv, hw⟩ := boundary_face_extension hv hu
  refine ⟨w, hwv, hw, fun x hx hx0 y hy hy0 => ?_⟩
  have hS := isOpen_boundaryHalfBall R
  have hsub : boundaryHalfBall R ⊆ ball 0 R := inter_subset_left
  have hDc : ContinuousOn (iteratedFDeriv ℝ k w) (ball 0 R) :=
    ((hw.continuousOn_iteratedFDerivWithin le_rfl isOpen_ball.uniqueDiffOn).congr
      fun z hz => (iteratedFDerivWithin_of_isOpen k isOpen_ball hz).symm)
  have hDeq : EqOn (iteratedFDeriv ℝ k w) (iteratedFDeriv ℝ k v) (boundaryHalfBall R) := by
    intro z hz
    have h : w =ᶠ[𝓝 z] v := (hS.eventually_mem hz).mono fun y hy => hwv hy
    exact (h.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds
  have hxc := boundary_neumann_reflect_mem_closure hx hx0
  have hyc := boundary_neumann_reflect_mem_closure hy hy0
  have : NeBot (𝓝[boundaryHalfBall R] x) := mem_closure_iff_nhdsWithin_neBot.mp hxc
  have : NeBot (𝓝[boundaryHalfBall R] y) := mem_closure_iff_nhdsWithin_neBot.mp hyc
  let F := 𝓝[boundaryHalfBall R] x ×ˢ 𝓝[boundaryHalfBall R] y
  have hx' : Tendsto (iteratedFDeriv ℝ k w) (𝓝[boundaryHalfBall R] x)
      (𝓝 (iteratedFDeriv ℝ k w x)) :=
    ((hDc x hx).mono hsub).tendsto
  have hy' : Tendsto (iteratedFDeriv ℝ k w) (𝓝[boundaryHalfBall R] y)
      (𝓝 (iteratedFDeriv ℝ k w y)) :=
    ((hDc y hy).mono hsub).tendsto
  have hl : Tendsto (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ‖iteratedFDeriv ℝ k w p.1 - iteratedFDeriv ℝ k w p.2‖) F
      (𝓝 ‖iteratedFDeriv ℝ k w x - iteratedFDeriv ℝ k w y‖) :=
    ((hx'.comp tendsto_fst).sub (hy'.comp tendsto_snd)).norm
  have hd : Tendsto (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      dist p.1 p.2) F (𝓝 (dist x y)) :=
    (tendsto_fst.mono_right nhdsWithin_le_nhds).dist (tendsto_snd.mono_right nhdsWithin_le_nhds)
  have hr : Tendsto (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      C * dist p.1 p.2 ^ α) F (𝓝 (C * dist x y ^ α)) :=
    (hd.rpow_const (Or.inr hα.le)).const_mul C
  refine le_of_tendsto_of_tendsto hl hr ?_
  filter_upwards [prod_mem_prod self_mem_nhdsWithin self_mem_nhdsWithin] with p hp
  rw [hDeq hp.1, hDeq hp.2]
  exact hhol p.1 hp.1 p.2 hp.2

end LiquidDrop
