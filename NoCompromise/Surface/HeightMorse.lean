module

public import NoCompromise.Surface.Shape
public import NoCompromise.Surface.MorseIndex
public import NoCompromise.Surface.RegularValue

@[expose] public section

/-!
# Height functions, curvature, and Morse index

The sign of Gaussian curvature determines the parity of the Morse index at a
nondegenerate critical point of height. Height is Morse precisely when both
corresponding antipodal directions are regular values of the unit normal.
-/

noncomputable section
open Set Function InnerProductSpace
namespace LiquidDrop

/-- The Hessian of `f|_S` at `p` as a bilinear form on the tangent plane. -/
def tangentHessian (S : Set E₃) (n : E₃ → E₃) (f : E₃ → ℝ) (p : E₃) :
    tangentPlane S p → tangentPlane S p → ℝ :=
  fun X Y => surfaceHessian n f p X Y

/-- The Morse index of `f|_S` at `p`. -/
noncomputable def surfaceIndex (S : Set E₃) (n : E₃ → E₃) (f : E₃ → ℝ) (p : E₃) : ℕ :=
  formIndex (tangentHessian S n f p)

/-- `f|_S` is a Morse function: every critical point is nondegenerate. -/
def IsSurfaceMorse (S : Set E₃) (n : E₃ → E₃) (f : E₃ → ℝ) : Prop :=
  ∀ p, IsSurfaceCriticalPoint S f p → IsNondegenerateForm (tangentHessian S n f p)

private lemma secondFundamentalForm_eq_inner_shape {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p : E₃}
    (hp : p ∈ S) (X Y : tangentPlane S p) :
    secondFundamentalForm n p X Y = inner ℝ (tangentShapeOperator S n p X) Y := by
  change inner ℝ (fderiv ℝ n p X) (Y : E₃) =
    inner ℝ (tangentShapeOperator S n p X : E₃) (Y : E₃)
  rw [fderiv_normal_eq_tangentShapeOperator hS hn hp]

private lemma tangentHessian_height_operator {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p v : E₃}
    (hv : ‖v‖ = 1) (hcrit : IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p) :
    ∃ A : tangentPlane S p →ₗ[ℝ] tangentPlane S p,
      A.IsSymmetric ∧ LinearMap.det A = gaussCurvature S n p ∧
        tangentHessian S n (fun x => inner ℝ x v) p = fun X Y => inner ℝ (A X) Y := by
  let A := (tangentShapeOperator S n p).toLinearMap
  have hA : A.IsSymmetric := by
    intro X Y
    rw [← real_inner_comm X (A Y)]
    exact (secondFundamentalForm_eq_inner_shape hS hn hcrit.1 X Y).symm.trans
      ((secondFundamentalForm_symm hS hn hcrit.1 X.property Y.property).trans
        (secondFundamentalForm_eq_inner_shape hS hn hcrit.1 Y X))
  rcases (isSurfaceCriticalPoint_height_iff hS hn hcrit.1 hv).mp hcrit with he | he
  · refine ⟨-A, ?_, det_neg_of_finrank_two A (hS.finrank_tangentPlane hcrit.1), ?_⟩
    · intro X Y
      simpa only [LinearMap.neg_apply, inner_neg_left, inner_neg_right] using
        congrArg Neg.neg (hA X Y)
    · funext X Y
      change surfaceHessian n (fun x => inner ℝ x v) p X Y = inner ℝ ((-A) X) Y
      rw [surfaceHessian_height_of_eq he hv, LinearMap.neg_apply, inner_neg_left]
      exact congrArg Neg.neg (secondFundamentalForm_eq_inner_shape hS hn hcrit.1 X Y)
  · refine ⟨A, hA, rfl, ?_⟩
    funext X Y
    change surfaceHessian n (fun x => inner ℝ x v) p X Y = inner ℝ (A X) Y
    rw [surfaceHessian_height_of_eq_neg he hv]
    exact secondFundamentalForm_eq_inner_shape hS hn hcrit.1 X Y

-- lem:sign-kappa-index
theorem isNondegenerateForm_tangentHessian_height_iff {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p v : E₃} (hv : ‖v‖ = 1)
    (hcrit : IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p) :
    IsNondegenerateForm (tangentHessian S n (fun x => inner ℝ x v) p) ↔
      gaussCurvature S n p ≠ 0 := by
  obtain ⟨A, _, hdet, hform⟩ := tangentHessian_height_operator hS hn hv hcrit
  rw [hform, isNondegenerateForm_inner_iff, hdet]

theorem sign_gaussCurvature_eq_neg_one_pow_surfaceIndex {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p v : E₃} (hv : ‖v‖ = 1)
    (hcrit : IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p)
    (hκ : gaussCurvature S n p ≠ 0) :
    Real.sign (gaussCurvature S n p) = (-1 : ℝ) ^ surfaceIndex S n (fun x => inner ℝ x v) p := by
  obtain ⟨A, hA, hdet, hform⟩ := tangentHessian_height_operator hS hn hv hcrit
  unfold surfaceIndex
  rw [hform, ← hdet]
  exact sign_det_eq_neg_one_pow_formIndex hA (hS.finrank_tangentPlane hcrit.1)
    (hdet ▸ hκ)

-- lem:critical-normal
theorem setOf_isSurfaceCriticalPoint_height {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {v : E₃} (hv : ‖v‖ = 1) :
    {p | IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p} =
      (S ∩ n ⁻¹' {v}) ∪ (S ∩ n ⁻¹' {-v}) := by
  ext p
  change IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p ↔
    (p ∈ S ∧ n p = v) ∨ (p ∈ S ∧ n p = -v)
  constructor
  · intro hc
    exact ((isSurfaceCriticalPoint_height_iff hS hn hc.1 hv).mp hc).elim
      (fun he => Or.inl ⟨hc.1, he⟩) (fun he => Or.inr ⟨hc.1, he⟩)
  · rintro (⟨hp, he⟩ | ⟨hp, he⟩)
    · exact (isSurfaceCriticalPoint_height_iff hS hn hp hv).mpr (Or.inl he)
    · exact (isSurfaceCriticalPoint_height_iff hS hn hp hv).mpr (Or.inr he)

theorem disjoint_normal_preimage_neg {S : Set E₃} {n : E₃ → E₃} {v : E₃} (hv : ‖v‖ = 1) :
    Disjoint (S ∩ n ⁻¹' {v}) (S ∩ n ⁻¹' {-v}) := by
  apply Set.disjoint_left.mpr
  intro p hp hpn
  have he : v = -v := hp.2.symm.trans hpn.2
  have hz : v = 0 := by
    have : (2 : ℝ) • v = 0 := by simpa [two_smul, ← he] using add_neg_cancel v
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)
  simp [hz] at hv

private lemma normal_map_eq_iff_surjective {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p : E₃} (hp : p ∈ S) :
    (tangentPlane S p).map (fderiv ℝ n p : E₃ →ₗ[ℝ] E₃) = tangentPlane S p ↔
      Surjective (tangentShapeOperator S n p) := by
  constructor
  · intro he Y
    have hy : (Y : E₃) ∈ (tangentPlane S p).map (fderiv ℝ n p : E₃ →ₗ[ℝ] E₃) := by
      rw [he]
      exact Y.property
    obtain ⟨X, hX, hXY⟩ := Submodule.mem_map.mp hy
    refine ⟨⟨X, hX⟩, Subtype.ext ?_⟩
    rw [← fderiv_normal_eq_tangentShapeOperator hS hn hp]
    exact hXY
  · intro hs
    apply le_antisymm
    · rintro Y ⟨X, hX, rfl⟩
      exact hn.shapeOperator_mem hS hp hX
    · intro Y hY
      obtain ⟨X, hX⟩ := hs ⟨Y, hY⟩
      refine Submodule.mem_map.mpr ⟨X, X.property, ?_⟩
      change fderiv ℝ n p X = Y
      rw [fderiv_normal_eq_tangentShapeOperator hS hn hp]
      exact congrArg Subtype.val hX

theorem isSurfaceRegularValue_normal_iff {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) (y : E₃) :
    IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y ↔
      ∀ p ∈ S, n p = y → gaussCurvature S n p ≠ 0 := by
  unfold IsSurfaceRegularValue
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  apply forall_congr'
  intro he
  rw [← he, tangentPlane_sphere_normal_eq hS hn hp,
    normal_map_eq_iff_surjective hS hn hp]
  change Surjective (tangentShapeOperator S n p).toLinearMap ↔
    LinearMap.det (tangentShapeOperator S n p).toLinearMap ≠ 0
  rw [← LinearMap.injective_iff_surjective, ne_eq,
    LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]

theorem isSurfaceMorse_height_iff {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {v : E₃} (hv : ‖v‖ = 1) :
    IsSurfaceMorse S n (fun x => inner ℝ x v) ↔
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n v ∧
        IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n (-v) := by
  rw [isSurfaceRegularValue_normal_iff hS hn, isSurfaceRegularValue_normal_iff hS hn]
  constructor
  · intro hm
    constructor
    · intro p hp he
      have hc := (isSurfaceCriticalPoint_height_iff hS hn hp hv).mpr (Or.inl he)
      exact (isNondegenerateForm_tangentHessian_height_iff hS hn hv hc).mp (hm p hc)
    · intro p hp he
      have hc := (isSurfaceCriticalPoint_height_iff hS hn hp hv).mpr (Or.inr he)
      exact (isNondegenerateForm_tangentHessian_height_iff hS hn hv hc).mp (hm p hc)
  · rintro ⟨hpos, hneg⟩ p hc
    apply (isNondegenerateForm_tangentHessian_height_iff hS hn hv hc).mpr
    exact ((isSurfaceCriticalPoint_height_iff hS hn hc.1 hv).mp hc).elim
      (hpos p hc.1) (hneg p hc.1)

end LiquidDrop
