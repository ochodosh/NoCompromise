module

public import NoCompromise.Area.Linear

@[expose] public section

/-!
# Quantitative area bounds for almost-linear maps

The lower and upper stretch bounds are proved from finite-dimensional spectral
algebra. Hausdorff-measure distortion then compares a perturbation with its
linear model, without invoking a nonlinear area formula.
-/
noncomputable section
open MeasureTheory Set Module
open scoped ENNReal NNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The extremal singular values bound every stretch of a planar linear map. -/
lemma singularValues_two_norm_bounds {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin 2)) :
    L.singularValues 1 * ‖x‖ ≤ ‖L x‖ ∧ ‖L x‖ ≤ L.singularValues 0 * ‖x‖ := by
  let T := L.toLinearMap.adjoint.comp L.toLinearMap
  let hT := L.toLinearMap.isSymmetric_adjoint_comp_self
  let b := hT.eigenvectorBasis (by simp : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)
  have hdiag (i : Fin 2) : b.repr (T x) i = L.singularValues i ^ 2 * b.repr x i := by
    rw [L.toLinearMap.sq_singularValues_fin (by simp)]
    exact hT.eigenvectorBasis_apply_self_apply (by simp) x i
  have hnorm : ‖x‖ ^ 2 = (b.repr x 0) ^ 2 + (b.repr x 1) ^ 2 := by
    rw [← b.repr.norm_map x, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hLnorm : ‖L x‖ ^ 2 =
      L.singularValues 0 ^ 2 * (b.repr x 0) ^ 2 +
      L.singularValues 1 ^ 2 * (b.repr x 1) ^ 2 := by
    calc
      ‖L x‖ ^ 2 = inner ℝ (T x) x := by
        simp only [T, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
          ContinuousLinearMap.coe_coe, real_inner_self_eq_norm_sq]
      _ = inner ℝ (b.repr (T x)) (b.repr x) := (b.repr.inner_map_map _ _).symm
      _ = _ := by
        rw [PiLp.inner_apply, Fin.sum_univ_two, hdiag, hdiag]
        simp only [RCLike.inner_apply, conj_trivial, Fin.val_zero, Fin.val_one]
        ring
  have hsv := L.singularValues_antitone (by norm_num : 0 ≤ 1)
  have hsv0 := L.singularValues_nonneg 0
  have hsv1 := L.singularValues_nonneg 1
  have hsq : L.singularValues 1 ^ 2 ≤ L.singularValues 0 ^ 2 :=
    pow_le_pow_left₀ hsv1 hsv 2
  constructor
  · apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [mul_pow, hnorm, hLnorm]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (b.repr x 0))]
  · apply le_of_sq_le_sq _ (mul_nonneg hsv0 (norm_nonneg _))
    rw [mul_pow, hnorm, hLnorm]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (b.repr x 1))]

/-- The largest singular value is at most the operator norm. -/
lemma singularValues_zero_le_norm {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    L.singularValues 0 ≤ ‖L‖ := by
  let T := L.toLinearMap.adjoint.comp L.toLinearMap
  let hT := L.toLinearMap.isSymmetric_adjoint_comp_self
  let b := hT.eigenvectorBasis (by simp : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)
  have hdiag : T (b 0) = L.singularValues 0 ^ 2 • b 0 := by
    rw [L.toLinearMap.sq_singularValues_of_lt (n := 2) (by simp) (i := 0) (by norm_num)]
    exact hT.apply_eigenvectorBasis (by simp) 0
  have hnorm : ‖L (b 0)‖ ^ 2 = L.singularValues 0 ^ 2 := by
    calc
      _ = inner ℝ (T (b 0)) (b 0) := by
        simp only [T, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
          ContinuousLinearMap.coe_coe, real_inner_self_eq_norm_sq]
      _ = _ := by rw [hdiag, real_inner_smul_left, real_inner_self_eq_norm_sq,
        b.norm_eq_one]; ring
  have hle : ‖L (b 0)‖ ≤ ‖L‖ := by simpa only [b.norm_eq_one, mul_one] using L.le_opNorm (b 0)
  exact (le_of_sq_le_sq hnorm.symm.le (norm_nonneg _)).trans hle

/-- Lipschitz distortion for normalized two-dimensional Hausdorff measure. -/
lemma hausdorffMeasure2_image_le_of_lipschitzOn {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin n))} {K : ℝ≥0}
    (hf : LipschitzOnWith K f B) :
    hausdorffMeasure2 m (f '' B) ≤ (K : ℝ≥0∞) ^ 2 * hausdorffMeasure2 n B := by
  unfold hausdorffMeasure2
  simp_rw [Measure.euclideanHausdorffMeasure_def]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc
    _ ≤ _ := mul_le_mul' le_rfl (hf.hausdorffMeasure_image_le (d := 2) (by norm_num))
    _ = _ := by rw [ENNReal.rpow_ofNat]; ac_rfl

/-- A linear perturbation retains its lower stretch minus the perturbation size. -/
lemma almostLinear_lower_stretch {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    {h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))} {ε : ℝ}
    (he : ∀ x ∈ B, ∀ y ∈ B, ‖h x - h y - L (x - y)‖ ≤ ε * ‖x - y‖)
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ B) (hy : y ∈ B) :
    (L.singularValues 1 - ε) * ‖x - y‖ ≤ ‖h x - h y‖ := by
  have hlo := (singularValues_two_norm_bounds L (x - y)).1
  have hn := norm_sub_le (h x - h y) (h x - h y - L (x - y))
  have hid : h x - h y - (h x - h y - L (x - y)) = L (x - y) := by abel
  rw [hid] at hn
  linarith [he x hx y hy]

/-- The inverse on the image is Lipschitz when the error is less than half the lower stretch. -/
lemma almostLinear_injective_inverse {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L)
    {h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))} {ε : ℝ}
    (he : ∀ x ∈ B, ∀ y ∈ B, ‖h x - h y - L (x - y)‖ ≤ ε * ‖x - y‖)
    (hε : ε < L.singularValues 1 / 2) :
    InjOn h B ∧ LipschitzOnWith (Real.toNNReal (2 / L.singularValues 1))
      (Function.invFunOn h B) (h '' B) := by
  have hs := (singularValues_two_pos_and_ordered L hL).1
  have hpos : 0 < L.singularValues 1 - ε := by linarith
  have hinj : InjOn h B := by
    intro x hx y hy hxy
    have hh := almostLinear_lower_stretch L he hx hy
    rw [hxy, sub_self, norm_zero] at hh
    have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  refine ⟨hinj, LipschitzOnWith.of_dist_le_mul ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [hinj.leftInvOn_invFunOn hx, hinj.leftInvOn_invFunOn hy,
    Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hs).2
  have hh := almostLinear_lower_stretch L he hx hy
  have hn := norm_nonneg (x - y)
  have hhalf : L.singularValues 1 / 2 * ‖x - y‖ ≤ ‖h x - h y‖ := by
    nlinarith
  nlinarith

/-- Comparing two parametrizations by their relative upper and lower stretches. -/
lemma hausdorffMeasure2_image_bounds_of_relative_stretch {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L)
    {h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hh : InjOn h B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hst : ∀ x ∈ B, ∀ y ∈ B,
      b * ‖L (x - y)‖ ≤ ‖h x - h y‖ ∧ ‖h x - h y‖ ≤ a * ‖L (x - y)‖) :
    ENNReal.ofReal (b ^ 2) * hausdorffMeasure2 m (L '' B) ≤ hausdorffMeasure2 m (h '' B) ∧
    hausdorffMeasure2 m (h '' B) ≤
      ENNReal.ofReal (a ^ 2) * hausdorffMeasure2 m (L '' B) := by
  have hLin : InjOn L B := hL.injOn
  have hq : LipschitzOnWith (Real.toNNReal a)
      (h ∘ Function.invFunOn L B) (L '' B) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa only [Function.comp_apply, hLin.leftInvOn_invFunOn hx,
      hLin.leftInvOn_invFunOn hy, dist_eq_norm, Real.coe_toNNReal _ ha, ← L.map_sub]
      using (hst x hx y hy).2
  have hp : LipschitzOnWith (Real.toNNReal (1 / b))
      (L ∘ Function.invFunOn h B) (h '' B) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hh.leftInvOn_invFunOn hx,
      hh.leftInvOn_invFunOn hy, dist_eq_norm, Real.coe_toNNReal _ (by positivity : 0 ≤ 1 / b),
      ← L.map_sub]
    rw [div_mul_eq_mul_div, one_mul]
    exact (le_div_iff₀ hb).2 (by simpa only [mul_comm] using (hst x hx y hy).1)
  have hqi : (h ∘ Function.invFunOn L B) '' (L '' B) = h '' B := by
    simp only [Function.comp_def]
    rw [← Set.image_image h (Function.invFunOn L B), hLin.invFunOn_image Subset.rfl]
  have hpi : (L ∘ Function.invFunOn h B) '' (h '' B) = L '' B := by
    simp only [Function.comp_def]
    rw [← Set.image_image L (Function.invFunOn h B), hh.invFunOn_image Subset.rfl]
  have hupper := hausdorffMeasure2_image_le_of_lipschitzOn hq
  have hlower := hausdorffMeasure2_image_le_of_lipschitzOn hp
  rw [hqi] at hupper
  rw [hpi] at hlower
  change _ ≤ ENNReal.ofReal a ^ 2 * _ at hupper
  change _ ≤ ENNReal.ofReal (1 / b) ^ 2 * _ at hlower
  refine ⟨?_, ?_⟩
  · rw [ENNReal.ofReal_pow hb.le]
    calc
      _ ≤ ENNReal.ofReal b ^ 2 *
          (ENNReal.ofReal (1 / b) ^ 2 * hausdorffMeasure2 m (h '' B)) :=
        mul_le_mul' le_rfl hlower
      _ = _ := by
        rw [← mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul hb.le,
          mul_one_div_cancel hb.ne', ENNReal.ofReal_one, one_pow, one_mul]
  · simpa only [ENNReal.ofReal_pow ha] using hupper

/-- Multiplicative area bounds for an almost-linear map; the set need not be measurable. -/
theorem almostLinear_area_multiplicative {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L)
    {h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))} {ε : ℝ} (hε0 : 0 ≤ ε)
    (he : ∀ x ∈ B, ∀ y ∈ B, ‖h x - h y - L (x - y)‖ ≤ ε * ‖x - y‖)
    (hε : ε < L.singularValues 1 / 2) :
    ENNReal.ofReal ((1 - ε / L.singularValues 1) ^ 2 * jacobian2Linear L) * volume B ≤
      hausdorffMeasure2 m (h '' B) ∧
    hausdorffMeasure2 m (h '' B) ≤
      ENNReal.ofReal ((1 + ε / L.singularValues 1) ^ 2 * jacobian2Linear L) * volume B := by
  have hs := (singularValues_two_pos_and_ordered L hL).1
  have hq0 : 0 ≤ ε / L.singularValues 1 := div_nonneg hε0 hs.le
  have hq1 : ε / L.singularValues 1 < 1 := (div_lt_one hs).2 (by linarith)
  have hst : ∀ x ∈ B, ∀ y ∈ B,
      (1 - ε / L.singularValues 1) * ‖L (x - y)‖ ≤ ‖h x - h y‖ ∧
      ‖h x - h y‖ ≤ (1 + ε / L.singularValues 1) * ‖L (x - y)‖ := by
    intro x hx y hy
    have herr : ‖h x - h y - L (x - y)‖ ≤
        ε / L.singularValues 1 * ‖L (x - y)‖ := by
      calc
        _ ≤ ε * ‖x - y‖ := he x hx y hy
        _ = ε / L.singularValues 1 * (L.singularValues 1 * ‖x - y‖) := by
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (singularValues_two_norm_bounds L (x - y)).1 hq0
    have hlo := norm_sub_le (h x - h y) (h x - h y - L (x - y))
    have hup := norm_add_le (h x - h y - L (x - y)) (L (x - y))
    have hid : h x - h y - (h x - h y - L (x - y)) = L (x - y) := by abel
    rw [hid] at hlo
    rw [sub_add_cancel] at hup
    constructor <;> nlinarith
  have ha := hausdorffMeasure2_image_bounds_of_relative_stretch L hL
    (almostLinear_injective_inverse L hL he hε).1 (by linarith : 0 ≤ 1 + ε / L.singularValues 1)
    (by linarith : 0 < 1 - ε / L.singularValues 1) hst
  rw [hausdorffMeasure2_image_linear L hL] at ha
  simpa only [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc] using ha

/-- The elementary scalar estimate producing a linear error in area. -/
lemma almostLinear_scalar_bounds {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hε0 : 0 ≤ ε) (hε : ε < b / 2) :
    a * b - 3 * a * ε ≤ (1 - ε / b) ^ 2 * (a * b) ∧
    (1 + ε / b) ^ 2 * (a * b) ≤ a * b + 3 * a * ε := by
  have hq0 : 0 ≤ ε / b := div_nonneg hε0 hb.le
  have hq1 : ε / b ≤ 1 := (div_le_one hb).2 (by linarith)
  have hlow : 1 - 3 * (ε / b) ≤ (1 - ε / b) ^ 2 := by nlinarith
  have hupp : (1 + ε / b) ^ 2 ≤ 1 + 3 * (ε / b) := by nlinarith
  constructor
  · calc
      _ = (1 - 3 * (ε / b)) * (a * b) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hlow (mul_nonneg ha hb.le)
  · calc
      _ ≤ (1 + 3 * (ε / b)) * (a * b) :=
        mul_le_mul_of_nonneg_right hupp (mul_nonneg ha hb.le)
      _ = _ := by field_simp

/-- A negative error parameter forces the source to contain at most one point. -/
lemma almostLinear_subsingleton_of_error_neg {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    {h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))} {ε : ℝ} (hε : ε < 0)
    (he : ∀ x ∈ B, ∀ y ∈ B, ‖h x - h y - L (x - y)‖ ≤ ε * ‖x - y‖) :
    B.Subsingleton := by
  intro x hx y hy
  have hh := he x hx y hy
  have hz : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y), norm_nonneg (h x - h y - L (x - y))]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Sets containing at most one point have zero normalized Hausdorff area. -/
lemma hausdorffMeasure2_subsingleton {m : ℕ} {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : B.Subsingleton) : hausdorffMeasure2 m B = 0 := by
  have := Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin m))
    (by norm_num : (0 : ℝ) < 2)
  simp [hausdorffMeasure2, Measure.euclideanHausdorffMeasure_def,
    Measure.smul_apply, hB.measure_zero]

/-- The blueprint's almost-linear area estimate, with the explicit constant `3 s₁(L)`.
The estimate holds for arbitrary sets, including nonmeasurable sets, and for every
real error parameter satisfying the stated perturbation hypothesis. -/
theorem almostLinear_area_bounds {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L)
    {h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))} {ε : ℝ}
    (he : ∀ x ∈ B, ∀ y ∈ B, ‖h x - h y - L (x - y)‖ ≤ ε * ‖x - y‖)
    (hε : ε < L.singularValues 1 / 2) :
    ENNReal.ofReal (jacobian2Linear L - 3 * L.singularValues 0 * ε) * volume B ≤
      hausdorffMeasure2 m (h '' B) ∧
    hausdorffMeasure2 m (h '' B) ≤
      ENNReal.ofReal (jacobian2Linear L + 3 * L.singularValues 0 * ε) * volume B := by
  by_cases hε0 : 0 ≤ ε
  · have hm := almostLinear_area_multiplicative L hL hε0 he hε
    have hs := almostLinear_scalar_bounds (L.singularValues_nonneg 0)
      (singularValues_two_pos_and_ordered L hL).1 hε0 hε
    rw [← jacobian2Linear_eq_singularValues L] at hs
    exact ⟨(mul_le_mul' (ENNReal.ofReal_le_ofReal hs.1) le_rfl).trans hm.1,
      hm.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hs.2) le_rfl)⟩
  · have hB := almostLinear_subsingleton_of_error_neg L (lt_of_not_ge hε0) he
    simp [hB.measure_zero volume, hausdorffMeasure2_subsingleton (hB.image h)]

/-- The error constant is uniform on operator-norm bounded families. -/
lemma almostLinear_constant_le {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) {N : ℝ}
    (hN : ‖L‖ ≤ N) : 3 * L.singularValues 0 ≤ 3 * N := by
  linarith [singularValues_zero_le_norm L]

/-- Rank-two form of the complete almost-linear lemma, including the inverse. -/
theorem almostLinear {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : finrank ℝ L.range = 2)
    {h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))} {ε : ℝ}
    (he : ∀ x ∈ B, ∀ y ∈ B, ‖h x - h y - L (x - y)‖ ≤ ε * ‖x - y‖)
    (hε : ε < L.singularValues 1 / 2) :
    InjOn h B ∧ LipschitzOnWith (Real.toNNReal (2 / L.singularValues 1))
      (Function.invFunOn h B) (h '' B) ∧
    ENNReal.ofReal (jacobian2Linear L - 3 * L.singularValues 0 * ε) * volume B ≤
      hausdorffMeasure2 m (h '' B) ∧
    hausdorffMeasure2 m (h '' B) ≤
      ENNReal.ofReal (jacobian2Linear L + 3 * L.singularValues 0 * ε) * volume B := by
  have hinj := (rank_two_iff_injective L).mp hL
  exact ⟨(almostLinear_injective_inverse L hinj he hε).1,
    (almostLinear_injective_inverse L hinj he hε).2, almostLinear_area_bounds L hinj he hε⟩

/-- A uniform version with constant `3 N` for maps whose operator norm is at most `N`.
Thus the blueprint's family with an additional lower singular-value bound has a
uniform constant as well. -/
theorem almostLinear_area_bounds_uniform {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : Function.Injective L) {N : ℝ} (hN : ‖L‖ ≤ N)
    {h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))} {ε : ℝ}
    (he : ∀ x ∈ B, ∀ y ∈ B, ‖h x - h y - L (x - y)‖ ≤ ε * ‖x - y‖)
    (hε : ε < L.singularValues 1 / 2) :
    ENNReal.ofReal (jacobian2Linear L - 3 * N * ε) * volume B ≤
      hausdorffMeasure2 m (h '' B) ∧
    hausdorffMeasure2 m (h '' B) ≤
      ENNReal.ofReal (jacobian2Linear L + 3 * N * ε) * volume B := by
  by_cases hε0 : 0 ≤ ε
  · have hm := almostLinear_area_bounds L hL he hε
    have hc := mul_le_mul_of_nonneg_right (almostLinear_constant_le L hN) hε0
    exact ⟨(mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl).trans hm.1,
      hm.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl)⟩
  · have hB := almostLinear_subsingleton_of_error_neg L (lt_of_not_ge hε0) he
    simp [hB.measure_zero volume, hausdorffMeasure2_subsingleton (hB.image h)]

end LiquidDrop





