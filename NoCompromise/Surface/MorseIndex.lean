module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Basic.Real.Sign
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

/-!
# Nondegeneracy and index of bilinear forms (linear algebra for `lem:sign-kappa-index`)

`formIndex B` is the Morse index: the largest dimension of a subspace on which `B` is
negative definite. For a symmetric operator `T` on a two-dimensional inner-product space,
`⟪T ·, ·⟫` is nondegenerate iff `det T ≠ 0`, and then `sign (det T) = (-1) ^ formIndex`.
-/

namespace LiquidDrop

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A bilinear form (given as a curried function) is nondegenerate. -/
def IsNondegenerateForm (B : V → V → ℝ) : Prop :=
  ∀ X, (∀ Y, B X Y = 0) → X = 0

/-- The (Morse) index of a form: the largest dimension of a subspace on which it is
negative definite. -/
noncomputable def formIndex (B : V → V → ℝ) : ℕ :=
  sSup {d | ∃ W : Submodule ℝ V, Module.finrank ℝ W = d ∧
    ∀ x ∈ W, x ≠ 0 → B x x < 0}

private lemma formIndex_bdd (B : V → V → ℝ) :
    BddAbove {d | ∃ W : Submodule ℝ V, Module.finrank ℝ W = d ∧
      ∀ x ∈ W, x ≠ 0 → B x x < 0} := by
  refine ⟨Module.finrank ℝ V, ?_⟩
  rintro d ⟨W, rfl, _⟩
  exact Submodule.finrank_le W

omit [FiniteDimensional ℝ V] in
private lemma formIndex_nonempty (B : V → V → ℝ) :
    Set.Nonempty {d | ∃ W : Submodule ℝ V, Module.finrank ℝ W = d ∧
      ∀ x ∈ W, x ≠ 0 → B x x < 0} := by
  refine ⟨0, ⊥, by simp, ?_⟩
  simp

theorem formIndex_le_finrank (B : V → V → ℝ) : formIndex B ≤ Module.finrank ℝ V := by
  apply csSup_le (formIndex_nonempty B)
  rintro d ⟨W, rfl, _⟩
  exact Submodule.finrank_le W

/-- Nondegeneracy of `⟪T ·, ·⟫` is invertibility of `T` (any finite dimension). -/
theorem isNondegenerateForm_inner_iff (T : V →ₗ[ℝ] V) :
    IsNondegenerateForm (fun X Y => inner ℝ (T X) Y) ↔ LinearMap.det T ≠ 0 := by
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot']
  constructor
  · intro h x hx
    exact h x (by simp [hx])
  · intro h x hx
    exact h x (inner_self_eq_zero.mp (hx (T x)))

/-- A form positive on every nonzero vector has index zero. -/
theorem formIndex_eq_zero_of_pos (B : V → V → ℝ)
    (hB : ∀ x, x ≠ 0 → 0 < B x x) : formIndex B = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le (formIndex_nonempty B)
  rintro d ⟨W, rfl, hW⟩
  have hbot : W = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    by_contra hn
    exact (hB x hn).not_gt (hW x hx hn)
  simp [hbot]

/-- A form negative on every nonzero vector has maximal index. -/
theorem formIndex_eq_finrank_of_neg (B : V → V → ℝ)
    (hB : ∀ x, x ≠ 0 → B x x < 0) : formIndex B = Module.finrank ℝ V := by
  apply le_antisymm (formIndex_le_finrank B)
  apply le_csSup (formIndex_bdd B)
  exact ⟨⊤, by simp, fun x _ hx => hB x hx⟩

set_option linter.unusedSectionVars false in
/-- Scaling a two-dimensional operator by `-1` does not change its determinant. -/
theorem det_neg_of_finrank_two (T : V →ₗ[ℝ] V) (h2 : Module.finrank ℝ V = 2) :
    LinearMap.det (-T) = LinearMap.det T := by
  rw [← neg_one_smul ℝ T, LinearMap.det_smul, h2]
  norm_num

/-- In dimension two, vectors of both signs force index one. -/
theorem formIndex_eq_one_of_mixed (T : V →ₗ[ℝ] V)
    (h2 : Module.finrank ℝ V = 2)
    (hn : ∃ x, inner ℝ (T x) x < 0)
    (hp : ∃ x, 0 < inner ℝ (T x) x) :
    formIndex (fun X Y => inner ℝ (T X) Y) = 1 := by
  obtain ⟨v, hv⟩ := hn
  obtain ⟨w, hw⟩ := hp
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  apply le_antisymm
  · apply csSup_le (formIndex_nonempty _)
    rintro d ⟨W, rfl, hW⟩
    have hle : Module.finrank ℝ W ≤ 2 := h2 ▸ Submodule.finrank_le W
    have hne : Module.finrank ℝ W ≠ 2 := by
      intro he
      have htop := Submodule.eq_top_of_finrank_eq (he.trans h2.symm)
      exact hw.not_gt (hW w (htop ▸ Submodule.mem_top) hw0)
    omega
  · apply le_csSup (formIndex_bdd _)
    refine ⟨Submodule.span ℝ {v}, finrank_span_singleton hv0, ?_⟩
    intro x hx hx0
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ha : a ≠ 0 := by intro h; simp [h] at hx0
    have hneg := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ha) hv
    simpa only [map_smul, real_inner_smul_left, real_inner_smul_right,
      pow_two, mul_assoc] using hneg

private lemma eigenbasis_quadratic_two {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric)
    (h2 : Module.finrank ℝ V = 2) (x : V) :
    inner ℝ (T x) x =
      hT.eigenvalues h2 0 * ((hT.eigenvectorBasis h2).repr x 0) ^ 2 +
      hT.eigenvalues h2 1 * ((hT.eigenvectorBasis h2).repr x 1) ^ 2 := by
  rw [← (hT.eigenvectorBasis h2).repr.inner_map_map, PiLp.inner_apply]
  simp only [hT.eigenvectorBasis_apply_self_apply, Fin.sum_univ_two,
    RCLike.inner_apply, conj_trivial, RCLike.ofReal_real_eq_id, id_eq]
  ring

omit [FiniteDimensional ℝ V] in
private lemma basis_two_coords_ne_zero (b : OrthonormalBasis (Fin 2) ℝ V)
    {x : V} (hx : x ≠ 0) : b.repr x 0 ≠ 0 ∨ b.repr x 1 ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  apply b.repr.injective
  ext i
  fin_cases i
  · simpa using h.1
  · simpa using h.2

private lemma quadratic_two_pos {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < a * x ^ 2 + b * y ^ 2 := by
  rcases hxy with hx | hy
  · exact add_pos_of_pos_of_nonneg (mul_pos ha (sq_pos_of_ne_zero hx))
      (mul_nonneg hb.le (sq_nonneg y))
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (sq_nonneg x))
      (mul_pos hb (sq_pos_of_ne_zero hy))

/-- In dimension two, the sign of the determinant of a symmetric operator is `(-1)^index`. -/
theorem sign_det_eq_neg_one_pow_formIndex {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric)
    (h2 : Module.finrank ℝ V = 2) (hdet : LinearMap.det T ≠ 0) :
    Real.sign (LinearMap.det T) = (-1 : ℝ) ^ formIndex (fun X Y => inner ℝ (T X) Y) := by
  have hd : LinearMap.det T = hT.eigenvalues h2 0 * hT.eigenvalues h2 1 := by
    simpa only [Fin.prod_univ_two, RCLike.ofReal_real_eq_id, id_eq] using
      hT.det_eq_prod_eigenvalues h2
  have h0 : hT.eigenvalues h2 0 ≠ 0 := by
    intro h; apply hdet; simp [hd, h]
  have h1 : hT.eigenvalues h2 1 ≠ 0 := by
    intro h; apply hdet; simp [hd, h]
  have horder : hT.eigenvalues h2 1 ≤ hT.eigenvalues h2 0 :=
    hT.eigenvalues_antitone h2 (by decide : (0 : Fin 2) ≤ 1)
  have he (i : Fin 2) :
      inner ℝ (T (hT.eigenvectorBasis h2 i)) (hT.eigenvectorBasis h2 i) =
        hT.eigenvalues h2 i := by
    rw [hT.apply_eigenvectorBasis h2, real_inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  rcases h0.lt_or_gt with hn0 | hp0
  · have hn1 : hT.eigenvalues h2 1 < 0 := lt_of_le_of_lt horder hn0
    have hi : formIndex (fun X Y => inner ℝ (T X) Y) = 2 := by
      rw [formIndex_eq_finrank_of_neg, h2]
      intro x hx
      rw [eigenbasis_quadratic_two hT h2]
      have h := quadratic_two_pos (neg_pos.mpr hn0) (neg_pos.mpr hn1)
        (basis_two_coords_ne_zero (hT.eigenvectorBasis h2) hx)
      nlinarith
    rw [Real.sign_of_pos (by rw [hd]; exact mul_pos_of_neg_of_neg hn0 hn1), hi]
    norm_num
  · rcases h1.lt_or_gt with hn1 | hp1
    · have hi : formIndex (fun X Y => inner ℝ (T X) Y) = 1 :=
        formIndex_eq_one_of_mixed T h2
          ⟨hT.eigenvectorBasis h2 1, (he 1).symm ▸ hn1⟩
          ⟨hT.eigenvectorBasis h2 0, (he 0).symm ▸ hp0⟩
      rw [Real.sign_of_neg (by rw [hd]; exact mul_neg_of_pos_of_neg hp0 hn1), hi]
      norm_num
    · have hi : formIndex (fun X Y => inner ℝ (T X) Y) = 0 := by
        apply formIndex_eq_zero_of_pos
        intro x hx
        rw [eigenbasis_quadratic_two hT h2]
        exact quadratic_two_pos hp0 hp1 (basis_two_coords_ne_zero (hT.eigenvectorBasis h2) hx)
      rw [Real.sign_of_pos (by rw [hd]; exact mul_pos hp0 hp1), hi]
      norm_num

/-- A symmetric operator of negative determinant in dimension two has index one. -/
theorem formIndex_eq_one_of_det_neg {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric)
    (h2 : Module.finrank ℝ V = 2) (hdet : LinearMap.det T < 0) :
    formIndex (fun X Y => inner ℝ (T X) Y) = 1 := by
  have hs := sign_det_eq_neg_one_pow_formIndex hT h2 hdet.ne
  rw [Real.sign_of_neg hdet] at hs
  have hi := formIndex_le_finrank (fun X Y => inner ℝ (T X) Y)
  rw [h2] at hi
  have hc : formIndex (fun X Y => inner ℝ (T X) Y) = 0 ∨
      formIndex (fun X Y => inner ℝ (T X) Y) = 1 ∨
      formIndex (fun X Y => inner ℝ (T X) Y) = 2 := by omega
  rcases hc with hc | hc | hc
  · norm_num [hc] at hs
  · exact hc
  · norm_num [hc] at hs

end LiquidDrop
