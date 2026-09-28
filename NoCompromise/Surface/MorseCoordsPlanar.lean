import NoCompromise.Surface.MorseCoords
import NoCompromise.Surface.MorseSurfaceChart

/-!
# The planar Morse lemma `lem:morse-coords`

Assembly of the ingredients of `NoCompromise.Surface.MorseCoords`: a linear change of
coordinates making the first pivot nonzero, the completion-of-squares chart, and the
identification of the signs of the two pivots with `formIndex`. The chart regularity is
C¹ pending the user's wording decision.
-/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The linear map of the plane with matrix `[[a, b], [c, d]]`, used for the initial
linear coordinates in `lem:morse-coords`. -/
def morsePlaneLin (a b c d : ℝ) : E2 →L[ℝ] E2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2 ![a * u 0 + b * u 1, c * u 0 + d * u 1]
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro r x
        ext i
        fin_cases i <;> simp <;> ring }

@[simp] theorem morsePlaneLin_apply_zero (a b c d : ℝ) (u : E2) :
    morsePlaneLin a b c d u 0 = a * u 0 + b * u 1 := rfl

@[simp] theorem morsePlaneLin_apply_one (a b c d : ℝ) (u : E2) :
    morsePlaneLin a b c d u 1 = c * u 0 + d * u 1 := rfl

/-- A plane linear map of nonzero determinant is injective (`lem:morse-coords`). -/
theorem morsePlaneLin_injective {a b c d : ℝ} (h : a * d - b * c ≠ 0) :
    Function.Injective (morsePlaneLin a b c d) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h0 : a * x 0 + b * x 1 = 0 := by
    simpa using congrArg (fun y : E2 => y 0) hx
  have h1 : c * x 0 + d * x 1 = 0 := by
    simpa using congrArg (fun y : E2 => y 1) hx
  have hx0 : (a * d - b * c) * x 0 = 0 := by linear_combination d * h0 - b * h1
  have hx1 : (a * d - b * c) * x 1 = 0 := by linear_combination a * h1 - c * h0
  ext i
  fin_cases i
  · simpa using (mul_eq_zero.mp hx0).resolve_left h
  · simpa using (mul_eq_zero.mp hx1).resolve_left h

/-- The plane linear isomorphism with matrix `[[a, b], [c, d]]` of nonzero determinant,
for the initial linear coordinates in `lem:morse-coords`. -/
def morsePlaneEquiv (a b c d : ℝ) (h : a * d - b * c ≠ 0) : E2 ≃L[ℝ] E2 :=
  (LinearEquiv.ofBijective (morsePlaneLin a b c d).toLinearMap
    ⟨morsePlaneLin_injective h,
      LinearMap.surjective_of_injective (morsePlaneLin_injective h)⟩).toContinuousLinearEquiv

theorem morsePlaneEquiv_apply (a b c d : ℝ) (h : a * d - b * c ≠ 0) (u : E2) :
    morsePlaneEquiv a b c d h u = morsePlaneLin a b c d u := rfl

/-- A pair of C¹ conditions for an open partial homeomorphism of the plane and its
inverse, as in `lem:morse-coords` (C¹ pending the user's wording decision). -/
def IsMorseC1Chart (e : OpenPartialHomeomorph E2 E2) : Prop :=
  ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target

/-- Composition preserves the C¹ chart conditions of `lem:morse-coords`. -/
theorem IsMorseC1Chart.trans {e₁ e₂ : OpenPartialHomeomorph E2 E2}
    (h1 : IsMorseC1Chart e₁) (h2 : IsMorseC1Chart e₂) : IsMorseC1Chart (e₁.trans e₂) := by
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source]
    exact h2.1.comp (h1.1.mono inter_subset_left) (fun x hx => hx.2)
  · rw [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.trans_target]
    exact h1.2.comp (h2.2.mono inter_subset_left) (fun x hx => hx.2)

/-- A continuous linear isomorphism is a C¹ chart for `lem:morse-coords`. -/
theorem isMorseC1Chart_linearEquiv (L : E2 ≃L[ℝ] E2) :
    IsMorseC1Chart L.toHomeomorph.toOpenPartialHomeomorph := by
  refine ⟨?_, ?_⟩
  · simpa using L.contDiff.contDiffOn
  · simpa using L.symm.contDiff.contDiffOn

/-- The identity on an open set is a C¹ chart for `lem:morse-coords`. -/
theorem isMorseC1Chart_ofSet {W : Set E2} (hW : IsOpen W) :
    IsMorseC1Chart (OpenPartialHomeomorph.ofSet W hW) := by
  refine ⟨?_, ?_⟩
  · simpa using contDiffOn_id
  · simpa using contDiffOn_id

/-- In dimension two, a form taking both signs on the diagonal and homogeneous of degree
two there has index one. General-form version of `formIndex_eq_one_of_mixed`, used for
`lem:morse-coords`. -/
theorem formIndex_eq_one_of_mixed_form {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (B : V → V → ℝ)
    (h2 : Module.finrank ℝ V = 2)
    (hsc : ∀ (a : ℝ) (x : V), B (a • x) (a • x) = a ^ 2 * B x x)
    (hn : ∃ x, B x x < 0) (hp : ∃ x, 0 < B x x) : formIndex B = 1 := by
  obtain ⟨v, hv⟩ := hn
  obtain ⟨w, hw⟩ := hp
  have hv0 : v ≠ 0 := by
    rintro rfl
    have h := hsc 0 0
    simp at h
    linarith
  have hw0 : w ≠ 0 := by
    rintro rfl
    have h := hsc 0 0
    simp at h
    linarith
  have hne : Set.Nonempty {d | ∃ W : Submodule ℝ V, Module.finrank ℝ W = d ∧
      ∀ x ∈ W, x ≠ 0 → B x x < 0} := ⟨0, ⊥, by simp, by simp⟩
  have hbdd : BddAbove {d | ∃ W : Submodule ℝ V, Module.finrank ℝ W = d ∧
      ∀ x ∈ W, x ≠ 0 → B x x < 0} := by
    refine ⟨Module.finrank ℝ V, ?_⟩
    rintro d ⟨W, rfl, _⟩
    exact Submodule.finrank_le W
  apply le_antisymm
  · apply csSup_le hne
    rintro d ⟨W, rfl, hW⟩
    have hle : Module.finrank ℝ W ≤ 2 := h2 ▸ Submodule.finrank_le W
    have hne2 : Module.finrank ℝ W ≠ 2 := by
      intro he
      have htop := Submodule.eq_top_of_finrank_eq (he.trans h2.symm)
      exact hw.not_gt (hW w (htop ▸ Submodule.mem_top) hw0)
    omega
  · apply le_csSup hbdd
    refine ⟨Submodule.span ℝ {v}, finrank_span_singleton hv0, ?_⟩
    intro x hx hx0
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ha : a ≠ 0 := by intro h; simp [h] at hx0
    rw [hsc]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ha) hv

/-- The coefficient expansion of a symmetric bilinear form of the plane at two vectors,
used in `lem:morse-coords`. -/
theorem morse_bilinear_expansion₂ (Q : E2 →L[ℝ] E2 →L[ℝ] ℝ)
    (hQ : ∀ v w : E2, Q v w = Q w v) (x y : E2) :
    Q x y = Q (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) * x 0 * y 0 +
      Q (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) * (x 0 * y 1 + x 1 * y 0) +
      Q (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) * x 1 * y 1 := by
  have h1 := morse_bilinear_expansion Q hQ (x + y)
  have h2 := morse_bilinear_expansion Q hQ x
  have h3 := morse_bilinear_expansion Q hQ y
  simp only [map_add, add_apply, PiLp.add_apply] at h1
  rw [hQ y x] at h1
  linear_combination (h1 - h2 - h3) / 2

/-- A completed square with two positive pivots is positive off the origin
(`lem:morse-coords`). -/
theorem morse_quad_pos {a s : ℝ} (b : ℝ) (ha : 0 < a) (hs : 0 < s) {w : E2}
    (hw : w ≠ 0) : 0 < a * (w 0 + b * w 1) ^ 2 + s * w 1 ^ 2 := by
  by_cases h1 : w 1 = 0
  · have h0 : w 0 ≠ 0 := by
      intro h0
      apply hw
      ext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    rw [h1]
    simpa using mul_pos ha (sq_pos_of_ne_zero h0)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (sq_nonneg _))
      (mul_pos hs (sq_pos_of_ne_zero h1))

/-- A nonvanishing continuous function keeps its sign near the origin
(`lem:morse-coords`). -/
theorem eventually_sign_eq_of_ne {f : E2 → ℝ} (hf : ContinuousAt f 0) (h : f 0 ≠ 0) :
    ∀ᶠ u in 𝓝 (0 : E2), Real.sign (f u) = Real.sign (f 0) := by
  rcases h.lt_or_gt with h | h
  · filter_upwards [hf.eventually (gt_mem_nhds h)] with u hu
    rw [Real.sign_of_neg hu, Real.sign_of_neg h]
  · filter_upwards [hf.eventually (lt_mem_nhds h)] with u hu
    rw [Real.sign_of_pos hu, Real.sign_of_pos h]

/-- Assembly of the chart in `lem:morse-coords` from a linear change of coordinates `L`,
a C¹ chart `eφ`, an open set `W` and a final linear map `P`
(C¹ pending the user's wording decision). -/
theorem morse_chart_assembly {g : E2 → ℝ} {k : ℕ} (L P : E2 ≃L[ℝ] E2)
    (eφ : OpenPartialHomeomorph E2 E2) (h0φ : (0 : E2) ∈ eφ.source) (heφ0 : eφ 0 = 0)
    (hφ : IsMorseC1Chart eφ) {W : Set E2} (hWo : IsOpen W) (hW0 : (0 : E2) ∈ W)
    (hform : ∀ u ∈ W, u ∈ eφ.source → g (L u) = morseModel k (P (eφ u))) :
    ∃ e : OpenPartialHomeomorph E2 E2, (0 : E2) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ x ∈ e.source, g x = morseModel k (e x) := by
  let e := ((L.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (OpenPartialHomeomorph.ofSet W hWo)).trans eφ).trans P.toHomeomorph.toOpenPartialHomeomorph
  have hC : IsMorseC1Chart e :=
    (((isMorseC1Chart_linearEquiv _).trans (isMorseC1Chart_ofSet hWo)).trans hφ).trans
      (isMorseC1Chart_linearEquiv _)
  have happ : ∀ x, e x = P (eφ (L.symm x)) := fun x => rfl
  have hsrc : ∀ x ∈ e.source, L.symm x ∈ W ∧ L.symm x ∈ eφ.source := by
    intro x hx
    simp only [e, mfld_simps] at hx
    exact ⟨hx.1, hx.2⟩
  refine ⟨e, ?_, ?_, hC.1, hC.2, ?_⟩
  · simp only [e, mfld_simps]
    simpa using ⟨hW0, h0φ⟩
  · rw [happ]
    simp [heφ0]
  · intro x hx
    obtain ⟨h1, h2⟩ := hsrc x hx
    have := hform _ h1 h2
    rw [happ]
    simpa using this

/-- lem:morse-coords, the planar Morse lemma at C¹ regularity (C¹ pending the user's
wording decision): at a nondegenerate critical point of a C³ function with critical value
zero there is a C¹ chart with C¹ inverse, sending the origin to itself, in which the
function is the model quadratic form of the index of its Hessian. -/
theorem exists_morse_coords {g : E2 → ℝ} (hg : ContDiffAt ℝ 3 g 0) (h0 : g 0 = 0)
    (hd : fderiv ℝ g 0 = 0)
    (hnd : IsNondegenerateForm (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w)) :
    ∃ e : OpenPartialHomeomorph E2 E2, (0 : E2) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ x ∈ e.source,
        g x = morseModel (formIndex (fun v w : E2 => fderiv ℝ (fderiv ℝ g) 0 v w)) (e x) := by
  obtain ⟨R, hR, -, hB0, hBx⟩ := exists_morseB hg h0 hd
  set H := fderiv ℝ (fderiv ℝ g) 0 with hHdef
  have hHs : ∀ v w : E2, H v w = H w v := by
    intro v w
    rw [← hB0]
    exact (hBx 0 (mem_ball_self hR)).2 v w
  obtain ⟨v, hv⟩ : ∃ v : E2, H v v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ X Y : E2, H X Y = 0 := by
      intro X Y
      have h := hcon (X + Y)
      simp only [map_add, add_apply, hcon X, hcon Y, hHs Y X] at h
      linarith
    have h1 := hnd (EuclideanSpace.single 0 1) (hz _)
    have h2 := congrArg (fun y : E2 => y 0) h1
    simp at h2
  have hdet : v 0 * v 0 - -v 1 * v 1 ≠ 0 := by
    intro h
    have h0' : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have h1' : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    apply hv
    have : v = 0 := by
      ext i
      fin_cases i
      · simpa using h0'
      · simpa using h1'
    simp [this]
  set L := morsePlaneEquiv (v 0) (-v 1) (v 1) (v 0) hdet with hLdef
  have hLe0 : L (EuclideanSpace.single 0 1) = v := by
    ext i
    fin_cases i <;> simp [L, morsePlaneEquiv_apply]
  let e0 : E2 := EuclideanSpace.single 0 1
  let e1 : E2 := EuclideanSpace.single 1 1
  let Q : E2 → E2 →L[ℝ] E2 →L[ℝ] ℝ := fun u =>
    (1 / 2 : ℝ) • (morseB g (L u)).bilinearComp (L : E2 →L[ℝ] E2) (L : E2 →L[ℝ] E2)
  have hQ : ∀ u w w' : E2, Q u w w' = 1 / 2 * morseB g (L u) (L w) (L w') := by
    intro u w w'
    simp [Q]
  let A : E2 → ℝ := fun u => Q u e0 e0
  let Bc : E2 → ℝ := fun u => Q u e0 e1
  let D : E2 → ℝ := fun u => Q u e1 e1
  let s : E2 → ℝ := fun u => D u - Bc u ^ 2 / A u
  have hBL : ContDiffAt ℝ 1 (fun u => morseB g (L u)) 0 := by
    have h : ContDiffAt ℝ 1 (morseB g) (L 0) := by
      rw [map_zero]
      exact contDiffAt_morseB hg
    exact h.comp 0 L.contDiff.contDiffAt
  have hcoef : ∀ w w' : E2, ContDiffAt ℝ 1 (fun u => Q u w w') 0 := by
    intro w w'
    have : (fun u => Q u w w') = fun u => 1 / 2 * morseB g (L u) (L w) (L w') :=
      funext fun u => hQ u w w'
    rw [this]
    exact contDiffAt_const.mul ((hBL.clm_apply contDiffAt_const).clm_apply contDiffAt_const)
  have hQ0 : ∀ x y : E2, Q 0 x y = 1 / 2 * H (L x) (L y) := by
    intro x y
    rw [hQ, map_zero, hB0]
  have hQ0s : ∀ x y : E2, Q 0 x y = Q 0 y x := by
    intro x y
    rw [hQ0, hQ0, hHs]
  have hexp : ∀ x y : E2, Q 0 x y =
      A 0 * x 0 * y 0 + Bc 0 * (x 0 * y 1 + x 1 * y 0) + D 0 * x 1 * y 1 :=
    morse_bilinear_expansion₂ (Q 0) hQ0s
  have hA0 : A 0 ≠ 0 := by
    have : A 0 = 1 / 2 * H v v := by
      change Q 0 e0 e0 = _
      rw [hQ0, hLe0]
    rw [this]
    exact mul_ne_zero (by norm_num) hv
  have hnd' : IsNondegenerateForm (fun x y : E2 => H (L x) (L y)) :=
    (isNondegenerateForm_comp_linearEquiv L.toLinearEquiv (fun v w : E2 => H v w)).mpr hnd
  have hs0 : s 0 ≠ 0 := by
    intro hs
    let w : E2 := WithLp.toLp 2 ![-(Bc 0) / A 0, 1]
    have hw0 : w 0 = -(Bc 0) / A 0 := rfl
    have hw1 : w 1 = 1 := rfl
    have key : A 0 * (-(Bc 0) / A 0) = -(Bc 0) := by field_simp
    have hw : w = 0 := hnd' w (fun Y => by
      have h : Q 0 w Y = 0 := by
        rw [hexp, hw0, hw1]
        linear_combination Y 1 * hs + Y 0 * key
      rw [hQ0] at h
      linarith)
    have h1 : w 1 = 0 := by rw [hw]; simp
    rw [hw1] at h1
    exact one_ne_zero h1
  obtain ⟨eφ, h0φ, heφ0, hφC, hφiC, hφeq⟩ :=
    exists_morseSquareChart (hcoef e0 e0) (hcoef e0 e1) (hcoef e1 e1) hA0 hs0
  have hAc : ContinuousAt A 0 := (hcoef e0 e0).continuousAt
  have hsc : ContinuousAt s 0 :=
    (hcoef e1 e1).continuousAt.sub (((hcoef e0 e1).continuousAt.pow 2).div hAc hA0)
  have hev1 : ∀ᶠ u in 𝓝 (0 : E2), L u ∈ ball (0 : E2) R :=
    L.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact ball_mem_nhds 0 hR)
  have hev : ∀ᶠ u in 𝓝 (0 : E2), L u ∈ ball (0 : E2) R ∧ A u ≠ 0 ∧
      Real.sign (A u) = Real.sign (A 0) ∧ Real.sign (s u) = Real.sign (s 0) :=
    hev1.and ((hAc.eventually_ne hA0).and
      ((eventually_sign_eq_of_ne hAc hA0).and (eventually_sign_eq_of_ne hsc hs0)))
  obtain ⟨W, hWP, hWo, hW0⟩ := _root_.eventually_nhds_iff.mp hev
  have hform : ∀ u ∈ W, g (L u) =
      Real.sign (A 0) * (eφ u 0) ^ 2 + Real.sign (s 0) * (eφ u 1) ^ 2 := by
    intro u hu
    obtain ⟨hLu, hAu, hsA, hss⟩ := hWP u hu
    obtain ⟨hgx, hsym⟩ := hBx (L u) hLu
    have hQs : ∀ x y : E2, Q u x y = Q u y x := by
      intro x y
      rw [hQ, hQ, hsym]
    have h1 := morse_bilinear_expansion (Q u) hQs u
    have h2 := morseSquareChart_identity A Bc D u hAu
    have h3 : g (L u) = Q u u u := by rw [hgx, hQ]
    rw [h3, h1, hφeq, ← hsA, ← hss]
    exact h2
  have hquad : ∀ w : E2, H (L w) (L w) =
      2 * (A 0 * (w 0 + Bc 0 / A 0 * w 1) ^ 2 + s 0 * w 1 ^ 2) := by
    intro w
    have h := hexp w w
    rw [hQ0] at h
    rw [← morse_complete_square _ _ _ _ _ hA0]
    linear_combination 2 * h
  have hk : formIndex (fun v w : E2 => H v w) = formIndex (fun x y : E2 => H (L x) (L y)) :=
    (formIndex_comp_linearEquiv L.toLinearEquiv (fun v w : E2 => H v w)).symm
  have hsc2 : ∀ (c : ℝ) (x : E2), H (L (c • x)) (L (c • x)) = c ^ 2 * H (L x) (L x) := by
    intro c x
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  let wn : E2 := WithLp.toLp 2 ![-(Bc 0) / A 0, 1]
  let wp : E2 := WithLp.toLp 2 ![1, 0]
  have hwn : H (L wn) (L wn) = 2 * s 0 := by
    rw [hquad]
    have h0' : wn 0 = -(Bc 0) / A 0 := rfl
    have h1' : wn 1 = 1 := rfl
    rw [h0', h1']
    ring
  have hwp : H (L wp) (L wp) = 2 * A 0 := by
    rw [hquad]
    have h0' : wp 0 = 1 := rfl
    have h1' : wp 1 = 0 := rfl
    rw [h0', h1']
    ring
  have hfin : Module.finrank ℝ E2 = 2 := finrank_euclideanSpace_fin
  let swap : E2 ≃L[ℝ] E2 := morsePlaneEquiv 0 1 1 0 (by norm_num)
  have hswap0 : ∀ y : E2, swap y 0 = y 1 := fun y => by
    simp [swap, morsePlaneEquiv_apply]
  have hswap1 : ∀ y : E2, swap y 1 = y 0 := fun y => by
    simp [swap, morsePlaneEquiv_apply]
  rcases hA0.lt_or_gt with ha | ha <;> rcases hs0.lt_or_gt with hs | hs
  · have hi : formIndex (fun v w : E2 => H v w) = 2 := by
      rw [hk, formIndex_eq_finrank_of_neg, hfin]
      intro x hx
      rw [hquad]
      have := morse_quad_pos (Bc 0 / A 0) (neg_pos.mpr ha) (neg_pos.mpr hs) hx
      linarith
    refine morse_chart_assembly L (ContinuousLinearEquiv.refl ℝ E2) eφ h0φ heφ0
      ⟨hφC, hφiC⟩ hWo hW0 ?_
    intro u hu _
    rw [hi, hform u hu, Real.sign_of_neg ha, Real.sign_of_neg hs]
    simp [morseModel]
    ring
  · have hi : formIndex (fun v w : E2 => H v w) = 1 := by
      rw [hk]
      exact formIndex_eq_one_of_mixed_form _ hfin hsc2 ⟨wp, by rw [hwp]; linarith⟩
        ⟨wn, by rw [hwn]; linarith⟩
    refine morse_chart_assembly L swap eφ h0φ heφ0 ⟨hφC, hφiC⟩ hWo hW0 ?_
    intro u hu _
    rw [hi, hform u hu, Real.sign_of_neg ha, Real.sign_of_pos hs]
    simp only [morseModel, hswap0, hswap1]
    norm_num
    ring
  · have hi : formIndex (fun v w : E2 => H v w) = 1 := by
      rw [hk]
      exact formIndex_eq_one_of_mixed_form _ hfin hsc2 ⟨wn, by rw [hwn]; linarith⟩
        ⟨wp, by rw [hwp]; linarith⟩
    refine morse_chart_assembly L (ContinuousLinearEquiv.refl ℝ E2) eφ h0φ heφ0
      ⟨hφC, hφiC⟩ hWo hW0 ?_
    intro u hu _
    rw [hi, hform u hu, Real.sign_of_pos ha, Real.sign_of_neg hs]
    simp [morseModel]
    ring
  · have hi : formIndex (fun v w : E2 => H v w) = 0 := by
      rw [hk]
      apply formIndex_eq_zero_of_pos
      intro x hx
      rw [hquad]
      have := morse_quad_pos (Bc 0 / A 0) ha hs hx
      linarith
    refine morse_chart_assembly L (ContinuousLinearEquiv.refl ℝ E2) eφ h0φ heφ0
      ⟨hφC, hφiC⟩ hWo hW0 ?_
    intro u hu _
    rw [hi, hform u hu, Real.sign_of_pos ha, Real.sign_of_pos hs]
    simp [morseModel]

/-- The named hypothesis `MorseCoordsStatement` of `lem:morse-coords` holds
(C¹ pending the user's wording decision). -/
theorem morseCoordsStatement : MorseCoordsStatement :=
  fun _ hg h0 hd hnd => exists_morse_coords hg h0 hd hnd

end LiquidDrop
