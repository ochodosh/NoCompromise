import NoCompromise.Sobolev.LipschitzDomains

/-!
# Lipschitz graph charts at polyhedral corners

Finite maxima of affine functions are Lipschitz. Active face inequalities give
one-sided graph charts; the remaining strict inequalities survive shrinking.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A finite nonempty maximum preserves a common Lipschitz constant. -/
lemma lipschitzWith_finset_max {α ι : Type*} [PseudoMetricSpace α]
    (s : Finset ι) (hs : s.Nonempty) {f : ι → α → ℝ} {L : ℝ≥0}
    (hf : ∀ j ∈ s, LipschitzWith L (f j)) :
    LipschitzWith L (fun x => s.sup' hs (fun j => f j x)) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  rw [Finset.sup'_le_iff]
  intro j hj
  exact ((hf j hj).le_add_mul x y).trans
    (add_le_add (Finset.le_sup' (f := fun j => f j y) hj) le_rfl)

/-- Finite affine maxima are globally Lipschitz, with a bound from the linear parts. -/
lemma lipschitzWith_finset_max_affine {n : ℕ} {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty)
    (F : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (b : ι → ℝ) :
    LipschitzWith (s.sup fun j => ‖F j‖₊)
      (fun x => s.sup' hs (fun j => F j x + b j)) := by
  apply lipschitzWith_finset_max
  intro j hj
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_add_right]
  exact ((F j).lipschitzWith.dist_le_mul x y).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.le_sup (f := fun j => ‖F j‖₊) hj)
      dist_nonneg)

/-- A finite collection of strict linear inequalities with negative normal slopes
is exactly the upper side of the maximum of their graph heights. -/
lemma finite_linear_faces_graph_iff {n : ℕ} {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (i : Fin n)
    (F : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hF : ∀ j ∈ s, F j (EuclideanSpace.single i 1) < 0)
    (t : EuclideanSpace ℝ (Fin n)) (q : ℝ) :
    (∀ j ∈ s, F j (t +
      (q + s.sup' hs (fun k => -F k t / F k (EuclideanSpace.single i 1))) •
        EuclideanSpace.single i 1) < 0) ↔ 0 < q := by
  have heq (j : ι) (hj : j ∈ s) :
      F j (t + (q + s.sup' hs (fun k => -F k t / F k (EuclideanSpace.single i 1))) •
        EuclideanSpace.single i 1) < 0 ↔
      -F j t / F j (EuclideanSpace.single i 1) <
        q + s.sup' hs (fun k => -F k t / F k (EuclideanSpace.single i 1)) := by
    rw [div_lt_iff_of_neg (hF j hj)]
    simp only [map_add, map_smul, smul_eq_mul]
    constructor <;> intro h <;> linarith
  constructor
  · intro h
    have h' : s.sup' hs (fun j => -F j t / F j (EuclideanSpace.single i 1)) <
        q + s.sup' hs (fun j => -F j t / F j (EuclideanSpace.single i 1)) := by
      rw [Finset.sup'_lt_iff]
      intro j hj
      exact (heq j hj).mp (h j hj)
    linarith
  · intro h j hj
    apply (heq j hj).mpr
    exact (Finset.le_sup' (f := fun j => -F j t / F j (EuclideanSpace.single i 1)) hj).trans_lt
      (by linarith)

/-- Every neighborhood of the origin contains a positive coordinate cube. -/
lemma exists_coordinateCube_subset_nhds_zero {n : ℕ}
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : O ∈ 𝓝 0) :
    ∃ R : ℝ, 0 < R ∧ coordinateCube n R ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hO
  refine ⟨ε / (2 * (n + 1 : ℝ)), by positivity, ?_⟩
  intro x hx
  apply hball
  have hn := norm_le_succ_card_mul_of_mem_coordinateCube (by positivity) hx
  have heq : (n + 1 : ℝ) * (ε / (2 * (n + 1 : ℝ))) = ε / 2 := by field_simp
  rw [heq] at hn
  simpa only [mem_ball, dist_zero_right] using (show ‖x‖ < ε by linarith)

/-- Finite active supporting faces with negative normal slopes define a genuine graph
chart. Inactive faces may be arbitrary linear inequalities that are strict at the origin. -/
theorem exists_lipschitzGraphChart_finite_halfspaces {n : ℕ} {ι : Type*}
    (s A : Finset ι) (hA : A.Nonempty) (hAs : A ⊆ s) (i : Fin n)
    (F : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (b : ι → ℝ)
    (hzero : ∀ j ∈ A, b j = 0)
    (hstrict : ∀ j ∈ s, j ∉ A → 0 < b j)
    (hslope : ∀ j ∈ A, F j (EuclideanSpace.single i 1) < 0) :
    ∃ c : LipschitzGraphChart n,
      c.IsChartFor {x | ∀ j ∈ s, F j x < b j} ∧ 0 ∈ c.region := by
  classical
  let G (j : ι) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (-(F j (EuclideanSpace.single i 1))⁻¹) • F j
  let h (x : EuclideanSpace ℝ (Fin n)) : ℝ := A.sup' hA (fun j => G j x)
  have hh : LipschitzWith (A.sup fun j => ‖G j‖₊) h := by
    simpa only [add_zero] using lipschitzWith_finset_max_affine A hA G (fun _ => 0)
  have hhzero : h 0 = 0 := by simp [h]
  have hformula (t : EuclideanSpace ℝ (Fin n)) :
      h t = A.sup' hA (fun j => -F j t / F j (EuclideanSpace.single i 1)) := by
    apply Finset.sup'_congr hA rfl
    intro j hj
    simp [G, div_eq_mul_inv, mul_comm]
  have hgraph (y : EuclideanSpace ℝ (Fin n)) :
      graphShear i h y = coordinateErase i y + (y i + h (coordinateErase i y)) •
        EuclideanSpace.single i 1 := by
    ext j
    by_cases hj : j = i <;> simp [graphShear, coordinateErase_apply, hj]
  have herasezero : coordinateErase i (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
    ext j
    simp [coordinateErase_apply]
  have hgraphzero : graphShear i h 0 = 0 := by
    simp [graphShear, herasezero, hhzero]
  have hactive (y : EuclideanSpace ℝ (Fin n)) :
      (∀ j ∈ A, F j (graphShear i h y) < b j) ↔ 0 < y i := by
    have hb : (∀ j ∈ A, F j (graphShear i h y) < b j) ↔
        ∀ j ∈ A, F j (graphShear i h y) < 0 := by
      constructor <;> intro h' j hj <;> simpa only [hzero j hj] using h' j hj
    rw [hb, hgraph, hformula]
    exact finite_linear_faces_graph_iff A hA i F hslope (coordinateErase i y) (y i)
  have hO : {y | ∀ j ∈ s, j ∉ A → F j (graphShear i h y) < b j} ∈ 𝓝 0 := by
    change ∀ᶠ y in 𝓝 0, ∀ j ∈ s, j ∉ A → F j (graphShear i h y) < b j
    rw [Finset.eventually_all]
    intro j hj
    by_cases hja : j ∈ A
    · exact Eventually.of_forall fun _ h' => (h' hja).elim
    · have hc : Continuous (fun y => F j (graphShear i h y)) :=
        (F j).continuous.comp (lipschitzWith_graphShear i hh).continuous
      have hevent := hc.continuousAt.eventually_lt_const
        (show F j (graphShear i h 0) < b j by simpa [hgraphzero] using hstrict j hj hja)
      filter_upwards [hevent] with y hy using fun _ => hy
  obtain ⟨R, hR, hRO⟩ := exists_coordinateCube_subset_nhds_zero hO
  let c : LipschitzGraphChart n :=
    ⟨i, R, hR, h, A.sup (fun j => ‖G j‖₊), hh, AffineIsometryEquiv.refl ℝ _⟩
  have hmem (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ coordinateCube n R) :
      c.homeomorph y ∈ {x | ∀ j ∈ s, F j x < b j} ↔ 0 < y i := by
    change (∀ j ∈ s, F j (graphShear i h y) < b j) ↔ 0 < y i
    constructor
    · intro hy'
      exact (hactive y).mp (fun j hj => hy' j (hAs hj))
    · intro hy' j hj
      by_cases hja : j ∈ A
      · exact (hactive y).mpr hy' j hja
      · exact hRO hy j hj hja
  refine ⟨c, ?_, ?_⟩
  · change c.homeomorph '' coordinateHalfCube i R =
      {x | ∀ j ∈ s, F j x < b j} ∩ (c.homeomorph '' coordinateCube n R)
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hmem y hy.1).mpr hy.2, ⟨y, hy.1, rfl⟩⟩
    · rintro ⟨hz, y, hy, rfl⟩
      exact ⟨y, ⟨hy, (hmem y hy).mp hz⟩, rfl⟩
  · refine ⟨0, ?_, ?_⟩
    · intro j
      simpa only [PiLp.zero_apply, abs_zero] using hR
    · exact hgraphzero

/-- Rigid placement carries genuine graph charts to genuine graph charts. -/
theorem exists_lipschitzGraphChart_image {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (c : LipschitzGraphChart n) (hc : c.IsChartFor D) (hx : x ∈ c.region)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ d : LipschitzGraphChart n, d.IsChartFor (a '' D) ∧ a x ∈ d.region := by
  let d : LipschitzGraphChart n := {c with placement := c.placement.trans a}
  have hregion : d.region = a '' c.region := by
    change (a ∘ c.homeomorph) '' coordinateCube n c.radius =
      a '' (c.homeomorph '' coordinateCube n c.radius)
    exact (image_image a c.homeomorph _).symm
  have hupper : d.upperRegion = a '' c.upperRegion := by
    change (a ∘ c.homeomorph) '' coordinateHalfCube c.normal c.radius =
      a '' (c.homeomorph '' coordinateHalfCube c.normal c.radius)
    exact (image_image a c.homeomorph _).symm
  refine ⟨d, ?_, ?_⟩
  · change d.upperRegion = a '' D ∩ d.region
    rw [hupper, hc, image_inter a.injective, hregion]
  · rw [hregion]
    exact mem_image_of_mem a hx

/-- A finite intersection of open linear halfspaces that contains the origin strictly
has Lipschitz boundary. The supporting faces at a corner are allowed to meet. -/
theorem hasLipschitzBoundary_finite_halfspaces_of_pos {n : ℕ} {ι : Type*}
    (s : Finset ι) (F : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (b : ι → ℝ)
    (hb : ∀ j ∈ s, 0 < b j) : HasLipschitzBoundary {x | ∀ j ∈ s, F j x < b j} := by
  classical
  let D : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ j ∈ s, F j x < b j}
  have hD : IsOpen D := by
    simpa only [D, ofPred_forall] using
      (isOpen_biInter_finset (s := s) fun j _ => isOpen_lt (F j).continuous continuous_const)
  intro x hx
  have hle (j : ι) (hj : j ∈ s) : F j x ≤ b j := by
    have hs : D ⊆ {y | F j y ≤ b j} := fun y hy => (hy j hj).le
    exact closure_minimal hs (isClosed_le (F j).continuous continuous_const)
      (frontier_subset_closure hx)
  have hxnot : x ∉ D := by
    rw [hD.frontier_eq] at hx
    exact hx.2
  have hex : ∃ j ∈ s, F j x = b j := by
    by_contra h
    push Not at h
    apply hxnot
    intro j hj
    exact lt_of_le_of_ne (hle j hj) (h j hj)
  obtain ⟨j₀, hj₀, heq₀⟩ := hex
  have hxne : x ≠ 0 := by
    intro hzero
    have h := hb j₀ hj₀
    rw [hzero, map_zero] at heq₀
    linarith
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hi : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hxne
    ext i
    exact h i
  obtain ⟨i, _⟩ := hi
  let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Submodule.reflection (ℝ ∙ (‖x‖ • EuclideanSpace.single i 1 - (-x)))ᗮ
  have he : e (‖x‖ • EuclideanSpace.single i 1) = -x :=
    Submodule.reflection_sub (by simp [norm_smul, PiLp.norm_single])
  let a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n) :=
    e.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ x)
  have ha (y : EuclideanSpace ℝ (Fin n)) : a y = e y + x := rfl
  have ha0 : a 0 = x := by simp [ha]
  let G (j : ι) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (F j).comp e.toLinearIsometry.toContinuousLinearMap
  let c (j : ι) : ℝ := b j - F j x
  let A : Finset ι := s.filter (fun j => F j x = b j)
  have hA : A.Nonempty := ⟨j₀, by simp [A, hj₀, heq₀]⟩
  have hAs : A ⊆ s := Finset.filter_subset _ _
  have hzero (j : ι) (hj : j ∈ A) : c j = 0 := by
    have h := (Finset.mem_filter.mp hj).2
    simp only [c, h, sub_self]
  have hstrict (j : ι) (hj : j ∈ s) (hja : j ∉ A) : 0 < c j := by
    have hne : F j x ≠ b j := by
      intro h
      exact hja (by simp [A, hj, h])
    exact sub_pos.mpr (lt_of_le_of_ne (hle j hj) hne)
  have hslope (j : ι) (hj : j ∈ A) : G j (EuclideanSpace.single i 1) < 0 := by
    have hnorm : ‖x‖ * G j (EuclideanSpace.single i 1) = -F j x := by
      calc
        _ = F j (e (‖x‖ • EuclideanSpace.single i 1)) := by
          simp [G]
        _ = _ := by rw [he, map_neg]
    have hface := (Finset.mem_filter.mp hj).2
    have hpos := hb j (hAs hj)
    rw [hface] at hnorm
    nlinarith
  obtain ⟨k, hk, hkzero⟩ :=
    exists_lipschitzGraphChart_finite_halfspaces s A hA hAs i G c hzero hstrict hslope
  have himage : a '' {y | ∀ j ∈ s, G j y < c j} = D := by
    have hface (j : ι) (y : EuclideanSpace ℝ (Fin n)) :
        F j (a y) = G j y + F j x := by simp [ha, G]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩ j hj
      have h := hz j hj
      change G j z < b j - F j x at h
      rw [hface]
      linarith
    · intro hy
      refine ⟨a.symm y, ?_, a.apply_symm_apply y⟩
      intro j hj
      have h := hy j hj
      have heq := hface j (a.symm y)
      rw [a.apply_symm_apply] at heq
      change G j (a.symm y) < b j - F j x
      linarith
  obtain ⟨k', hk', hx'⟩ := exists_lipschitzGraphChart_image k hk hkzero a
  exact ⟨k', by simpa only [himage] using hk', by simpa only [ha0] using hx'⟩

/-- The two oriented coordinate functionals for each pair of opposite cube faces. -/
def cubeFaceFunctional {n : ℕ} (j : Fin n × Bool) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  if j.2 then EuclideanSpace.proj j.1 else -EuclideanSpace.proj j.1

/-- A coordinate cube is the intersection of its finitely many strict face inequalities. -/
lemma coordinateCube_eq_finite_halfspaces (n : ℕ) (R : ℝ) :
    coordinateCube n R =
      {x | ∀ j ∈ (Finset.univ : Finset (Fin n × Bool)), cubeFaceFunctional j x < R} := by
  ext x
  constructor
  · intro hx j _
    obtain ⟨j, b⟩ := j
    cases b
    · change -x j < R
      have h := (abs_lt.mp (hx j)).1
      linarith
    · exact (abs_lt.mp (hx j)).2
  · intro hx j
    have hpos := hx (j, true) (Finset.mem_univ _)
    have hneg := hx (j, false) (Finset.mem_univ _)
    change x j < R at hpos
    change -x j < R at hneg
    exact abs_lt.mpr ⟨by linarith, hpos⟩

/-- Positive coordinate cubes have Lipschitz boundary, including all edges and corners. -/
theorem hasLipschitzBoundary_coordinateCube (n : ℕ) {R : ℝ} (hR : 0 < R) :
    HasLipschitzBoundary (coordinateCube n R) := by
  rw [coordinateCube_eq_finite_halfspaces]
  exact hasLipschitzBoundary_finite_halfspaces_of_pos Finset.univ cubeFaceFunctional
    (fun _ => R) (fun _ _ => hR)

end LiquidDrop
