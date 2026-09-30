module

public import NoCompromise.Sard.Flat

@[expose] public section

/-!
# Cubic flatness and twice-flat values on C¹ surfaces

The mean value theorem raises a uniform derivative remainder estimate by one
order. This gives cubic remainders at points where the first three derivatives
vanish. On a C¹ surface, the quadratic remainder already suffices for a null
scalar image because the parameter space is two-dimensional.
-/

noncomputable section
open MeasureTheory Filter Set Metric InnerProductSpace Function
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A uniform order-`m` estimate on the derivative gives an order-`m+1`
estimate on the function near a compact set of critical points. -/
lemma compact_uniform_flat_succ {n m : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U S : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContDiffOn ℝ 1 f U) (hfirst : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hflat : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ x ∈ S, ∀ y, dist y x < δ →
      dist (fderiv ℝ f y) (fderiv ℝ f x) ≤ ε * dist y x ^ m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ > 0, ∀ x ∈ S, ∀ y, dist y x < ρ →
      dist (f y) (f x) ≤ ε * dist y x ^ (m + 1) := by
  obtain ⟨δ, hδ, hd⟩ := hflat ε hε
  obtain ⟨r, hr, hrU⟩ := hS.exists_thickening_subset_open hU hSU
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro x hx y hy
  have hyδ := hy.trans_le (min_le_left _ _)
  have hyr := hy.trans_le (min_le_right _ _)
  have hsegdist (z) (hz : z ∈ segment ℝ x y) : dist z x ≤ dist y x := by
    simpa only [mem_closedBall, dist_comm x y] using segment_subset_closedBall_left x y hz
  have hsegU : segment ℝ x y ⊆ U := by
    intro z hz
    exact hrU (mem_thickening_iff.mpr ⟨x, hx, (hsegdist z hz).trans_lt hyr⟩)
  have hbound (z) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ f z‖ ≤ ε * dist y x ^ m := by
    have h := hd x hx z ((hsegdist z hz).trans_lt hyδ)
    rw [hfirst x hx, dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ dist_nonneg (hsegdist z hz) m) hε.le)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hf.differentiableOn (by norm_num) z (hsegU hz)).differentiableAt
      (hU.mem_nhds (hsegU hz))) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [dist_eq_norm, pow_succ, mul_assoc] using h

/-- At a compact set of points where the first three derivatives vanish, a C³
map has uniformly arbitrarily small cubic remainders. -/
lemma compact_uniform_cubic_flat {n : ℕ}
    {U S : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ 3 f U) (hfirst : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hsecond : ∀ x ∈ S, fderiv ℝ (fderiv ℝ f) x = 0)
    (hthird : ∀ x ∈ S, fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ > 0, ∀ x ∈ S, ∀ y, dist y x < ρ →
      dist (f y) (f x) ≤ ε * dist y x ^ 3 := by
  have hdf : ContDiffOn ℝ 2 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf |>.2.2
  have hddf : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ f)) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hdf |>.2.2
  apply compact_uniform_flat_succ hU hS hSU (hf.of_le (by norm_num)) hfirst (m := 2) ?_ ε hε
  intro η hη
  apply compact_uniform_flat_succ hU hS hSU (hdf.of_le (by norm_num)) hsecond (m := 1) ?_ η hη
  intro κ hκ
  obtain ⟨δ, hδ, hb⟩ := compact_uniform_small_slope_of_fderiv_eq_zero
    hU hS hSU hddf hthird ⟨κ, hκ.le⟩ hκ
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  rw [pow_one]
  exact_mod_cast hb x hx y hy

/-- A compact thrice-flat stratum of a scalar C³ map in three dimensions has null image. -/
lemma measure_image_compact_thrice_flat
    {U S : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiffOn ℝ 3 f U) (hfirst : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hsecond : ∀ x ∈ S, fderiv ℝ (fderiv ℝ f) x = 0)
    (hthird : ∀ x ∈ S, fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x = 0) :
    volume (f '' S) = 0 :=
  measure_image_eq_zero_of_bounded_uniform_flat hS.isBounded f
    (compact_uniform_cubic_flat hU hS hSU hf hfirst hsecond hthird)

/-- A C¹ parametrization has a uniform Lipschitz bound between points of a compact
set and sufficiently close parameter points. -/
lemma compact_uniform_lipschitz_near {n m : ℕ}
    {W S : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W) (hS : IsCompact S)
    (hSW : S ⊆ W) {γ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hγ : ContDiffOn ℝ 1 γ W) :
    ∃ M ≥ (1 : ℝ), ∃ δ > 0, ∀ x ∈ S, ∀ y, dist y x < δ →
      dist (γ y) (γ x) ≤ M * dist y x := by
  obtain ⟨r, hr, hrW⟩ := hS.exists_cthickening_subset_open hW hSW
  obtain ⟨M, hM⟩ := hS.cthickening.exists_bound_of_continuousOn
    ((hγ.continuousOn_fderiv_of_isOpen hW le_rfl).mono hrW)
  refine ⟨max 1 M, le_max_left _ _, r, hr, ?_⟩
  intro x hx y hy
  have hseg (z) (hz : z ∈ segment ℝ x y) : z ∈ cthickening r S := by
    apply thickening_subset_cthickening
    apply mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    exact (show dist z x ≤ dist y x by
      simpa only [mem_closedBall, dist_comm x y] using
        segment_subset_closedBall_left x y hz).trans_lt hy
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hγ.differentiableOn (by norm_num) z (hrW (hseg z hz))).differentiableAt
      (hW.mem_nhds (hrW (hseg z hz))))
    (fun z hz => (hM z (hseg z hz)).trans (le_max_right 1 M))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [dist_eq_norm] using h

/-- A compact twice-flat critical set on a C¹ parametrized surface has null image.
Only quadratic smallness is needed because the parameter domain has dimension two. -/
lemma measure_image_compact_twice_flat_parametrization {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {W S : Set (EuclideanSpace ℝ (Fin 2))} (hW : IsOpen W) (hS : IsCompact S)
    (hSW : S ⊆ W) {γ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin n)}
    (hγ : ContDiffOn ℝ 1 γ W) (hγU : MapsTo γ W U)
    (hfirst : ∀ x ∈ S, fderiv ℝ f (γ x) = 0)
    (hsecond : ∀ x ∈ S, fderiv ℝ (fderiv ℝ f) (γ x) = 0) :
    volume ((f ∘ γ) '' S) = 0 := by
  have hT := hS.image_of_continuousOn (hγ.continuousOn.mono hSW)
  have hTU : γ '' S ⊆ U := by rintro _ ⟨x, hx, rfl⟩; exact hγU (hSW hx)
  obtain ⟨M, hM, δ, hδ, hLip⟩ := compact_uniform_lipschitz_near hW hS hSW hγ
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  apply measure_image_eq_zero_of_bounded_uniform_flat hS.isBounded (f ∘ γ)
  intro ε hε
  obtain ⟨ρ, hρ, hflat⟩ := compact_uniform_quadratic_flat hU hT hTU hf
    (by rintro _ ⟨x, hx, rfl⟩; exact hfirst x hx)
    (by rintro _ ⟨x, hx, rfl⟩; exact hsecond x hx)
    (ε / M ^ 2) (div_pos hε (sq_pos_of_pos hMpos))
  refine ⟨min δ (ρ / M), lt_min hδ (div_pos hρ hMpos), ?_⟩
  intro x hx y hy
  have hl := hLip x hx y (hy.trans_le (min_le_left _ _))
  have hdist : dist (γ y) (γ x) < ρ := hl.trans_lt (by
    simpa only [mul_comm] using
      (lt_div_iff₀ hMpos).mp (hy.trans_le (min_le_right _ _)))
  calc
    dist ((f ∘ γ) y) ((f ∘ γ) x) ≤ (ε / M ^ 2) * dist (γ y) (γ x) ^ 2 :=
      hflat (γ x) ⟨x, hx, rfl⟩ (γ y) hdist
    _ ≤ (ε / M ^ 2) * (M * dist y x) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg hl 2)
        (div_nonneg hε.le (sq_nonneg M))
    _ = ε * dist y x ^ 2 := by field_simp

/-- The twice-flat part of a scalar C² function has null image on every C¹ surface. -/
lemma measure_image_twice_flat_inter_surface {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {W : Set (EuclideanSpace ℝ (Fin 2))} (hW : IsOpen W)
    {γ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin n)}
    (hγ : ContDiffOn ℝ 1 γ W) (hγU : MapsTo γ W U) :
    volume (f '' ({x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0}
      ∩ γ '' W)) = 0 := by
  let : LocallyCompactSpace W := hW.locallyCompactSpace
  let K := CompactExhaustion.choice W
  let A : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun j => Subtype.val '' K j
  have hAc (j : ℕ) : IsCompact (A j) := (K.isCompact j).image continuous_subtype_val
  have hAW (j : ℕ) : A j ⊆ W := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    (contDiffOn_succ_iff_fderiv_of_isOpen hU).mp hf |>.2.2
  have hc : ContinuousOn
      (fun x => (fderiv ℝ f (γ x), fderiv ℝ (fderiv ℝ f) (γ x))) W :=
    ((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).prodMk
      (hdf.continuousOn_fderiv_of_isOpen hU le_rfl)).comp hγ.continuousOn hγU
  let S : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun j => A j ∩
    (fun x => (fderiv ℝ f (γ x), fderiv ℝ (fderiv ℝ f) (γ x))) ⁻¹' {(0, 0)}
  have hSc (j : ℕ) : IsCompact (S j) := by
    apply (hAc j).of_isClosed_subset _ inter_subset_left
    exact (hc.mono (hAW j)).preimage_isClosed_of_isClosed (hAc j).isClosed isClosed_singleton
  have hnull (j : ℕ) : volume ((f ∘ γ) '' S j) = 0 :=
    measure_image_compact_twice_flat_parametrization hU hf hW (hSc j)
      (inter_subset_left.trans (hAW j)) hγ hγU
      (fun _ hx => congrArg Prod.fst hx.2) (fun _ hx => congrArg Prod.snd hx.2)
  apply measure_mono_null (t := ⋃ j, (f ∘ γ) '' S j) _ (measure_iUnion_null hnull)
  rintro _ ⟨x, ⟨hx, y, hy, rfl⟩, rfl⟩
  obtain ⟨j, hj⟩ := K.exists_mem ⟨y, hy⟩
  exact mem_iUnion.mpr ⟨j, y, ⟨⟨⟨y, hy⟩, hj, rfl⟩,
    Prod.ext hx.2.1 hx.2.2⟩, rfl⟩

end LiquidDrop
