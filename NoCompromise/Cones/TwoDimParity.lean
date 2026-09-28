import NoCompromise.Cones.TwoDimLink

/-!
# Parity of the planar cone link

Angular coordinates and phase changes for the canonical representative of a
locally perimeter-minimizing planar cone.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace LiquidDrop

/-- The positively oriented unit-circle parametrization in Euclidean coordinates. -/
def cone2dCircle (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.cos θ, Real.sin θ]

/-- The first coordinate of the unit-circle parametrization. -/
@[simp] theorem cone2dCircle_zero (θ : ℝ) : cone2dCircle θ 0 = Real.cos θ := rfl

/-- The second coordinate of the unit-circle parametrization. -/
@[simp] theorem cone2dCircle_one (θ : ℝ) : cone2dCircle θ 1 = Real.sin θ := rfl

/-- The circle parametrization is continuous. -/
theorem cone2dCircle_continuous : Continuous cone2dCircle := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Real.continuous_cos
  · exact Real.continuous_sin

/-- Every value of the circle parametrization has norm one. -/
@[simp] theorem cone2dCircle_norm (θ : ℝ) : ‖cone2dCircle θ‖ = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq (cone2dCircle θ)
  simp only [Fin.sum_univ_two, cone2dCircle_zero, cone2dCircle_one] at h
  nlinarith [Real.sin_sq_add_cos_sq θ, norm_nonneg (cone2dCircle θ)]

/-- The circle parametrization takes values on the unit sphere. -/
theorem cone2dCircle_mem_sphere (θ : ℝ) : cone2dCircle θ ∈ Metric.sphere 0 1 := by
  simp

/-- One full positive turn preserves the circle point. -/
@[simp] theorem cone2dCircle_add_two_pi (θ : ℝ) :
    cone2dCircle (θ + 2 * Real.pi) = cone2dCircle θ := by
  ext i
  fin_cases i <;> simp

/-- Rotation by an angle in the standard Euclidean plane. The inverse rotates
by the negative angle. -/
def cone2dRotation (s : ℝ) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := WithLp.toLp 2 ![Real.cos s * x 0 - Real.sin s * x 1,
    Real.sin s * x 0 + Real.cos s * x 1]
  invFun x := WithLp.toLp 2 ![Real.cos s * x 0 + Real.sin s * x 1,
    -Real.sin s * x 0 + Real.cos s * x 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring
  left_inv x := by
    ext i
    fin_cases i <;> simp
    · linear_combination x 0 * Real.sin_sq_add_cos_sq s
    · linear_combination x 1 * Real.sin_sq_add_cos_sq s
  right_inv x := by
    ext i
    fin_cases i <;> simp
    · linear_combination x 0 * Real.sin_sq_add_cos_sq s
    · linear_combination x 1 * Real.sin_sq_add_cos_sq s
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (Real.cos s * x 0 - Real.sin s * x 1)^2 +
      (Real.sin s * x 0 + Real.cos s * x 1)^2 = (x 0)^2 + (x 1)^2
    linear_combination ((x 0)^2 + (x 1)^2) * Real.sin_sq_add_cos_sq s

/-- In the rotated frame, angular coordinates are translated by the frame angle. -/
@[simp] theorem cone2dRotation_symm_circle (s θ : ℝ) :
    (cone2dRotation s).symm (cone2dCircle θ) = cone2dCircle (θ - s) := by
  ext i
  fin_cases i
  · change Real.cos s * Real.cos θ + Real.sin s * Real.sin θ = Real.cos (θ - s)
    rw [Real.cos_sub]
    ring
  · change -Real.sin s * Real.cos θ + Real.cos s * Real.sin θ = Real.sin (θ - s)
    rw [Real.sin_sub]
    ring

/-- Close to the frame angle, the left and right angular arcs lie in the
corresponding sectors with vertex slope zero. -/
theorem cone2dCircle_eventually_mem_sectors (s : ℝ) {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) :
    (∀ᶠ θ in 𝓝[<] s,
      cone2dCircle θ ∈ cone2dOpenSector (cone2dRotation s) c (-δ) 0) ∧
    (∀ᶠ θ in 𝓝[>] s,
      cone2dCircle θ ∈ cone2dOpenSector (cone2dRotation s) c 0 δ) := by
  have hcos : ∀ᶠ θ in 𝓝 s, 0 < Real.cos (θ - s) :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simp)
  have hlo : ∀ᶠ θ in 𝓝 s, -δ * Real.cos (θ - s) < c * Real.sin (θ - s) :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using hδ)
  have hhi : ∀ᶠ θ in 𝓝 s, c * Real.sin (θ - s) < δ * Real.cos (θ - s) :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using hδ)
  constructor
  · filter_upwards [hcos.filter_mono nhdsWithin_le_nhds,
      hlo.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds (show s - Real.pi < s by linarith [Real.pi_pos])).filter_mono
        nhdsWithin_le_nhds, self_mem_nhdsWithin] with θ hcos hlo hπ hθ
    simp only [cone2dOpenSector, mem_ofPred_eq, cone2dRotation_symm_circle,
      cone2dCircle_zero, cone2dCircle_one, zero_mul]
    exact ⟨hcos, hlo, mul_neg_of_pos_of_neg hc
      (Real.sin_neg_of_neg_of_neg_pi_lt (by exact sub_neg.mpr hθ) (by linarith))⟩
  · filter_upwards [hcos.filter_mono nhdsWithin_le_nhds,
      hhi.filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (show s < s + Real.pi by linarith [Real.pi_pos])).filter_mono
        nhdsWithin_le_nhds, self_mem_nhdsWithin] with θ hcos hhi hπ hθ
    simp only [cone2dOpenSector, mem_ofPred_eq, cone2dRotation_symm_circle,
      cone2dCircle_zero, cone2dCircle_one, zero_mul]
    exact ⟨hcos, mul_pos hc
      (Real.sin_pos_of_pos_of_lt_pi (by exact sub_pos.mpr hθ) (by linarith)), hhi⟩

/-- The canonical interior phase changes when the angular parameter crosses
any frontier point of a locally perimeter-minimizing planar cone. -/
theorem cone2dCircle_frontier_flip {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    {s : ℝ} (hs : cone2dCircle s ∈ frontier (densityOne C)) :
    ((∀ᶠ θ in 𝓝[<] s, cone2dCircle θ ∈ interior (densityOne C)) ∧
      (∀ᶠ θ in 𝓝[>] s, cone2dCircle θ ∈ interior ((densityOne C)ᶜ))) ∨
    ((∀ᶠ θ in 𝓝[<] s, cone2dCircle θ ∈ interior ((densityOne C)ᶜ)) ∧
      (∀ᶠ θ in 𝓝[>] s, cone2dCircle θ ∈ interior (densityOne C))) := by
  obtain ⟨c, hc, δ, hδ, hphases⟩ := cone2d_frontier_adjacent_sectors hmin hcone
    (cone2dRotation s) (u := cone2dCircle s) (by simp) hs
  simp only [cone2dRotation_symm_circle, sub_self, cone2dCircle_one, Real.sin_zero,
    cone2dCircle_zero, Real.cos_zero, zero_div, mul_zero, zero_sub, zero_add] at hphases
  have harcs := cone2dCircle_eventually_mem_sectors s (lt_trans zero_lt_one hc.1) hδ
  rcases hphases with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact Or.inl ⟨harcs.1.mono fun _ h => hl h, harcs.2.mono fun _ h => hr h⟩
  · exact Or.inr ⟨harcs.1.mono fun _ h => hl h, harcs.2.mono fun _ h => hr h⟩

/-- A continuous curve avoiding the frontier on a closed interval has the
same interior phase at both endpoints. This is purely topological. -/
theorem cone2d_phase_constant_on_interval
    {X : Type*} [TopologicalSpace X] {D : Set X} {f : ℝ → X}
    (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (havoid : ∀ t ∈ Icc a b, f t ∉ frontier D) :
    (f a ∈ interior D ↔ f b ∈ interior D) := by
  have hcover : Icc a b ⊆ (f ⁻¹' interior D) ∪ (f ⁻¹' interior Dᶜ) := by
    intro t ht
    have h := havoid t ht
    rw [← mem_compl_iff, compl_frontier_eq_union_interior] at h
    exact h
  have hdisj : Disjoint (f ⁻¹' interior D) (f ⁻¹' interior Dᶜ) := by
    apply disjoint_left.mpr
    intro t ht ht'
    exact interior_subset ht' (interior_subset ht)
  constructor
  · intro ha
    exact (isPreconnected_Icc.subset_left_of_subset_union
      (isOpen_interior.preimage hf) (isOpen_interior.preimage hf)
      hdisj hcover ⟨a, ⟨le_rfl, hab⟩, ha⟩) ⟨hab, le_rfl⟩
  · intro hb
    exact (isPreconnected_Icc.subset_left_of_subset_union
      (isOpen_interior.preimage hf) (isOpen_interior.preimage hf)
      hdisj hcover ⟨b, ⟨hab, le_rfl⟩, hb⟩) ⟨le_rfl, hab⟩

/-- A one-sided phase change admits nearby points in opposite phases, with
no further frontier point up to the chosen right endpoint. -/
theorem cone2d_flip_choose
    {X : Type*} [TopologicalSpace X] {D : Set X} {f : ℝ → X}
    {a s b : ℝ} (has : a < s) (hsb : s < b)
    (hflip :
      ((∀ᶠ t in 𝓝[<] s, f t ∈ interior D) ∧
        (∀ᶠ t in 𝓝[>] s, f t ∈ interior Dᶜ)) ∨
      ((∀ᶠ t in 𝓝[<] s, f t ∈ interior Dᶜ) ∧
        (∀ᶠ t in 𝓝[>] s, f t ∈ interior D))) :
    ∃ l ∈ Ioo a s, ∃ r ∈ Ioo s b,
      f l ∉ frontier D ∧ f r ∉ frontier D ∧
      (f l ∈ interior D ↔ f r ∉ interior D) ∧
      ∀ t ∈ Ioc s r, f t ∉ frontier D := by
  have hlpick {P : ℝ → Prop} (hP : ∀ᶠ t in 𝓝[<] s, P t) :
      ∃ l ∈ Ioo a s, P l := by
    have h := hP.and ((eventually_gt_nhds has).filter_mono nhdsWithin_le_nhds)
    obtain ⟨l, ⟨hl, hal⟩, hls⟩ := (h.and self_mem_nhdsWithin).exists
    exact ⟨l, ⟨hal, hls⟩, hl⟩
  have hrpick {P : ℝ → Prop} (hP : ∀ᶠ t in 𝓝[>] s, P t) :
      ∃ r ∈ Ioo s b, ∀ t ∈ Ioc s r, P t := by
    have h := hP.and ((eventually_lt_nhds hsb).filter_mono nhdsWithin_le_nhds)
    obtain ⟨r, hsr, hr⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp h
    exact ⟨r, ⟨hsr, (hr ⟨hsr, le_rfl⟩).2⟩, fun t ht => (hr ht).1⟩
  have hn {x : X} (hx : x ∈ interior D) : x ∉ frontier D :=
    fun h => disjoint_left.mp disjoint_interior_frontier hx h
  have hnc {x : X} (hx : x ∈ interior Dᶜ) : x ∉ frontier D := by
    rw [← frontier_compl]
    exact fun h => disjoint_left.mp disjoint_interior_frontier hx h
  have hni {x : X} (hx : x ∈ interior Dᶜ) : x ∉ interior D :=
    fun h => interior_subset hx (interior_subset h)
  rcases hflip with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · obtain ⟨l, hl, hlp⟩ := hlpick hl
    obtain ⟨r, hr, hrp⟩ := hrpick hr
    have hrp' := hrp r ⟨hr.1, le_rfl⟩
    exact ⟨l, hl, r, hr, hn hlp, hnc hrp',
      ⟨fun _ => hni hrp', fun _ => hlp⟩, fun t ht => hnc (hrp t ht)⟩
  · obtain ⟨l, hl, hlp⟩ := hlpick hl
    obtain ⟨r, hr, hrp⟩ := hrpick hr
    have hrp' := hrp r ⟨hr.1, le_rfl⟩
    exact ⟨l, hl, r, hr, hnc hlp, hn hrp',
      ⟨fun h => (hni hlp h).elim, fun h => (h hrp').elim⟩,
      fun t ht => hn (hrp t ht)⟩

/-- For a continuous curve with finitely many frontier crossings, each of which
changes the phase, equal endpoint phases are equivalent to an even crossing count. -/
theorem cone2d_phase_parity_on_interval
    {X : Type*} [TopologicalSpace X] {D : Set X} {f : ℝ → X}
    (hf : Continuous f)
    (hflip : ∀ s, f s ∈ frontier D →
      ((∀ᶠ t in 𝓝[<] s, f t ∈ interior D) ∧
        (∀ᶠ t in 𝓝[>] s, f t ∈ interior Dᶜ)) ∨
      ((∀ᶠ t in 𝓝[<] s, f t ∈ interior Dᶜ) ∧
        (∀ᶠ t in 𝓝[>] s, f t ∈ interior D)))
    {a b : ℝ} (hab : a < b) (ha : f a ∉ frontier D) (hb : f b ∉ frontier D)
    (hfin : (f ⁻¹' frontier D ∩ Ioo a b).Finite) :
    (f a ∈ interior D ↔ f b ∈ interior D) ↔
      Even (f ⁻¹' frontier D ∩ Ioo a b).ncard := by
  classical
  generalize hn : (f ⁻¹' frontier D ∩ Ioo a b).ncard = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases he : (f ⁻¹' frontier D ∩ Ioo a b) = ∅
    · have hconst := cone2d_phase_constant_on_interval hf hab.le (D := D) (by
        intro t ht htf
        by_cases hta : t = a
        · exact ha (hta ▸ htf)
        by_cases htb : t = b
        · exact hb (htb ▸ htf)
        have ht' : t ∈ f ⁻¹' frontier D ∩ Ioo a b :=
          ⟨htf, lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
        rw [he] at ht'
        exact ht')
      subst n
      simp only [he, ncard_empty]
      exact iff_of_true hconst (by exact ⟨0, rfl⟩)
    · obtain ⟨s, hs, hleast⟩ := Set.exists_min_image _ id hfin (nonempty_iff_ne_empty.mpr he)
      obtain ⟨l, hl, r, hr, hlf, hrf, hop, hgap⟩ :=
        cone2d_flip_choose hs.2.1 hs.2.2 (hflip s hs.1)
      have hal : f a ∈ interior D ↔ f l ∈ interior D :=
        cone2d_phase_constant_on_interval hf hl.1.le (by
          intro t ht htf
          by_cases hta : t = a
          · exact ha (hta ▸ htf)
          have ht' : t ∈ f ⁻¹' frontier D ∩ Ioo a b :=
            ⟨htf, lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2.trans_lt (hl.2.trans hs.2.2)⟩
          have hst := hleast t ht'
          dsimp only [id] at hst
          linarith [ht.2, hl.2])
      have hsub : f ⁻¹' frontier D ∩ Ioo r b ⊆ f ⁻¹' frontier D ∩ Ioo a b := by
        intro t ht
        exact ⟨ht.1, hs.2.1.trans (hr.1.trans ht.2.1), ht.2.2⟩
      have hfin' := hfin.subset hsub
      have hsnot : s ∉ f ⁻¹' frontier D ∩ Ioo r b := by
        intro ht
        exact (hr.1.trans ht.2.1).false
      have hdecomp : f ⁻¹' frontier D ∩ Ioo a b =
          insert s (f ⁻¹' frontier D ∩ Ioo r b) := by
        ext t
        constructor
        · intro ht
          by_cases hts : t = s
          · exact Or.inl hts
          · have hst : s < t := lt_of_le_of_ne (hleast t ht) (Ne.symm hts)
            have hrt : r < t := by
              by_contra h
              exact hgap t ⟨hst, le_of_not_gt h⟩ ht.1
            exact Or.inr ⟨ht.1, hrt, ht.2.2⟩
        · rintro (rfl | ht)
          · exact hs
          · exact hsub ht
      have hcard : (f ⁻¹' frontier D ∩ Ioo a b).ncard =
          (f ⁻¹' frontier D ∩ Ioo r b).ncard + 1 := by
        rw [hdecomp, ncard_insert_of_notMem hsnot hfin']
      have hlt : (f ⁻¹' frontier D ∩ Ioo r b).ncard < n := by omega
      have hih := ih _ hlt hr.2 hrf hb hfin' rfl
      rw [← hn, hcard, Nat.even_add_one, ← hih]
      tauto

/-- Angular parametrization is injective on any half-open interval of one turn. -/
theorem cone2dCircle_injOn (a : ℝ) :
    InjOn cone2dCircle (Ico a (a + 2 * Real.pi)) := by
  intro x hx y hy hxy
  have hc : Real.cos x = Real.cos y := congrArg (fun u => u 0) hxy
  have hs : Real.sin x = Real.sin y := congrArg (fun u => u 1) hxy
  have hd : Real.cos (x - y) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.sin_sq_add_cos_sq y]
  exact sub_eq_zero.mp ((Real.cos_eq_one_iff_of_lt_of_lt
    (by linarith [hx.1, hy.2]) (by linarith [hx.2, hy.1])).mp hd)

/-- Every point of the Euclidean unit circle has an angular representative
between minus pi and pi. -/
theorem cone2dCircle_surjOn :
    SurjOn cone2dCircle (Icc (-Real.pi) Real.pi) (Metric.sphere 0 1) := by
  intro u hu
  have hn : ‖u‖ = 1 := by simpa using hu
  have hsq : (u 0)^2 + (u 1)^2 = 1 := by
    simpa [Fin.sum_univ_two, hn] using (EuclideanSpace.real_norm_sq_eq u).symm
  have hcoord : u 0 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg (u 1)]
  obtain ⟨θ, hθ, hcos⟩ := Real.surjOn_cos hcoord
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ
  have hsinSq : (Real.sin θ)^2 = (u 1)^2 := by
    have ht := Real.sin_sq_add_cos_sq θ
    rw [hcos] at ht
    linarith
  by_cases hu1 : 0 ≤ u 1
  · refine ⟨θ, ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩, ?_⟩
    ext i
    fin_cases i
    · exact hcos
    · exact (sq_eq_sq₀ hsin hu1).mp hsinSq
  · refine ⟨-θ, ⟨by linarith [hθ.2], by linarith [hθ.1, Real.pi_pos]⟩, ?_⟩
    ext i
    fin_cases i
    · simpa using hcos
    · change Real.sin (-θ) = u 1
      rw [Real.sin_neg]
      have h := (sq_eq_sq₀ hsin (neg_nonneg.mpr (le_of_not_ge hu1))).mp
        (show (Real.sin θ)^2 = (-u 1)^2 by nlinarith [hsinSq])
      linarith

/-- On any one-turn interval, finitely many link points have finitely many
angular representatives. -/
theorem cone2dCircle_frontier_finite {D : Set (EuclideanSpace ℝ (Fin 2))}
    (hfin : (frontier D ∩ Metric.sphere 0 1).Finite) (a : ℝ) :
    (cone2dCircle ⁻¹' frontier D ∩ Ico a (a + 2 * Real.pi)).Finite := by
  apply (finite_image_iff ((cone2dCircle_injOn a).mono inter_subset_right)).mp
  apply hfin.subset
  rintro u ⟨θ, hθ, rfl⟩
  exact ⟨hθ.1, cone2dCircle_mem_sphere θ⟩

/-- There is a starting angle strictly between zero and pi whose circle point
avoids any prescribed finite link. -/
theorem cone2dCircle_exists_start {D : Set (EuclideanSpace ℝ (Fin 2))}
    (hfin : (frontier D ∩ Metric.sphere 0 1).Finite) :
    ∃ a ∈ Ioo 0 Real.pi, cone2dCircle a ∉ frontier D := by
  obtain ⟨a, ha, havoid⟩ := (Ioo_infinite Real.pi_pos).exists_notMem_finite
    (cone2dCircle_frontier_finite hfin 0)
  refine ⟨a, ha, fun h => havoid ⟨h, ?_⟩⟩
  exact ⟨ha.1.le, by linarith [ha.2, Real.pi_pos]⟩

/-- If the starting point avoids the frontier, one open angular turn represents
every point of the link exactly once. -/
theorem cone2dCircle_image_frontier {D : Set (EuclideanSpace ℝ (Fin 2))}
    {a : ℝ} (ha : a ∈ Ioo 0 Real.pi) (havoid : cone2dCircle a ∉ frontier D) :
    cone2dCircle '' (cone2dCircle ⁻¹' frontier D ∩ Ioo a (a + 2 * Real.pi)) =
      frontier D ∩ Metric.sphere 0 1 := by
  apply subset_antisymm
  · rintro u ⟨θ, hθ, rfl⟩
    exact ⟨hθ.1, cone2dCircle_mem_sphere θ⟩
  · intro u hu
    obtain ⟨θ, hθ, heq⟩ := cone2dCircle_surjOn hu.2
    have huθ : cone2dCircle θ ∈ frontier D := heq.symm ▸ hu.1
    by_cases haθ : a ≤ θ
    · have hne : θ ≠ a := by
        rintro rfl
        exact havoid huθ
      refine ⟨θ, ⟨huθ, lt_of_le_of_ne haθ (Ne.symm hne), ?_⟩, heq⟩
      linarith [hθ.2, ha.1, Real.pi_pos]
    · refine ⟨θ + 2 * Real.pi, ⟨?_, ?_, ?_⟩, ?_⟩
      · simpa only [mem_preimage, cone2dCircle_add_two_pi, heq] using hu.1
      · linarith [hθ.1, ha.2]
      · linarith [lt_of_not_ge haθ]
      · simpa using heq

/-- The canonical frontier of a locally perimeter-minimizing planar cone meets
the unit circle in an even number of points. -/
theorem cone2d_link_even {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C) :
    Even (frontier (densityOne C) ∩ Metric.sphere 0 1).ncard := by
  have hfin := cone2d_link_finite hmin hcone
  obtain ⟨a, ha, havoid⟩ := cone2dCircle_exists_start hfin
  have hfin' :
      (cone2dCircle ⁻¹' frontier (densityOne C) ∩ Ioo a (a + 2 * Real.pi)).Finite :=
    (cone2dCircle_frontier_finite hfin a).subset
      (inter_subset_inter_right _ Ioo_subset_Ico_self)
  have heven := (cone2d_phase_parity_on_interval cone2dCircle_continuous
    (fun _ hs => cone2dCircle_frontier_flip hmin hcone hs)
    (show a < a + 2 * Real.pi by linarith [Real.pi_pos]) havoid
    (by simpa using havoid) hfin').mp (by simp)
  have himage := cone2dCircle_image_frontier ha havoid
  rw [← himage, ((cone2dCircle_injOn a).mono
    (inter_subset_right.trans Ioo_subset_Ico_self)).ncard_image]
  exact heven

/-- Blueprint `lem:cone-2d-link`, all three clauses. -/
theorem cone2d_link {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C) :
    (frontier (densityOne C) ∩ Metric.sphere 0 1).Finite ∧
    frontier (densityOne C) \ {0} =
      {x | x ≠ 0 ∧ ‖x‖⁻¹ • x ∈ frontier (densityOne C) ∩ Metric.sphere 0 1} ∧
    Even (frontier (densityOne C) ∩ Metric.sphere 0 1).ncard := by
  exact ⟨cone2d_link_finite hmin hcone, cone2d_frontier_eq_rays hcone,
    cone2d_link_even hmin hcone⟩

end LiquidDrop
