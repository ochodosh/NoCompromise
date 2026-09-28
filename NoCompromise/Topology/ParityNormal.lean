import NoCompromise.Topology.OrientationParity

/-!
# The global unit normal selected by parity (`prop:orientation-parity` (ii))

At each surface point exactly one unit normal points towards odd intersection parity. The
signed normalised gradients of local charts realise this choice; a smooth partition of unity
glues them into a smooth ambient unit normal field. In particular every compact smooth embedded
surface in `ℝ³` is orientable.
-/

namespace LiquidDrop

noncomputable section
open Set Filter
open scoped Topology Gradient

private lemma eventually_line_mem_ball {p q v : E₃} {r : ℝ}
    (hq : q ∈ Metric.ball p r) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      q + s • v ∈ Metric.ball p r ∧ q - s • v ∈ Metric.ball p r := by
  have hp : Continuous (fun s : ℝ => q + s • v) := by fun_prop
  have hm : Continuous (fun s : ℝ => q - s • v) := by fun_prop
  have hp' : ∀ᶠ s in 𝓝 (0 : ℝ), q + s • v ∈ Metric.ball p r :=
    (hp.continuousAt (x := 0)).preimage_mem_nhds
    (by simpa using Metric.isOpen_ball.mem_nhds hq)
  have hm' : ∀ᶠ s in 𝓝 (0 : ℝ), q - s • v ∈ Metric.ball p r :=
    (hm.continuousAt (x := 0)).preimage_mem_nhds
    (by simpa using Metric.isOpen_ball.mem_nhds hq)
  exact nhdsWithin_le_nhds (hp'.and hm')

/-- prop:orientation-parity (ii): a regular chart has a single parity sign, valid at every
surface point of a sufficiently small ball and every direction of positive derivative. -/
lemma parity_normal_chart_sign {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) {z : E₃} (hz : z ∉ S)
    {U : Set E₃} {φ : E₃ → ℝ} (hU : IsOpen U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hzero : S ∩ U = {x ∈ U | φ x = 0}) (hreg : ∀ x ∈ S ∩ U, gradient φ x ≠ 0)
    {p : E₃} (hp : p ∈ S) (hpU : p ∈ U) :
    ∃ r > 0, Metric.ball p r ⊆ U ∧ ∃ b : Prop,
      ∀ q ∈ S ∩ Metric.ball p r, ∀ v : E₃, 0 < fderiv ℝ φ q v →
        ∀ᶠ s in 𝓝[>] (0 : ℝ),
          (SurfaceOddParity S z (q + s • v) ↔ b) ∧
          (SurfaceOddParity S z (q - s • v) ↔ ¬ b) := by
  classical
  obtain ⟨r, hr, hrU, hsides⟩ := surfaceOddParity_local_sides hS hc hz hU hφ hzero hreg hp hpU
  have hφp : φ p = 0 := (hzero ▸ (show p ∈ S ∩ U from ⟨hp, hpU⟩)).2
  have hg := hreg p ⟨hp, hpU⟩
  have hd : 0 < fderiv ℝ φ p (gradient φ p) := by
    rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hg) 2
  obtain ⟨s, hsign, hball⟩ := ((eventually_sign_along_line
    (hφ.differentiable (by simp) p) hφp hd).and
    (eventually_line_mem_ball (v := gradient φ p) (Metric.mem_ball_self hr))).exists
  refine ⟨r, hr, hrU, SurfaceOddParity S z (p + s • gradient φ p), ?_⟩
  intro q hq v hv
  have hφq : φ q = 0 := (hzero ▸ (show q ∈ S ∩ U from ⟨hq.1, hrU hq.2⟩)).2
  filter_upwards [eventually_sign_along_line (hφ.differentiable (by simp) q) hφq hv,
    eventually_line_mem_ball (v := v) hq.2] with t ht htball
  have ha := (hsides _ htball.1 _ hball.1).1 ht.1 hsign.1
  have hb := (hsides _ hball.1 _ htball.2).2.2 hsign.1 ht.2
  exact ⟨ha, by tauto⟩

private lemma unit_normal_eq_or_neg {g v : E₃} (hg : g ≠ 0) (hv : ‖v‖ = 1)
    (hvorth : ∀ X ∈ (ℝ ∙ g)ᗮ, inner ℝ v X = 0) :
    v = ‖g‖⁻¹ • g ∨ v = -(‖g‖⁻¹ • g) := by
  have hmem : v ∈ ℝ ∙ g := by
    rw [← Submodule.orthogonal_orthogonal (ℝ ∙ g)]
    exact (Submodule.mem_orthogonal' _ _).mpr hvorth
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  have hnorm : |a| = ‖g‖⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs] at hv
    simpa only [one_div] using (eq_div_iff (norm_ne_zero_iff.mpr hg)).mpr hv
  rcases (abs_eq (inv_nonneg.mpr (norm_nonneg g))).mp hnorm with ha | ha
  · exact Or.inl (by rw [ha])
  · exact Or.inr (by rw [ha, neg_smul])

/-- prop:orientation-parity (ii): exactly one unit normal points toward odd parity. -/
theorem exists_unique_parity_normal {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) {z : E₃} (hz : z ∉ S) {p : E₃} (hp : p ∈ S) :
    ∃! ν : E₃, ‖ν‖ = 1 ∧ (∀ X ∈ tangentPlane S p, inner ℝ ν X = 0) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), SurfaceOddParity S z (p + s • ν) := by
  classical
  obtain ⟨U, φ, hU, hpU, hφ, hzero, hreg⟩ := hS p hp
  have hg := hreg p ⟨hp, hpU⟩
  have hT := tangentPlane_eq hU hpU (hφ.of_le (by simp)).contDiffAt hzero hp hg
  let v : E₃ := ‖gradient φ p‖⁻¹ • gradient φ p
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hg]
  have hvorth : ∀ X ∈ tangentPlane S p, inner ℝ v X = 0 := by
    intro X hX
    have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hT ▸ hX)
    simp [v, real_inner_smul_left, hx]
  have hd : 0 < fderiv ℝ φ p v := by
    rw [← inner_gradient_left]
    simp only [v, inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hg)) (pow_pos (norm_pos_iff.mpr hg) 2)
  obtain ⟨r, hr, _, b, hb⟩ := parity_normal_chart_sign hS hc hz hU hφ hzero hreg hp hpU
  have he := hb p ⟨hp, Metric.mem_ball_self hr⟩ v hd
  have hall : ∀ w : E₃, ‖w‖ = 1 → (∀ X ∈ tangentPlane S p, inner ℝ w X = 0) →
      w = v ∨ w = -v := by
    intro w hw hworth
    exact unit_normal_eq_or_neg hg hw (by simpa only [← hT] using hworth)
  by_cases hbtrue : b
  · refine ⟨v, ⟨hv, hvorth, he.mono fun s hs => hs.1.mpr hbtrue⟩, ?_⟩
    intro w hw
    rcases hall w hw.1 hw.2.1 with h | h
    · exact h
    · exfalso
      obtain ⟨s, hs, hs'⟩ := (he.and hw.2.2).exists
      have hn : ¬ SurfaceOddParity S z (p - s • v) := fun hn => hs.2.mp hn hbtrue
      exact hn (by simpa [h, smul_neg, sub_eq_add_neg] using hs')
  · refine ⟨-v, ⟨by simpa using hv, ?_, ?_⟩, ?_⟩
    · intro X hX
      simp [inner_neg_left, hvorth X hX]
    · filter_upwards [he] with s hs
      simpa [smul_neg, sub_eq_add_neg] using hs.2.mpr hbtrue
    · intro w hw
      rcases hall w hw.1 hw.2.1 with h | h
      · exfalso
        obtain ⟨s, hs, hs'⟩ := (he.and hw.2.2).exists
        exact hbtrue (hs.1.mp (by simpa [h] using hs'))
      · exact h


/-- prop:orientation-parity (ii): the opposite of the selected direction has even parity. -/
lemma parity_normal_opposite {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) {z : E₃} (hz : z ∉ S) {p ν : E₃} (hp : p ∈ S)
    (hν : ‖ν‖ = 1) (horth : ∀ X ∈ tangentPlane S p, inner ℝ ν X = 0)
    (hodd : ∀ᶠ s in 𝓝[>] (0 : ℝ), SurfaceOddParity S z (p + s • ν)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      SurfaceOddParity S z (p + s • ν) ∧ ¬ SurfaceOddParity S z (p - s • ν) := by
  have htrans : ν ∉ tangentPlane S p := by
    intro hh
    have h := horth ν hh
    rw [real_inner_self_eq_norm_sq, hν] at h
    norm_num at h
  obtain ⟨r, hr, hcross⟩ := surfaceOddParity_crossing hS hc hz p hp ν htrans
  filter_upwards [hodd, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds hr)] with s hs hspos hslt
  exact ⟨hs, fun hn => hcross s ⟨hspos, hslt⟩ (by tauto)⟩

/-- prop:orientation-parity (ii): the parity-selected unit normal has a smooth local
ambient representative near each surface point. -/
lemma exists_local_parity_normal {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) {z : E₃} (hz : z ∉ S) {p : E₃} (hp : p ∈ S) :
    ∃ V : Set E₃, IsOpen V ∧ p ∈ V ∧ ∃ n : E₃ → E₃,
      ContDiffOn ℝ (⊤ : ℕ∞) n V ∧
      ∀ q ∈ S ∩ V, ‖n q‖ = 1 ∧
        (∀ X ∈ tangentPlane S q, inner ℝ (n q) X = 0) ∧
        ∀ᶠ s in 𝓝[>] (0 : ℝ), SurfaceOddParity S z (q + s • n q) := by
  classical
  obtain ⟨U, φ, hU, hpU, hφ, hzero, hreg⟩ := hS p hp
  obtain ⟨r, hr, hrU, b, hb⟩ := parity_normal_chart_sign hS hc hz hU hφ hzero hreg hp hpU
  have hg : ContDiff ℝ (⊤ : ℕ∞) (gradient φ) :=
    (InnerProductSpace.toDual ℝ E₃).symm.contDiff.comp (hφ.fderiv_right (by simp))
  let V : Set E₃ := Metric.ball p r ∩ {q | gradient φ q ≠ 0}
  have hV : IsOpen V := Metric.isOpen_ball.inter (isOpen_ne_fun hg.continuous continuous_const)
  have hpV : p ∈ V := ⟨Metric.mem_ball_self hr, hreg p ⟨hp, hpU⟩⟩
  let v : E₃ → E₃ := fun q => ‖gradient φ q‖⁻¹ • gradient φ q
  have hvdiff : ContDiffOn ℝ (⊤ : ℕ∞) v V := by
    intro q hq
    exact (((hg.contDiffAt.norm ℝ hq.2).inv (norm_ne_zero_iff.mpr hq.2)).smul
      hg.contDiffAt).contDiffWithinAt
  have hvunit (q : E₃) (hq : q ∈ S ∩ V) : ‖v q‖ = 1 := by
    simp [v, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      norm_ne_zero_iff.mpr hq.2.2]
  have hvorth (q : E₃) (hq : q ∈ S ∩ V) :
      ∀ X ∈ tangentPlane S q, inner ℝ (v q) X = 0 := by
    intro X hX
    have hT := tangentPlane_eq hU (hrU hq.2.1) (hφ.of_le (by simp)).contDiffAt
      hzero hq.1 hq.2.2
    have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hT ▸ hX)
    simp [v, real_inner_smul_left, hx]
  have hvpar (q : E₃) (hq : q ∈ S ∩ V) :
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        (SurfaceOddParity S z (q + s • v q) ↔ b) ∧
        (SurfaceOddParity S z (q - s • v q) ↔ ¬ b) := by
    apply hb q ⟨hq.1, hq.2.1⟩ (v q)
    rw [← inner_gradient_left]
    simp only [v, inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hq.2.2))
      (pow_pos (norm_pos_iff.mpr hq.2.2) 2)
  by_cases hbtrue : b
  · refine ⟨V, hV, hpV, v, hvdiff, fun q hq => ⟨hvunit q hq, hvorth q hq, ?_⟩⟩
    exact (hvpar q hq).mono fun s hs => hs.1.mpr hbtrue
  · refine ⟨V, hV, hpV, fun q => -(v q), hvdiff.neg,
      fun q hq => ⟨by simpa using hvunit q hq, ?_, ?_⟩⟩
    · intro X hX
      simp [inner_neg_left, hvorth q hq X hX]
    · filter_upwards [hvpar q hq] with s hs
      simpa [smul_neg, sub_eq_add_neg] using hs.2.mpr hbtrue

open scoped Manifold

/-- prop:orientation-parity (ii): a global smooth ambient unit normal on the surface,
selected by odd parity in the positive normal direction and even parity in the negative one. -/
theorem exists_parity_unitNormalField {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) {z : E₃} (hz : z ∉ S) :
    ∃ n : E₃ → E₃, IsUnitNormalField S n ∧
      ∀ p ∈ S, ∀ᶠ s in 𝓝[>] (0 : ℝ),
        SurfaceOddParity S z (p + s • n p) ∧ ¬ SurfaceOddParity S z (p - s • n p) := by
  classical
  choose V hV hpV n hndiff hn using fun p : S =>
    exists_local_parity_normal hS hc hz p.property
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E₃)) hc.isClosed V hV (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩)
  let N : E₃ → E₃ := fun x => ∑ᶠ i, ρ i x • n i x
  have hN : ContDiff ℝ (⊤ : ℕ∞) N :=
    (hρ.contMDiff_finsum_smul hV (fun i => (hndiff i).contMDiffOn)).contDiff
  have hpoint (p : E₃) (hp : p ∈ S) :
      ‖N p‖ = 1 ∧ (∀ X ∈ tangentPlane S p, inner ℝ (N p) X = 0) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), SurfaceOddParity S z (p + s • N p) := by
    obtain ⟨ν, hν, huniq⟩ := exists_unique_parity_normal hS hc hz hp
    have hNν : N p ∈ ({ν} : Set E₃) := by
      apply ρ.finsum_smul_mem_convex hp _ (convex_singleton ν)
      intro i hi
      exact mem_singleton_iff.mpr (huniq _ (hn i p ⟨hp,
        hρ i (subset_closure (Function.mem_support.mpr hi))⟩))
    simpa only [mem_singleton_iff.mp hNν] using hν
  refine ⟨N, ⟨⟨univ, isOpen_univ, subset_univ _, hN.contDiffOn⟩,
    fun p hp => ⟨(hpoint p hp).1, (hpoint p hp).2.1⟩⟩, ?_⟩
  intro p hp
  exact parity_normal_opposite hS hc hz hp (hpoint p hp).1 (hpoint p hp).2.1
    (hpoint p hp).2.2

/-- prop:orientation-parity (ii): every compact smooth embedded surface in three-space
admits a smooth ambient unit normal field. -/
theorem exists_unitNormalField_of_isCompact {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) :
    ∃ n : E₃ → E₃, IsUnitNormalField S n := by
  obtain ⟨z, hz⟩ := exists_not_mem_of_isCompact hc
  obtain ⟨n, hn, _⟩ := exists_parity_unitNormalField hS hc hz
  exact ⟨n, hn⟩

/-- `prop:orientation-parity`, bundled: for a compact connected smooth embedded surface and a
base point `z` off it, (i) transverse paths from `z` with a common endpoint have intersection
counts of the same parity, (ii) a smooth global unit normal points towards odd parity, and
(iii) the complement has exactly two connected components. -/
theorem orientation_parity {S : Set E₃} (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    (hconn : IsConnected S) {z : E₃} (hz : z ∉ S) :
    (∀ α β : EuclideanSpace ℝ (Fin 1) → E₃, ContDiff ℝ (⊤ : ℕ∞) α → ContDiff ℝ (⊤ : ℕ∞) β →
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p) →
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S β p) →
      α (EuclideanSpace.single 0 (-1)) = z → β (EuclideanSpace.single 0 (-1)) = z →
      α (EuclideanSpace.single 0 1) = β (EuclideanSpace.single 0 1) →
      α (EuclideanSpace.single 0 1) ∉ S →
      Even ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S).ncard +
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ β ⁻¹' S).ncard)) ∧
    (∃ n : E₃ → E₃, IsUnitNormalField S n ∧
      ∀ p ∈ S, ∀ᶠ s in 𝓝[>] (0 : ℝ),
        SurfaceOddParity S z (p + s • n p) ∧ ¬ SurfaceOddParity S z (p - s • n p)) ∧
    Nat.card (ConnectedComponents (Sᶜ : Set E₃)) = 2 := by
  refine ⟨fun α β hα hβ htα htβ hα0 hβ0 h1 hx => ?_, exists_parity_unitNormalField hS hc hz,
    card_connectedComponents_compl_surface_eq_two hS hc hconn⟩
  exact even_add_ncard_transverse_paths hS hc hα hβ htα htβ (hα0.trans hβ0.symm) h1
    (hα0 ▸ hz) hx

end

end LiquidDrop
