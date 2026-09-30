module

public import NoCompromise.Surface.Geometry
public import Mathlib.Topology.Sequences

@[expose] public section

/-!
# Concrete normal coordinates

The local inverse-function construction uses the square ambient map
`(x,t) ↦ (x + t • n x, φ x)`. Its restriction to the zero level in the
last target coordinate gives the normal coordinates on the surface.
-/

noncomputable section
open Set Filter Function InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The normal-coordinate map, on ambient representatives. -/
def normalCoordinateMap (n : E₃ → E₃) (q : E₃ × ℝ) : E₃ := q.1 + q.2 • n q.1

/-- The image of the normal coordinates of width `ε`. -/
def normalTube (S : Set E₃) (n : E₃ → E₃) (ε : ℝ) : Set E₃ :=
  normalCoordinateMap n '' (S ×ˢ Ioo (-ε) ε)

lemma subset_normalTube {S : Set E₃} {n : E₃ → E₃} {ε : ℝ} (hε : 0 < ε) :
    S ⊆ normalTube S n ε := by
  intro p hp
  exact ⟨(p, 0), ⟨hp, neg_neg_of_pos hε, hε⟩, by simp [normalCoordinateMap]⟩

/-- Local injectivity and openness of normal coordinates at every surface point. -/
theorem exists_normalCoordinate_neighbourhood {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p : E₃} (hp : p ∈ S) :
    ∃ W : Set (E₃ × ℝ), IsOpen W ∧ (p, 0) ∈ W ∧
      InjOn (normalCoordinateMap n) ((S ×ˢ univ) ∩ W) ∧
      (∀ V : Set (E₃ × ℝ), IsOpen V → V ⊆ W →
        IsOpen (normalCoordinateMap n '' ((S ×ˢ univ) ∩ V))) ∧
      ∃ g : E₃ → E₃ × ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) g (normalCoordinateMap n '' ((S ×ˢ univ) ∩ W)) ∧
        ∀ q ∈ (S ×ˢ univ) ∩ W, g (normalCoordinateMap n q) = q := by
  obtain ⟨U, φ, hU, hpU, hφ, hz, hr⟩ := hS p hp
  have hφp : φ p = 0 := (hz ▸ (show p ∈ S ∩ U from ⟨hp, hpU⟩)).2
  have htrans : fderiv ℝ φ p (n p) ≠ 0 := by
    intro he
    have hmem : n p ∈ tangentPlane S p := by
      rw [tangentPlane_eq hU hpU (hφ.of_le (by simp)).contDiffAt hz hp (hr p ⟨hp, hpU⟩),
        Submodule.mem_orthogonal_singleton_iff_inner_right, inner_gradient_left]
      exact he
    have hzero := (hn.2 p hp).2 (n p) hmem
    have hnp : n p = 0 := inner_self_eq_zero.mp hzero
    have := (hn.2 p hp).1
    simp [hnp] at this
  let L : (E₃ × ℝ) →L[ℝ] (E₃ × ℝ) :=
    ((ContinuousLinearMap.fst ℝ E₃ ℝ) + (ContinuousLinearMap.snd ℝ E₃ ℝ).smulRight (n p)).prod
      ((fderiv ℝ φ p).comp (ContinuousLinearMap.fst ℝ E₃ ℝ))
  have hL : Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro q hq
    change q = 0
    have hq' : q.1 + q.2 • n p = 0 ∧ fderiv ℝ φ p q.1 = 0 := by
      simpa [L, Prod.ext_iff] using hq
    have ht : q.2 = 0 := by
      have hh := congrArg (fderiv ℝ φ p) hq'.1
      simp only [map_add, map_smul, map_zero, hq'.2, zero_add, smul_eq_mul] at hh
      exact (mul_eq_zero.mp hh).resolve_right htrans
    have hx : q.1 = 0 := by simpa [ht] using hq'.1
    exact Prod.ext hx ht
  let eL : (E₃ × ℝ) ≃L[ℝ] (E₃ × ℝ) :=
    (LinearEquiv.ofInjectiveEndo L.toLinearMap hL).toContinuousLinearEquiv
  let F : E₃ × ℝ → E₃ × ℝ := fun q => (normalCoordinateMap n q, φ q.1)
  have hn' := hn.contDiffAt hp
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) F (p, 0) :=
    (contDiffAt_fst.add (contDiffAt_snd.smul (hn'.comp (p, 0) contDiffAt_fst))).prodMk
      (hφ.contDiffAt.comp (p, 0) contDiffAt_fst)
  have hF' : HasFDerivAt F eL.toContinuousLinearMap (p, 0) := by
    have hdφ : HasFDerivAt φ (fderiv ℝ φ p) p :=
      (hφ.differentiable (by simp) p).hasFDerivAt
    have hdn : HasFDerivAt n (fderiv ℝ n p) p :=
      (hn'.differentiableAt (by simp)).hasFDerivAt
    have hfst : HasFDerivAt (fun q : E₃ × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ E₃ ℝ) (p, 0) := hasFDerivAt_fst
    have hd := (hasFDerivAt_fst.add (hasFDerivAt_snd.smul
      (hdn.comp (p, (0 : ℝ)) hfst))).prodMk (hdφ.comp (p, (0 : ℝ)) hfst)
    convert! hd using 1
    ext q <;> simp [eL, L]
  obtain ⟨N, hN, hSN, hnN⟩ := hn.1
  let O : Set (E₃ × ℝ) := N ×ˢ univ
  have hO : IsOpen O := hN.prod isOpen_univ
  have hFO : ContDiffOn ℝ (⊤ : ℕ∞) F O :=
    (contDiffOn_fst.add (contDiffOn_snd.smul (hnN.comp contDiffOn_fst
      (fun _ hq => hq.1)))).prodMk (hφ.contDiffOn.comp contDiffOn_fst (mapsTo_univ _ _))
  let V := O ∩ (fderiv ℝ F) ⁻¹' range
    ((↑) : ((E₃ × ℝ) ≃L[ℝ] (E₃ × ℝ)) → (E₃ × ℝ) →L[ℝ] (E₃ × ℝ))
  have hV : IsOpen V :=
    (hFO.continuousOn_fderiv_of_isOpen hO (by simp)).isOpen_inter_preimage
      hO ContinuousLinearEquiv.isOpen
  have hpV : (p, (0 : ℝ)) ∈ V :=
    ⟨⟨hSN hp, mem_univ _⟩, eL, hF'.fderiv.symm⟩
  let e₀ := hF.toOpenPartialHomeomorph F hF' (by simp)
  let e := e₀.restrOpen V hV
  let W := e.source ∩ (U ×ˢ univ)
  have he : (e : E₃ × ℝ → E₃ × ℝ) = F := rfl
  refine ⟨W, e.open_source.inter (hU.prod isOpen_univ),
    ⟨⟨hF.mem_toOpenPartialHomeomorph_source hF' (by simp), hpV⟩, hpU, mem_univ _⟩,
      ?_, ?_, ?_⟩
  · intro q hq r hs hqr
    apply e.injOn hq.2.1 hs.2.1
    rw [he]
    apply Prod.ext hqr
    have hqφ : φ q.1 = 0 := (hz ▸ (show q.1 ∈ S ∩ U from ⟨hq.1.1, hq.2.2.1⟩)).2
    have hrφ : φ r.1 = 0 := (hz ▸ (show r.1 ∈ S ∩ U from ⟨hs.1.1, hs.2.2.1⟩)).2
    exact hqφ.trans hrφ.symm
  · intro V hV hVW
    have heV := e.isOpen_image_of_subset_source hV (fun q hq => (hVW hq).1)
    have himage : normalCoordinateMap n '' ((S ×ˢ univ) ∩ V) =
        (fun y : E₃ => (y, (0 : ℝ))) ⁻¹' (e '' V) := by
      ext y
      constructor
      · rintro ⟨q, ⟨hqS, hqV⟩, rfl⟩
        refine ⟨q, hqV, ?_⟩
        rw [he]
        apply Prod.ext
        · rfl
        exact (hz ▸ (show q.1 ∈ S ∩ U from ⟨hqS.1, (hVW hqV).2.1⟩)).2
      · rintro ⟨q, hqV, heq⟩
        rw [he] at heq
        have hqφ : φ q.1 = 0 := congrArg Prod.snd heq
        have hqS : q.1 ∈ S :=
          ((congrArg (fun A : Set E₃ => q.1 ∈ A) hz).mpr ⟨(hVW hqV).2.1, hqφ⟩).1
        exact ⟨q, ⟨⟨hqS, mem_univ _⟩, hqV⟩, congrArg Prod.fst heq⟩
    rw [himage]
    exact heV.preimage (continuous_id.prodMk continuous_const)
  · refine ⟨fun y => e.symm (y, 0), ?_, ?_⟩
    · intro y hy
      obtain ⟨q, hq, rfl⟩ := hy
      have hqφ : φ q.1 = 0 := (hz ▸ (show q.1 ∈ S ∩ U from ⟨hq.1.1, hq.2.2.1⟩)).2
      have htarget : (normalCoordinateMap n q, (0 : ℝ)) ∈ e.target := by
        have ht := e.map_source hq.2.1
        simpa only [he, F, hqφ] using ht
      have hsource := e.map_target htarget
      have hqO : e.symm (normalCoordinateMap n q, 0) ∈ O := hsource.2.1
      obtain ⟨e', he'⟩ := hsource.2.2
      have hcF := hFO.contDiffAt (hO.mem_nhds hqO)
      have hdF : HasFDerivAt F e'.toContinuousLinearMap
          (e.symm (normalCoordinateMap n q, 0)) := by
        rw [he']
        exact (hcF.differentiableAt (by simp)).hasFDerivAt
      have hi := e.contDiffAt_symm htarget (he ▸ hdF) (he ▸ hcF)
      have hpair : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : E₃ => (z, (0 : ℝ)))
          (normalCoordinateMap n q) := contDiffAt_id.prodMk contDiffAt_const
      have hcomp : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : E₃ => e.symm (z, 0))
          (normalCoordinateMap n q) :=
        hi.comp (f := fun z : E₃ => (z, (0 : ℝ))) (normalCoordinateMap n q) hpair
      exact hcomp.contDiffWithinAt
    · intro q hq
      have hqφ : φ q.1 = 0 := (hz ▸ (show q.1 ∈ S ∩ U from ⟨hq.1.1, hq.2.2.1⟩)).2
      have hi := e.left_inv hq.2.1
      simpa only [he, F, hqφ] using hi

/-- Compactness upgrades local normal-coordinate injectivity to a uniform width. -/
theorem exists_injOn_normalCoordinateMap {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n) :
    ∃ ε > 0, InjOn (normalCoordinateMap n) (S ×ˢ Ioo (-ε) ε) := by
  classical
  by_contra h
  simp only [InjOn] at h
  push Not at h
  choose a ha b hb he hne using fun k : ℕ => h (1 / ((k : ℝ) + 1)) (by positivity)
  have hta : Tendsto (fun k => (a k).2) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact (abs_lt.mpr (ha k).2).le
  have htb : Tendsto (fun k => (b k).2) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact (abs_lt.mpr (hb k).2).le
  obtain ⟨v, hv, k, hk, hbase⟩ := (hc.prod hc).tendsto_subseq
    (fun j => show ((a j).1, (b j).1) ∈ S ×ˢ S from ⟨(ha j).1, (hb j).1⟩)
  have hpa : Tendsto (fun j => (a (k j)).1) atTop (𝓝 v.1) :=
    (continuous_fst.tendsto v).comp hbase
  have hpb : Tendsto (fun j => (b (k j)).1) atTop (𝓝 v.2) :=
    (continuous_snd.tendsto v).comp hbase
  have hta' := hta.comp hk.tendsto_atTop
  have htb' := htb.comp hk.tendsto_atTop
  have hθa : Tendsto (fun j => normalCoordinateMap n (a (k j))) atTop (𝓝 v.1) := by
    simpa [normalCoordinateMap] using hpa.add
      (hta'.smul ((hn.contDiffAt hv.1).continuousAt.tendsto.comp hpa))
  have hθb : Tendsto (fun j => normalCoordinateMap n (b (k j))) atTop (𝓝 v.2) := by
    simpa [normalCoordinateMap] using hpb.add
      (htb'.smul ((hn.contDiffAt hv.2).continuousAt.tendsto.comp hpb))
  have hvEq : v.1 = v.2 := tendsto_nhds_unique hθa
    (hθb.congr (fun j => (he (k j)).symm))
  obtain ⟨W, hW, hpW, hinj, _⟩ := exists_normalCoordinate_neighbourhood hS hn hv.1
  have hA : ∀ᶠ j in atTop, a (k j) ∈ W :=
    (hpa.prodMk_nhds hta').eventually (hW.mem_nhds hpW)
  have hB : ∀ᶠ j in atTop, b (k j) ∈ W := by
    apply (hpb.prodMk_nhds htb').eventually
    rw [← hvEq]
    exact hW.mem_nhds hpW
  obtain ⟨j, hjA, hjB⟩ := (hA.and hB).exists
  exact hne (k j) (hinj ⟨⟨(ha (k j)).1, mem_univ _⟩, hjA⟩
    ⟨⟨(hb (k j)).1, mem_univ _⟩, hjB⟩ (he (k j)))

/-- All sufficiently thin normal-coordinate images are open. -/
theorem exists_isOpen_normalTube {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε ≤ δ → IsOpen (normalTube S n ε) := by
  classical
  choose W hW hpW hinj hopen hinverse using
    fun p : S => exists_normalCoordinate_neighbourhood hS hn p.property
  obtain ⟨U, V, _, hV, hSU, h0V, hUV⟩ := generalized_tube_lemma hc
    (isCompact_singleton (x := (0 : ℝ))) (isOpen_iUnion hW)
      (by
        rintro ⟨p, t⟩ ⟨hp, ht⟩
        obtain rfl : t = 0 := ht
        exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpW ⟨p, hp⟩⟩)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton 0)))
  refine ⟨δ, hδ, ?_⟩
  intro ε _ hεδ
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨q, hq, rfl⟩
  have hqV : q.2 ∈ V := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact (abs_lt.mpr hq.2).trans_le hεδ
  obtain ⟨p, hqp⟩ := mem_iUnion.mp (hUV ⟨hSU hq.1, hqV⟩)
  let A := W p ∩ (univ ×ˢ Ioo (-ε) ε)
  have hA : IsOpen A := (hW p).inter (isOpen_univ.prod isOpen_Ioo)
  have hqA : q ∈ A := ⟨hqp, mem_univ _, hq.2⟩
  have hsmall : normalCoordinateMap n '' ((S ×ˢ univ) ∩ A) ⊆ normalTube S n ε := by
    rintro z ⟨r, hr, rfl⟩
    exact ⟨r, ⟨hr.1.1, hr.2.2.2⟩, rfl⟩
  exact Filter.mem_of_superset ((hopen p A hA inter_subset_left).mem_nhds
    ⟨q, ⟨⟨hq.1, mem_univ _⟩, hqA⟩, rfl⟩) hsmall

/-- The injectivity and open-neighbourhood clauses of the tubular theorem. -/
theorem tubular_neighbourhood_open {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n) :
    ∃ ε > 0, InjOn (normalCoordinateMap n) (S ×ˢ Ioo (-ε) ε) ∧
      IsOpen (normalTube S n ε) ∧ S ⊆ normalTube S n ε := by
  obtain ⟨ε, hε, hi⟩ := exists_injOn_normalCoordinateMap hS hc hn
  obtain ⟨δ, hδ, ho⟩ := exists_isOpen_normalTube hS hc hn
  refine ⟨min ε δ, lt_min hε hδ, hi.mono ?_, ho _ (lt_min hε hδ) (min_le_right _ _),
    subset_normalTube (lt_min hε hδ)⟩
  exact prod_mono_right (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _))

/-- A compact smooth embedded surface with a smooth unit normal has a uniform
tubular neighbourhood, with smooth inverse projection and signed distance. -/
theorem tubular_neighbourhood {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n) :
    ∃ ε > 0, InjOn (normalCoordinateMap n) (S ×ˢ Ioo (-ε) ε) ∧
      IsOpen (normalTube S n ε) ∧ S ⊆ normalTube S n ε ∧
      ∃ (proj : E₃ → E₃) (dist : E₃ → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) proj (normalTube S n ε) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) dist (normalTube S n ε) ∧
        ∀ p ∈ S, ∀ t ∈ Ioo (-ε) ε,
          proj (p + t • n p) = p ∧ dist (p + t • n p) = t := by
  classical
  obtain ⟨ε₀, hε₀, hi₀⟩ := exists_injOn_normalCoordinateMap hS hc hn
  choose W hW hpW hinj hopen g hg hgleft using
    fun p : S => exists_normalCoordinate_neighbourhood hS hn p.property
  obtain ⟨U, V, _, hV, hSU, h0V, hUV⟩ := generalized_tube_lemma hc
    (isCompact_singleton (x := (0 : ℝ))) (isOpen_iUnion hW)
      (by
        rintro ⟨p, t⟩ ⟨hp, ht⟩
        obtain rfl : t = 0 := ht
        exact mem_iUnion.mpr ⟨⟨p, hp⟩, hpW ⟨p, hp⟩⟩)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton 0)))
  let ε := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have hi : InjOn (normalCoordinateMap n) (S ×ˢ Ioo (-ε) ε) :=
    hi₀.mono (prod_mono_right (Ioo_subset_Ioo
      (neg_le_neg (min_le_left _ _)) (min_le_left _ _)))
  let G := invFunOn (normalCoordinateMap n) (S ×ˢ Ioo (-ε) ε)
  have hGleft : ∀ q ∈ S ×ˢ Ioo (-ε) ε, G (normalCoordinateMap n q) = q :=
    hi.leftInvOn_invFunOn
  have hlocal : ∀ y ∈ normalTube S n ε,
      ∃ A : Set E₃, IsOpen A ∧ y ∈ A ∧ A ⊆ normalTube S n ε ∧
        ContDiffOn ℝ (⊤ : ℕ∞) G A := by
    rintro y ⟨q, hq, rfl⟩
    have hqV : q.2 ∈ V := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      exact (abs_lt.mpr hq.2).trans_le (min_le_right _ _)
    obtain ⟨p, hqp⟩ := mem_iUnion.mp (hUV ⟨hSU hq.1, hqV⟩)
    let B := W p ∩ (univ ×ˢ Ioo (-ε) ε)
    let A := normalCoordinateMap n '' ((S ×ˢ univ) ∩ B)
    have hB : IsOpen B := (hW p).inter (isOpen_univ.prod isOpen_Ioo)
    have hA : IsOpen A := hopen p B hB inter_subset_left
    have hAT : A ⊆ normalTube S n ε := by
      rintro z ⟨r, hr, rfl⟩
      exact ⟨r, ⟨hr.1.1, hr.2.2.2⟩, rfl⟩
    refine ⟨A, hA, ⟨q, ⟨⟨hq.1, mem_univ _⟩, hqp, mem_univ _, hq.2⟩, rfl⟩, hAT, ?_⟩
    apply (hg p).mono (image_mono (inter_subset_inter_right _ inter_subset_left)) |>.congr
    rintro z ⟨r, hr, rfl⟩
    exact (hGleft r ⟨hr.1.1, hr.2.2.2⟩).trans (hgleft p r ⟨hr.1, hr.2.1⟩).symm
  have ho : IsOpen (normalTube S n ε) := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨A, hA, hyA, hAT, _⟩ := hlocal y hy
    exact Filter.mem_of_superset (hA.mem_nhds hyA) hAT
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G (normalTube S n ε) := by
    intro y hy
    obtain ⟨A, hA, hyA, _, hGA⟩ := hlocal y hy
    exact (hGA.contDiffAt (hA.mem_nhds hyA)).contDiffWithinAt
  refine ⟨ε, hε, hi, ho, subset_normalTube hε,
    (fun y => (G y).1), (fun y => (G y).2), hG.fst, hG.snd, ?_⟩
  intro p hp t ht
  have hh := hGleft (p, t) ⟨hp, ht⟩
  exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩

end LiquidDrop
