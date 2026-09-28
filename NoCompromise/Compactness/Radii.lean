import NoCompromise.BV.GoodRadii
import NoCompromise.BV.SphericalSlicing

/-!
# Construction of the cutting radii

Blueprint `lem:radii-construction` (chapter 19). Given sets `E n` converging
locally in `L¹` to a finite-volume set `F`, we choose integer shells
`(k j, k j + 1)`, block thresholds `N j`, and good radii `R n` in the shells so
that the spherical sections and the symmetric differences of the cut sets are
quantitatively small.

Lean indexing: the blueprint's block index `j = 1, 2, …` becomes `j = 0, 1, …`,
so the blueprint bound `2^{1-j}` becomes `(2⁻¹)^j`. The initial terms `n < N 0`
(discarded in the blueprint) carry only a good radius in `(k 0, k 0 + 1)`.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
namespace LiquidDrop

/-- On a measurable set `K`, the `L¹` distance of two indicators is the volume
of the symmetric difference inside `K`. -/
theorem setIntegral_abs_indicator_sub_eq_inter (A B K : Set AmbientSpace)
    (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume)
    (hK : MeasurableSet K) :
    (∫ x in K, |A.indicator (fun _ => (1 : ℝ)) x - B.indicator (fun _ => (1 : ℝ)) x|) =
      volume.real (symmDiff A B ∩ K) := by
  calc
    _ = ∫ x in K, (symmDiff A B).indicator (fun _ => (1 : ℝ)) x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB, mem_symmDiff]
    _ = _ := by
      rw [integral_indicator₀ ((hA.symmDiff hB).mono Measure.restrict_le_self),
        setIntegral_const, smul_eq_mul, mul_one, measureReal_def, measureReal_def,
        Measure.restrict_apply' hK]

/-- Local `L¹` convergence of indicators gives convergence to zero of the
symmetric-difference volume in every ball. -/
theorem tendsto_volume_symmDiff_inter_ball
    (E : ℕ → Set AmbientSpace) (F : Set AmbientSpace)
    (hmE : ∀ n, NullMeasurableSet (E n) volume) (hmF : NullMeasurableSet F volume)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun n => ∫ x in K,
        |(E n).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0))
    (ρ : ℝ) :
    Tendsto (fun n => volume (symmDiff (E n) F ∩ ball 0 ρ)) atTop (𝓝 0) := by
  have hK : IsCompact (closedBall (0 : AmbientSpace) ρ) := isCompact_closedBall 0 ρ
  have hfin : ∀ n, volume (symmDiff (E n) F ∩ closedBall 0 ρ) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono inter_subset_right)
  have hreal := hconv _ hK
  simp only [setIntegral_abs_indicator_sub_eq_inter _ _ _ (hmE _) hmF hK.isClosed.measurableSet,
    measureReal_def] at hreal
  have hclosed : Tendsto (fun n => volume (symmDiff (E n) F ∩ closedBall 0 ρ)) atTop (𝓝 0) := by
    rw [← ENNReal.tendsto_toReal_iff hfin ENNReal.zero_ne_top]
    simpa using hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hclosed
    (fun _ => zero_le) (fun n => measure_mono (inter_subset_inter_right _ ball_subset_closedBall))

/-- The tails of a finite-volume set outside large balls have vanishing volume. -/
theorem tendsto_volume_diff_ball (F : Set AmbientSpace) (hmF : NullMeasurableSet F volume)
    (hFfin : volume F ≠ ∞) :
    Tendsto (fun m : ℕ => volume (F \ ball (0 : AmbientSpace) m)) atTop (𝓝 0) := by
  have hanti : Antitone (fun m : ℕ => F \ ball (0 : AmbientSpace) m) := by
    intro a b hab
    exact sdiff_subset_sdiff_right (ball_subset_ball (by exact_mod_cast hab))
  have h := tendsto_measure_iInter_atTop (μ := volume)
    (fun m : ℕ => hmF.diff measurableSet_ball.nullMeasurableSet) hanti
    ⟨0, ne_top_of_le_ne_top hFfin (measure_mono sdiff_subset)⟩
  have hempty : (⋂ m : ℕ, F \ ball (0 : AmbientSpace) m) = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
    exact (mem_iInter.1 hx m).2 (mem_ball.2 (by rwa [dist_zero_right]))
  rwa [hempty, measure_empty] at h

/-- In a unit shell `(a, a + 1)` with `0 ≤ a`, there is a good radius whose
density-one spherical section has area at most the volume of the shell part. -/
theorem exists_goodRadius_le (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {a : ℝ} (ha : 0 ≤ a) :
    ∃ r ∈ Ioo a (a + 1), IsGoodRadius E hE hmE 0 r ∧
      hausdorffMeasure2 3 (densityOne E ∩ sphere 0 r) ≤
        volume (E ∩ (ball (0 : AmbientSpace) (a + 1) \ ball 0 a)) := by
  set c := volume (E ∩ (ball (0 : AmbientSpace) (a + 1) \ ball 0 a)) with hc
  have hcfin : c ≠ ∞ := ne_top_of_le_ne_top measure_ball_lt_top.ne
    (measure_mono (inter_subset_right.trans sdiff_subset))
  by_contra hcon
  push Not at hcon
  have hgood := ae_isGoodRadius E hE hmE 0
  rw [ae_restrict_iff' measurableSet_Ioi] at hgood
  have hlt : ∀ᵐ r ∂volume, r ∈ Ioo a (a + 1) →
      c < hausdorffMeasure2 3 (densityOne E ∩ sphere 0 r) := by
    filter_upwards [hgood] with r hr hrI
    exact hcon r hrI (hr (lt_of_le_of_lt ha hrI.1))
  have hvol : volume (Ioo a (a + 1)) = 1 := by simp [Real.volume_Ioo]
  have hstrict := setLIntegral_strict_mono (μ := volume) (f := fun _ => c)
    (g := fun r => hausdorffMeasure2 3 (densityOne E ∩ sphere 0 r)) measurableSet_Ioo
    (by rw [hvol]; exact one_ne_zero)
    (measurable_sphere_sections (measurableSet_densityOne hmE) 0)
    (by simp only [setLIntegral_const, hvol, mul_one]; exact hcfin) hlt
  simp only [setLIntegral_const, hvol, mul_one] at hstrict
  rw [spherical_slicing hmE 0 ha] at hstrict
  exact lt_irrefl _ hstrict

lemma inv_two_pow_succ_add (j : ℕ) :
    (2⁻¹ : ℝ≥0∞) ^ (j + 1) + (2⁻¹ : ℝ≥0∞) ^ (j + 1) = (2⁻¹ : ℝ≥0∞) ^ j := by
  rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

/-- Shell estimate: the part of `E` in the shell `B_{b} \ B_{a}` is controlled by
the tail of `F` and the symmetric difference in `B_{b}`. -/
lemma volume_inter_shell_le (E F : Set AmbientSpace) (a b : ℝ) :
    volume (E ∩ (ball (0 : AmbientSpace) b \ ball 0 a)) ≤
      volume (F \ ball 0 a) + volume (symmDiff E F ∩ ball 0 b) := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  rintro x ⟨hxE, hxb, hxa⟩
  by_cases hxF : x ∈ F
  · exact Or.inl ⟨hxF, hxa⟩
  · exact Or.inr ⟨mem_symmDiff.2 (Or.inl ⟨hxE, hxF⟩), hxb⟩

/-- Symmetric-difference estimate for the inner cut at a radius `a < R < b`. -/
lemma volume_symmDiff_cut_le (E F : Set AmbientSpace) {a b R : ℝ} (haR : a < R)
    (hRb : R < b) :
    volume (symmDiff (E ∩ ball (0 : AmbientSpace) R) F) ≤
      volume (symmDiff E F ∩ ball 0 b) + volume (F \ ball 0 a) := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  have hRb' : ball (0 : AmbientSpace) R ⊆ ball 0 b := ball_subset_ball hRb.le
  have haR' : ball (0 : AmbientSpace) a ⊆ ball 0 R := ball_subset_ball haR.le
  intro x hx
  rcases mem_symmDiff.1 hx with ⟨⟨hxE, hxR⟩, hxF⟩ | ⟨hxF, hxn⟩
  · exact Or.inl ⟨mem_symmDiff.2 (Or.inl ⟨hxE, hxF⟩), hRb' hxR⟩
  · by_cases hxR : x ∈ ball (0 : AmbientSpace) R
    · have hxE : x ∉ E := fun hxE => hxn ⟨hxE, hxR⟩
      exact Or.inl ⟨mem_symmDiff.2 (Or.inr ⟨hxF, hxE⟩), hRb' hxR⟩
    · exact Or.inr ⟨hxF, fun hxa => hxR (haR' hxa)⟩

/-- The block index of `n` for a strictly increasing threshold sequence `N`:
the least `j` with `n < N (j + 1)`. -/
def blockIndex {N : ℕ → ℕ} (hN : StrictMono N) (n : ℕ) : ℕ :=
  Nat.find (⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (hN.id_le (n + 1))⟩ :
    ∃ j, n < N (j + 1))

lemma lt_blockIndex_succ {N : ℕ → ℕ} (hN : StrictMono N) (n : ℕ) :
    n < N (blockIndex hN n + 1) :=
  Nat.find_spec (⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (hN.id_le (n + 1))⟩ :
    ∃ j, n < N (j + 1))

lemma blockIndex_le {N : ℕ → ℕ} (hN : StrictMono N) {j n : ℕ} (hn : n < N (j + 1)) :
    blockIndex hN n ≤ j :=
  Nat.find_min' _ hn

lemma le_blockIndex {N : ℕ → ℕ} (hN : StrictMono N) {j n : ℕ} (hn : N j ≤ n) :
    j ≤ blockIndex hN n := by
  by_contra h
  push Not at h
  have h1 := lt_blockIndex_succ hN n
  have h2 : N (blockIndex hN n + 1) ≤ N j := hN.monotone h
  omega

lemma blockIndex_eq {N : ℕ → ℕ} (hN : StrictMono N) {j n : ℕ} (h1 : N j ≤ n)
    (h2 : n < N (j + 1)) : blockIndex hN n = j :=
  le_antisymm (blockIndex_le hN h2) (le_blockIndex hN h1)

lemma le_of_blockIndex {N : ℕ → ℕ} (hN : StrictMono N) {n : ℕ} (hn : N 0 ≤ n) :
    N (blockIndex hN n) ≤ n := by
  rcases h : blockIndex hN n with _ | i
  · exact hn
  · by_contra hlt
    push Not at hlt
    have := blockIndex_le hN hlt
    omega

lemma tendsto_blockIndex {N : ℕ → ℕ} (hN : StrictMono N) :
    Tendsto (blockIndex hN) atTop atTop :=
  tendsto_atTop.2 fun j => eventually_atTop.2 ⟨N j, fun _ hn => le_blockIndex hN hn⟩

/-- Blueprint `lem:radii-construction`. -/
theorem radii_construction
    (E : ℕ → Set AmbientSpace) (F : Set AmbientSpace)
    (hE : ∀ n, HasLocallyFinitePerimeter (E n)) (hmE : ∀ n, NullMeasurableSet (E n) volume)
    (hmF : NullMeasurableSet F volume) (hFfin : volume F ≠ ∞)
    (hconv : ∀ K : Set AmbientSpace, IsCompact K →
      Tendsto (fun n => ∫ x in K,
        |(E n).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    ∃ (N k : ℕ → ℕ) (R : ℕ → ℝ), StrictMono N ∧ StrictMono k ∧
      (∀ n, IsGoodRadius (E n) (hE n) (hmE n) 0 (R n)) ∧
      (∀ n, n < N 0 → R n ∈ Ioo (k 0 : ℝ) (k 0 + 1)) ∧
      (∀ j n, N j ≤ n → n < N (j + 1) →
        R n ∈ Ioo (k j : ℝ) (k j + 1) ∧
        hausdorffMeasure2 3 (densityOne (E n) ∩ sphere 0 (R n)) ≤ (2⁻¹ : ℝ≥0∞) ^ j ∧
        volume (symmDiff (E n ∩ ball 0 (R n)) F) ≤ (2⁻¹ : ℝ≥0∞) ^ j) ∧
      Tendsto R atTop atTop ∧
      Tendsto (fun n => hausdorffMeasure2 3 (densityOne (E n) ∩ sphere 0 (R n))) atTop (𝓝 0) ∧
      Tendsto (fun n => volume (symmDiff (E n ∩ ball 0 (R n)) F)) atTop (𝓝 0) ∧
      Tendsto (fun n => volume (E n ∩ ball 0 (R n))) atTop (𝓝 (volume F)) ∧
      (∀ K : Set AmbientSpace, IsCompact K →
        Tendsto (fun n => ∫ x in K, (E n \ ball 0 (R n)).indicator (fun _ => (1 : ℝ)) x)
          atTop (𝓝 0)) := by
  have hpos : ∀ j : ℕ, (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ (j + 1) := fun j =>
    ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _
  -- Step 1: the shells.
  obtain ⟨k, hk, hkF⟩ := Filter.extraction_forall_of_eventually
    (P := fun j m => volume (F \ ball (0 : AmbientSpace) m) ≤ (2⁻¹ : ℝ≥0∞) ^ (j + 1))
    (fun j => (ENNReal.tendsto_nhds_zero.1 (tendsto_volume_diff_ball F hmF hFfin)) _ (hpos j))
  -- Step 2: the thresholds.
  obtain ⟨N, hN, hNE⟩ := Filter.extraction_forall_of_eventually
    (P := fun j m => ∀ n, m ≤ n →
      volume (symmDiff (E n) F ∩ ball 0 ((k j : ℝ) + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ (j + 1))
    (fun j => Filter.eventually_forall_ge_atTop.2 ((ENNReal.tendsto_nhds_zero.1
      (tendsto_volume_symmDiff_inter_ball E F hmE hmF hconv ((k j : ℝ) + 1))) _ (hpos j)))
  -- Step 3: the radii.
  have hrad := fun (j n : ℕ) =>
    exists_goodRadius_le (E n) (hE n) (hmE n) (a := (k j : ℝ)) (Nat.cast_nonneg _)
  choose rad hradI hradG hradH using hrad
  set blk := blockIndex hN with hblk
  let R : ℕ → ℝ := fun n => rad (blk n) n
  -- Quantitative estimates on each block.
  have hblock : ∀ j n, N j ≤ n → n < N (j + 1) →
      R n ∈ Ioo (k j : ℝ) (k j + 1) ∧
      hausdorffMeasure2 3 (densityOne (E n) ∩ sphere 0 (R n)) ≤ (2⁻¹ : ℝ≥0∞) ^ j ∧
      volume (symmDiff (E n ∩ ball 0 (R n)) F) ≤ (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j n h1 h2
    have hb : blk n = j := blockIndex_eq hN h1 h2
    have hRn : R n = rad j n := by change rad (blk n) n = rad j n; rw [hb]
    have hI := hradI j n
    rw [hRn]
    refine ⟨hI, ?_, ?_⟩
    · calc
        _ ≤ _ := hradH j n
        _ ≤ volume (F \ ball 0 (k j : ℝ)) +
            volume (symmDiff (E n) F ∩ ball 0 ((k j : ℝ) + 1)) := volume_inter_shell_le _ _ _ _
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ (j + 1) + (2⁻¹ : ℝ≥0∞) ^ (j + 1) :=
            add_le_add (hkF j) (hNE j n h1)
        _ = _ := inv_two_pow_succ_add j
    · calc
        _ ≤ volume (symmDiff (E n) F ∩ ball 0 ((k j : ℝ) + 1)) +
            volume (F \ ball 0 (k j : ℝ)) := volume_symmDiff_cut_le _ _ hI.1 hI.2
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ (j + 1) + (2⁻¹ : ℝ≥0∞) ^ (j + 1) :=
            add_le_add (hNE j n h1) (hkF j)
        _ = _ := inv_two_pow_succ_add j
  -- Eventual bounds by the block index.
  have hev : ∀ᶠ n in atTop,
      hausdorffMeasure2 3 (densityOne (E n) ∩ sphere 0 (R n)) ≤ (2⁻¹ : ℝ≥0∞) ^ blk n ∧
      volume (symmDiff (E n ∩ ball 0 (R n)) F) ≤ (2⁻¹ : ℝ≥0∞) ^ blk n := by
    filter_upwards [eventually_ge_atTop (N 0)] with n hn
    have h1 : N (blk n) ≤ n := le_of_blockIndex hN hn
    have hb := hblock (blk n) n h1 (lt_blockIndex_succ hN n)
    exact ⟨hb.2.1, hb.2.2⟩
  have hpow : Tendsto (fun n => (2⁻¹ : ℝ≥0∞) ^ blk n) atTop (𝓝 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)).comp
      (tendsto_blockIndex hN)
  have hH : Tendsto (fun n => hausdorffMeasure2 3 (densityOne (E n) ∩ sphere 0 (R n)))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow
      (Eventually.of_forall fun _ => zero_le) (hev.mono fun _ h => h.1)
  have hD : Tendsto (fun n => volume (symmDiff (E n ∩ ball 0 (R n)) F)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow
      (Eventually.of_forall fun _ => zero_le) (hev.mono fun _ h => h.2)
  have hR : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop.comp (tendsto_blockIndex hN))
    have h1 : ((blk n : ℕ) : ℝ) ≤ k (blk n) := by exact_mod_cast hk.id_le (blk n)
    exact h1.trans (hradI (blk n) n).1.le
  refine ⟨N, k, R, hN, hk, fun n => hradG (blk n) n, fun n hn => ?_, hblock, hR, hH, hD,
    ?_, ?_⟩
  · have hb : blk n = 0 := Nat.le_zero.1 (blockIndex_le hN (hn.trans (hN (Nat.lt_succ_self 0))))
    change rad (blk n) n ∈ _
    rw [hb]
    exact hradI 0 n
  · -- Volumes of the inner cuts.
    have hup : ∀ n, volume (E n ∩ ball 0 (R n)) ≤
        volume F + volume (symmDiff (E n ∩ ball 0 (R n)) F) := fun n => by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro x hx
      by_cases hxF : x ∈ F
      · exact Or.inl hxF
      · exact Or.inr (mem_symmDiff.2 (Or.inl ⟨hx, hxF⟩))
    have hlow : ∀ n, volume F - volume (symmDiff (E n ∩ ball 0 (R n)) F) ≤
        volume (E n ∩ ball 0 (R n)) := fun n => by
      rw [tsub_le_iff_right]
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro x hx
      by_cases hxE : x ∈ E n ∩ ball 0 (R n)
      · exact Or.inl hxE
      · exact Or.inr (mem_symmDiff.2 (Or.inr ⟨hx, hxE⟩))
    have hU : Tendsto (fun n => volume F + volume (symmDiff (E n ∩ ball 0 (R n)) F)) atTop
        (𝓝 (volume F)) := by
      simpa using (tendsto_const_nhds (x := volume F)).add hD
    have hL : Tendsto (fun n => volume F - volume (symmDiff (E n ∩ ball 0 (R n)) F)) atTop
        (𝓝 (volume F)) := by
      simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := volume F)) hD (Or.inl hFfin)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hL hU hlow hup
  · -- Local convergence of the outer remainders.
    intro K hK
    obtain ⟨M, hM⟩ := (isBounded_iff_subset_ball (0 : AmbientSpace)).1 hK.isBounded
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_atTop.1 hR M] with n hn
    symm
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply indicator_of_notMem
    rintro ⟨_, hxn⟩
    exact hxn (ball_subset_ball hn (hM hx))

end LiquidDrop
