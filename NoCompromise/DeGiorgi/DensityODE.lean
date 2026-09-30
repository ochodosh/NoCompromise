module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

/-!
# A cubic lower barrier for radial density functions

The real-analysis argument uses absolute continuity on positive-radius compact
intervals. The cube-root chain rule is derived from local Lipschitz regularity,
and a negative minimum contradicts the resulting strict increase below the barrier.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- A continuous function starting at zero cannot decrease below zero if it increases
strictly on every positive-radius interval where it is negative. -/
lemma nonneg_of_strict_increase_on_negative_intervals {g : ℝ → ℝ} {R : ℝ}
    (hg : ContinuousOn g (Icc 0 R)) (hg0 : g 0 = 0)
    (hinc : ∀ a d : ℝ, 0 < a → a < d → d ≤ R →
      (∀ s ∈ Icc a d, g s < 0) → g a < g d) :
    ∀ r ∈ Icc 0 R, 0 ≤ g r := by
  intro r hr
  by_contra hneg
  have hgr : g r < 0 := lt_of_not_ge hneg
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc 0 r).Nonempty from ⟨0, ⟨le_rfl, hr.1⟩⟩)
    (hg.mono (Icc_subset_Icc le_rfl hr.2))
  have hgt : g t < 0 := (hmin ⟨hr.1, le_rfl⟩).trans_lt hgr
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by intro h; subst t; simp [hg0] at hgt)
  have htR : t ≤ R := ht.2.trans hr.2
  have hn : {s : ℝ | g s < 0} ∈ 𝓝[Icc 0 R] t :=
    (hg t ⟨ht.1, htR⟩).eventually (gt_mem_nhds hgt)
  obtain ⟨η, hη, hηg⟩ := Metric.mem_nhdsWithin_iff.mp hn
  let e := min (t / 2) (η / 2)
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have het : e ≤ t / 2 := min_le_left _ _
  have heη : e < η := (min_le_right _ _).trans_lt (by linarith)
  have ha0 : 0 < t - e := by linarith
  have hat : t - e < t := by linarith
  have hgneg (s : ℝ) (hs : s ∈ Icc (t - e) t) : g s < 0 := by
    apply hηg
    refine ⟨?_, ⟨by linarith [hs.1], hs.2.trans htR⟩⟩
    rw [mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith [hs.1]
  have hlt := hinc (t - e) t ha0 hat htR hgneg
  have hge : g t ≤ g (t - e) :=
    hmin (show t - e ∈ Icc 0 r from ⟨ha0.le, hat.le.trans ht.2⟩)
  linarith

/-- A positive Lipschitz function has a Lipschitz cube root on each compact interval. -/
lemma exists_lipschitzOnWith_cubic_root {f : ℝ → ℝ} {a d : ℝ} {L : ℝ≥0}
    (had : a ≤ d) (hf : LipschitzOnWith L f (Icc a d))
    (hpos : ∀ s ∈ Icc a d, 0 < f s) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun s => f s ^ (1 / 3 : ℝ)) (Icc a d) := by
  have hne : (Icc a d).Nonempty := ⟨a, ⟨le_rfl, had⟩⟩
  obtain ⟨p, hp, hpmin⟩ := isCompact_Icc.exists_isMinOn hne hf.continuousOn
  obtain ⟨q, hq, hqmax⟩ := isCompact_Icc.exists_isMaxOn hne hf.continuousOn
  have hcd : ContDiffOn ℝ 1 (fun u : ℝ => u ^ (1 / 3 : ℝ)) (Icc (f p) (f q)) :=
    contDiffOn_id.rpow_const_of_ne fun u hu => ne_of_gt ((hpos p hp).trans_le hu.1)
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact ⟨K * L, hK.comp hf (fun s hs => ⟨hpmin hs, hqmax hs⟩)⟩

lemma cubic_root_cube {u : ℝ} (hu : 0 ≤ u) : (u ^ (1 / 3 : ℝ)) ^ 3 = u := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
  norm_num

/-- The cube-root barrier cannot be crossed under the original derivative inequality. -/
theorem cubic_lower_barrier_of_slope {f : ℝ → ℝ} {R b c k : ℝ}
    (hc : 0 < c) (hk : 0 < k) (hkb : k ^ 3 ≤ b) (hkc : k ≤ c / 6)
    (hf : ContinuousOn f (Icc 0 R)) (hf0 : f 0 = 0)
    (hpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (hlip : ∀ a d : ℝ, 0 < a → a ≤ d → d ≤ R →
      ∃ L : ℝ≥0, LipschitzOnWith L f (Icc a d))
    (hderiv : ∀ᵐ r : ℝ, r ∈ Ioo 0 R → f r ≤ b * r ^ 3 →
      c * f r ^ (2 / 3 : ℝ) ≤ deriv f r) :
    ∀ r ∈ Icc 0 R, k ^ 3 * r ^ 3 ≤ f r := by
  let g (r : ℝ) := f r ^ (1 / 3 : ℝ) - k * r
  have hgc : ContinuousOn g (Icc 0 R) :=
    (hf.rpow_const (fun _ _ => Or.inr (by norm_num))).sub (by fun_prop)
  have hg0 : g 0 = 0 := by simp [g, hf0]
  have hg : ∀ r ∈ Icc 0 R, 0 ≤ g r := by
    apply nonneg_of_strict_increase_on_negative_intervals hgc hg0
    intro a d ha had hdR hgneg
    obtain ⟨L, hL⟩ := hlip a d ha had.le hdR
    have hfp (s : ℝ) (hs : s ∈ Icc a d) : 0 < f s :=
      hpos s (ha.trans_le hs.1) (hs.2.trans hdR)
    obtain ⟨K, hK⟩ := exists_lipschitzOnWith_cubic_root had.le hL hfp
    have hfAC : AbsolutelyContinuousOnInterval f a d :=
      (show LipschitzOnWith L f (uIcc a d) by
        rwa [uIcc_of_le had.le]).absolutelyContinuousOnInterval
    have hrootAC : AbsolutelyContinuousOnInterval (fun s => f s ^ (1 / 3 : ℝ)) a d :=
      (show LipschitzOnWith K (fun s => f s ^ (1 / 3 : ℝ)) (uIcc a d) by
        rwa [uIcc_of_le had.le]).absolutelyContinuousOnInterval
    have hlinearAC : AbsolutelyContinuousOnInterval (fun s : ℝ => k * s) a d :=
      (show ContDiffOn ℝ 1 (fun s : ℝ => k * s) (uIcc a d) by
        fun_prop).absolutelyContinuousOnInterval
    have hgAC : AbsolutelyContinuousOnInterval g a d := by
      simpa only [g, Pi.sub_def] using hrootAC.sub hlinearAC
    have hnd : ∀ᵐ s : ℝ, s ≠ d := by simp [ae_iff]
    have hgd : (fun _ : ℝ => c / 6) ≤ᵐ[volume.restrict (Icc a d)] deriv g := by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (s := Icc a d) hfAC.ae_differentiableAt,
        ae_restrict_of_ae (s := Icc a d) hderiv,
        ae_restrict_of_ae (s := Icc a d) hnd] with s hs hfs hsde hsd
      have hs0 : 0 < s := ha.trans_le hs.1
      have hsR : s < R := (lt_of_le_of_ne hs.2 hsd).trans_le hdR
      have hfps : 0 < f s := hfp s hs
      have hroot : f s ^ (1 / 3 : ℝ) < k * s := by
        have h := hgneg s hs
        dsimp [g] at h
        linarith
      have hsmall : f s ≤ b * s ^ 3 := by
        calc
          _ = (f s ^ (1 / 3 : ℝ)) ^ 3 := (cubic_root_cube hfps.le).symm
          _ ≤ (k * s) ^ 3 := pow_le_pow_left₀ (Real.rpow_nonneg hfps.le _) hroot.le 3
          _ = k ^ 3 * s ^ 3 := mul_pow _ _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right hkb (by positivity)
      have hpde := hsde ⟨hs0, hsR⟩ hsmall
      have hdf := hfs (by simpa only [uIcc_of_le had.le] using hs)
      have hdg : HasDerivAt g
          (deriv f s * (1 / 3 : ℝ) * f s ^ ((1 / 3 : ℝ) - 1) - k) s := by
        simpa only [g, Pi.sub_def, id_eq, mul_one] using
          (hdf.hasDerivAt.rpow_const (p := (1 / 3 : ℝ)) (Or.inl hfps.ne')).sub
            ((hasDerivAt_id s).const_mul k)
      rw [hdg.deriv]
      have hcancel : f s ^ (2 / 3 : ℝ) * f s ^ ((1 / 3 : ℝ) - 1) = 1 := by
        rw [← Real.rpow_add hfps]
        norm_num
      have hmul := mul_le_mul_of_nonneg_right hpde
        (Real.rpow_nonneg hfps.le ((1 / 3 : ℝ) - 1))
      nlinarith [hcancel]
    have hbound := intervalIntegral.integral_mono_ae_restrict had.le
      intervalIntegrable_const hgAC.intervalIntegrable_deriv hgd
    rw [intervalIntegral.integral_const, hgAC.integral_deriv_eq_sub, smul_eq_mul] at hbound
    have hstrict : 0 < (d - a) * (c / 6) := mul_pos (sub_pos.mpr had) (by positivity)
    linarith
  intro r hr
  have hnonneg : 0 ≤ f r := by
    rcases hr.1.eq_or_lt with hzero | hpositive
    · rw [← hzero, hf0]
    · exact (hpos r hpositive hr.2).le
  have hroot : k * r ≤ f r ^ (1 / 3 : ℝ) := by
    have h := hg r hr
    dsimp [g] at h
    linarith
  calc
    _ = (k * r) ^ 3 := (mul_pow _ _ _).symm
    _ ≤ (f r ^ (1 / 3 : ℝ)) ^ 3 := pow_le_pow_left₀ (mul_nonneg hk.le hr.1) hroot 3
    _ = _ := cubic_root_cube hnonneg

/-- A lower-density constant depending only on the two differential-inequality constants. -/
def densityCubicConstant (b c : ℝ) : ℝ :=
  (min (b ^ (1 / 3 : ℝ)) (c / 6)) ^ 3

lemma densityCubicConstant_pos {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    0 < densityCubicConstant b c := by
  unfold densityCubicConstant
  exact pow_pos (lt_min (Real.rpow_pos_of_pos hb _) (by positivity)) 3

/-- The pure real-analysis density lemma, with no differential conclusion assumed as input. -/
theorem cubic_lower_barrier {f : ℝ → ℝ} {R b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hf : ContinuousOn f (Icc 0 R)) (hf0 : f 0 = 0)
    (hpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (hlip : ∀ a d : ℝ, 0 < a → a ≤ d → d ≤ R →
      ∃ L : ℝ≥0, LipschitzOnWith L f (Icc a d))
    (hderiv : ∀ᵐ r : ℝ, r ∈ Ioo 0 R → f r ≤ b * r ^ 3 →
      c * f r ^ (2 / 3 : ℝ) ≤ deriv f r) :
    ∀ r ∈ Icc 0 R, densityCubicConstant b c * r ^ 3 ≤ f r := by
  unfold densityCubicConstant
  refine cubic_lower_barrier_of_slope hc
    (lt_min (Real.rpow_pos_of_pos hb _) (by positivity)) ?_
    (min_le_right _ _) hf hf0 hpos hlip hderiv
  exact (pow_le_pow_left₀
    (le_of_lt (lt_min (Real.rpow_pos_of_pos hb _) (by positivity)))
    (min_le_left _ _) 3).trans_eq (cubic_root_cube hb.le)

/-- A convenient form for radial-volume functions with one Lipschitz bound on `[0,R]`. -/
theorem cubic_lower_barrier_of_lipschitz {f : ℝ → ℝ} {R b c : ℝ} {L : ℝ≥0}
    (hb : 0 < b) (hc : 0 < c) (hf : LipschitzOnWith L f (Icc 0 R)) (hf0 : f 0 = 0)
    (hpos : ∀ r : ℝ, 0 < r → r ≤ R → 0 < f r)
    (hderiv : ∀ᵐ r : ℝ, r ∈ Ioo 0 R → f r ≤ b * r ^ 3 →
      c * f r ^ (2 / 3 : ℝ) ≤ deriv f r) :
    ∀ r ∈ Icc 0 R, densityCubicConstant b c * r ^ 3 ≤ f r := by
  apply cubic_lower_barrier hb hc hf.continuousOn hf0 hpos _ hderiv
  intro a d ha _ hd
  exact ⟨L, hf.mono (Icc_subset_Icc ha.le hd)⟩

end LiquidDrop
