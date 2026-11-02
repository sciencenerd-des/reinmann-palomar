/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.XiCenterPositive
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# One actual Xi Mellin remainder and all its derivatives

This is a theta Mellin truncation error, not a saddle expansion remainder.
All parameters share the same truncated kernel. The derivative bounds do not
establish the sign of model curvature or an all-rank cumulative budget.
-/
noncomputable section
namespace Reinmann
open Set MeasureTheory HurwitzZeta Filter Asymptotics
open scoped Topology

def thetaMellinCutoff (T : ℝ) : ℝ → ℂ :=
  (Ioi T).indicator (hurwitzEvenFEPair 0).f_modif

theorem thetaMellinCutoff_locallyIntegrable (T : ℝ) :
    LocallyIntegrableOn (thetaMellinCutoff T) (Ioi 0) := by
  intro x hx
  obtain ⟨U, hU, hi⟩ := (hurwitzEvenFEPair 0).hf_modif_int x hx
  exact ⟨U, hU, hi.indicator measurableSet_Ioi⟩

theorem thetaMellinCutoff_top (T a : ℝ) :
    thetaMellinCutoff T =O[atTop] (fun t : ℝ => t ^ a) := by
  have h : (hurwitzEvenFEPair 0).f_modif =O[atTop] (fun t : ℝ => t ^ a) := by
    simpa only [sub_zero] using! (hurwitzEvenFEPair 0).hf_modif_top a
  refine h.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop T] with t ht
  simp [thetaMellinCutoff, ht]

theorem thetaMellinCutoff_zero {T : ℝ} (hT : 0 < T) (a : ℝ) :
    thetaMellinCutoff T =O[𝓝[>] 0] (fun t : ℝ => t ^ a) := by
  refine (isBigO_zero (fun t : ℝ => t ^ a) (𝓝[>] 0)).congr' ?_ (EventuallyEq.refl _ _)
  apply Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_lt_nhds hT] with t ht
  simp [thetaMellinCutoff, not_lt_of_ge ht.le]

theorem differentiable_thetaMellinCutoff {T : ℝ} (hT : 0 < T) :
    Differentiable ℂ (mellin (thetaMellinCutoff T)) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow
    (thetaMellinCutoff_locallyIntegrable T) (thetaMellinCutoff_top T (-(s.re + 1)))
    (by linarith) (thetaMellinCutoff_zero hT (-(s.re - 1))) (by linarith)

theorem thetaUpperMellinRemainder_eq_cutoff {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    thetaUpperMellinRemainder T s = mellin (thetaMellinCutoff T) s := by
  unfold mellin thetaMellinCutoff
  simp only [← indicator_smul]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict_of_subset]
  · unfold thetaUpperMellinRemainder
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have hu : thetaCenterUpper t = (hurwitzEvenFEPair 0).f_modif t := by
      simp [thetaCenterUpper, show 1 < t from hT.trans_lt ht]
    rw [hu]
  · intro t ht
    exact (show 0 ≤ T by linarith).trans_lt ht

theorem differentiable_thetaUpperMellinRemainder {T : ℝ} (hT : 1 ≤ T) :
    Differentiable ℂ (thetaUpperMellinRemainder T) := by
  have he : thetaUpperMellinRemainder T = mellin (thetaMellinCutoff T) :=
    funext (thetaUpperMellinRemainder_eq_cutoff hT)
  rw [he]
  exact differentiable_thetaMellinCutoff (by linarith)

/-- A uniform Cauchy bound for every derivative of the common Mellin tail. -/
theorem thetaUpperMellinRemainder_iteratedDeriv_bound {T : ℝ} (hT : 1 ≤ T)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c.re + r ≤ 1) (n : ℕ) :
    ‖iteratedDeriv n (thetaUpperMellinRemainder T) c‖ ≤
      n.factorial * (4 * Real.exp (-T)) / r ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (differentiable_thetaUpperMellinRemainder hT).diffContOnCl
  intro z hz
  apply thetaUpperMellinRemainder_norm_le hT
  have hn := Complex.re_le_norm (z - c)
  rw [mem_sphere_iff_norm.mp hz] at hn
  simp only [Complex.sub_re] at hn
  linarith

theorem thetaCenterLower_mellinConvergent_all (s : ℂ) :
    MellinConvergent (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) •
      thetaCenterUpper t⁻¹) s := by
  rw [MellinConvergent.cpow_smul]
  have h := (MellinConvergent.comp_rpow (f := thetaCenterUpper)
    (s := s - 1 / 2) (a := -1) (by norm_num)).mpr
      (thetaCenterUpper_mellinConvergent ((s - 1 / 2) / ((-1 : ℝ) : ℂ)))
  simpa only [Real.rpow_neg_one, sub_eq_add_neg] using! h

/-- Neighboring parameters are compared through a derivative of the common
remainder; the error gains their separation, at every derivative order. -/
theorem thetaUpperMellinRemainder_neighbor_derivatives_bound {T : ℝ} (hT : 1 ≤ T)
    {a r : ℝ} (hr : 0 < r) (ha : a + r ≤ 1)
    {s t : ℂ} (hs : s.re ≤ a) (ht : t.re ≤ a) (n : ℕ) :
    ‖iteratedDeriv n (thetaUpperMellinRemainder T) t -
      iteratedDeriv n (thetaUpperMellinRemainder T) s‖ ≤
      ((n + 1).factorial * (4 * Real.exp (-T)) / r ^ (n + 1)) * ‖t - s‖ := by
  have hd : Differentiable ℂ (iteratedDeriv n (thetaUpperMellinRemainder T)) :=
    (differentiable_thetaUpperMellinRemainder hT).contDiff.differentiable_iteratedDeriv' n
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := {z : ℂ | z.re ≤ a})
    (fun z _ => hd z) ?_ ?_ hs ht
  · intro z hz
    rw [← iteratedDeriv_succ]
    simpa using! thetaUpperMellinRemainder_iteratedDeriv_bound hT
      (c := z) (r := r) hr (by linarith [show z.re ≤ a from hz]) (n + 1)
  · exact (convex_Iic a).linear_preimage Complex.reLm

/-- The two halves share one Mellin kernel, with the completed-zeta normalization. -/
theorem completedRiemannZeta₀_eq_paired_mellin (s : ℂ) :
    completedRiemannZeta₀ s =
      (mellin thetaCenterUpper (s / 2) + mellin thetaCenterUpper ((1 - s) / 2)) / 2 := by
  have h := (hasMellin_add (thetaCenterUpper_mellinConvergent (s / 2))
    (thetaCenterLower_mellinConvergent_all (s / 2))).2
  rw [mellin_cpow_smul, mellin_comp_inv] at h
  have he : mellin (hurwitzEvenFEPair 0).f_modif (s / 2) =
      mellin (fun t : ℝ => thetaCenterUpper t +
        (t : ℂ) ^ (-(1 / 2 : ℂ)) • thetaCenterUpper t⁻¹) (s / 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [thetaCenterKernel_split ht]
  change (hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2 = _
  rw [WeakFEPair.Λ₀, he, h]
  congr 2
  congr 1
  ring

/-- All Xi errors below are derivatives of this one entire function. -/
def xiMellinRemainder (T : ℝ) (s : ℂ) : ℂ :=
  s * (s - 1) / 4 *
    (thetaUpperMellinRemainder T (s / 2) + thetaUpperMellinRemainder T ((1 - s) / 2))

def xiMellinTruncation (T : ℝ) (s : ℂ) : ℂ :=
  1 / 2 + s * (s - 1) / 4 *
    ((∫ t : ℝ in Ioc 0 T, (t : ℂ) ^ (s / 2 - 1) • thetaCenterUpper t) +
     (∫ t : ℝ in Ioc 0 T, (t : ℂ) ^ ((1 - s) / 2 - 1) • thetaCenterUpper t))

/-- Exact actual-Xi identification, including the truncation boundary. -/
theorem xiMellinRemainder_eq_sub {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    xiMellinRemainder T s = xiCompleted s - xiMellinTruncation T s := by
  unfold xiMellinRemainder xiMellinTruncation xiCompleted
  rw [completedRiemannZeta₀_eq_paired_mellin,
    thetaUpperMellinRemainder_eq_sub hT, thetaUpperMellinRemainder_eq_sub hT]
  ring

theorem differentiable_xiMellinRemainder {T : ℝ} (hT : 1 ≤ T) :
    Differentiable ℂ (xiMellinRemainder T) := by
  unfold xiMellinRemainder
  have hd := differentiable_thetaUpperMellinRemainder hT
  exact ((differentiable_id.mul (differentiable_id.sub_const 1)).div_const 4).mul
    ((hd.comp (differentiable_id.div_const 2)).add
      (hd.comp (((differentiable_const 1).sub differentiable_id).div_const 2)))

/-- Explicit common Xi remainder bound on a closed strip. -/
theorem xiMellinRemainder_norm_le {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hl : -1 ≤ s.re) (hu : s.re ≤ 2) :
    ‖xiMellinRemainder T s‖ ≤ 2 * ‖s‖ * ‖s - 1‖ * Real.exp (-T) := by
  have h1 := thetaUpperMellinRemainder_norm_le hT (s := s / 2) (by simp only [Complex.div_ofNat_re]; linarith)
  have h2 := thetaUpperMellinRemainder_norm_le hT (s := (1 - s) / 2) (by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith)
  have hadd := (norm_add_le (thetaUpperMellinRemainder T (s / 2))
    (thetaUpperMellinRemainder T ((1 - s) / 2))).trans (add_le_add h1 h2)
  unfold xiMellinRemainder
  rw [norm_mul, norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    ‖s‖ * ‖s - 1‖ / 4 * ‖thetaUpperMellinRemainder T (s / 2) +
        thetaUpperMellinRemainder T ((1 - s) / 2)‖ ≤
      ‖s‖ * ‖s - 1‖ / 4 * (4 * Real.exp (-T) + 4 * Real.exp (-T)) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ = _ := by ring

/-- All derivative orders, all truncations, and all anchors in the specified
strip with an explicit disk margin. No rank or curvature assertion is made. -/
theorem xiMellinRemainder_iteratedDeriv_bound {T : ℝ} (hT : 1 ≤ T)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hl : -1 ≤ c.re - r) (hu : c.re + r ≤ 2) (n : ℕ) :
    ‖iteratedDeriv n (xiMellinRemainder T) c‖ ≤
      n.factorial * (2 * (‖c‖ + r) * (‖c - 1‖ + r) * Real.exp (-T)) / r ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (differentiable_xiMellinRemainder hT).diffContOnCl
  intro z hz
  have hn : ‖z - c‖ = r := mem_sphere_iff_norm.mp hz
  have hreal : |z.re - c.re| ≤ r := by
    simpa only [Complex.sub_re, hn] using! Complex.abs_re_le_norm (z - c)
  have hstrip := abs_le.mp hreal
  have hzc : ‖z‖ ≤ ‖c‖ + r := by
    calc
      ‖z‖ = ‖(z - c) + c‖ := by congr 1; ring
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ = _ := by rw [hn]; ring
  have hz1 : ‖z - 1‖ ≤ ‖c - 1‖ + r := by
    calc
      ‖z - 1‖ = ‖(z - c) + (c - 1)‖ := by congr 1; ring
      _ ≤ ‖z - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ = _ := by rw [hn]; ring
  calc
    ‖xiMellinRemainder T z‖ ≤ 2 * ‖z‖ * ‖z - 1‖ * Real.exp (-T) :=
      xiMellinRemainder_norm_le hT (by linarith [hstrip.1]) (by linarith [hstrip.2])
    _ ≤ _ := by gcongr

end Reinmann
