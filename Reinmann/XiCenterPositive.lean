/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.XiTaylorIdentification
public import Reinmann.FinitePFStrict
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Effective theta bound and positivity at the Xi center

Bounds use the actual Mathlib theta kernel, rather than a numerical certificate.
-/
noncomputable section
namespace Reinmann
open Set MeasureTheory HurwitzZeta

/-- A simple geometric majorant, intentionally weaker than Gaussian decay. -/
theorem theta_center_term_bound {t : ℝ} (ht : 1 ≤ t) (n : ℕ) :
    Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2 * t) ≤
      Real.exp (-t) * (1 / 2 : ℝ) ^ n := by
  have ht0 : 0 ≤ t := by linarith
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hsq : (n + 1 : ℝ) ≤ (n + 1 : ℝ)^2 := by nlinarith
  have he : Real.exp (-t) ≤ (1 / 2 : ℝ) := by
    have h1 : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
    have h2 : Real.exp 1 ≤ Real.exp t := Real.exp_le_exp.mpr ht
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos t)).mpr
    linarith
  calc
    Real.exp (-Real.pi * (n + 1 : ℝ)^2 * t) ≤ Real.exp (-((n + 1 : ℝ) * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hsq ht0,
        mul_le_mul_of_nonneg_right hpi (mul_nonneg (sq_nonneg (n + 1 : ℝ)) ht0)]
    _ = Real.exp (-t) * Real.exp (-t)^n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-t) * (1 / 2 : ℝ)^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le he _) (Real.exp_pos _).le

/-- The actual theta tail is nonnegative and has an explicit integrable bound. -/
theorem theta_center_tail_bounds {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ cosKernel 0 t - 1 ∧ cosKernel 0 t - 1 ≤ 4 * Real.exp (-t) := by
  have hs : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * t))
      (cosKernel 0 t - 1) := by
    simpa using! hasSum_nat_cosKernel₀ 0 (by linarith : 0 < t)
  have hg := hasSum_geometric_two.mul_left (2 * Real.exp (-t))
  constructor
  · exact HasSum.nonneg (fun n => by positivity) hs
  · have h := hasSum_le (fun n => by
      have := theta_center_term_bound ht n
      nlinarith) hs hg
    nlinarith

/-- Upper half of the convergent, pole-subtracted theta Mellin kernel. -/
def thetaCenterUpper : ℝ → ℂ :=
  (Ioi 1).indicator (hurwitzEvenFEPair 0).f_modif

theorem thetaCenterUpper_mellinConvergent (s : ℂ) :
    MellinConvergent thetaCenterUpper s := by
  have h := ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin s).1
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) •
    (hurwitzEvenFEPair 0).f_modif t) (Ioi 0) at h
  simpa only [MellinConvergent, thetaCenterUpper, indicator_smul] using!
    h.indicator measurableSet_Ioi

theorem thetaCenterUpper_eq {t : ℝ} (ht : 1 < t) :
    thetaCenterUpper t = (cosKernel 0 t - 1 : ℝ) := by
  simp [thetaCenterUpper, WeakFEPair.f_modif, ht,
    not_lt_of_ge ht.le, hurwitzEvenFEPair, Function.comp_def,
    evenKernel_eq_cosKernel_of_zero, Complex.ofReal_sub]

theorem thetaCenterUpper_eq_zero {t : ℝ} (ht : t ≤ 1) :
    thetaCenterUpper t = 0 := by
  simp [thetaCenterUpper, not_lt_of_ge ht]

/-- Exact splitting, including the deliberately zero value at the boundary. -/
theorem thetaCenterKernel_split {t : ℝ} (ht : 0 < t) :
    (hurwitzEvenFEPair 0).f_modif t = thetaCenterUpper t +
      (t : ℂ) ^ (-(1 / 2 : ℂ)) • thetaCenterUpper t⁻¹ := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · rw [thetaCenterUpper_eq_zero h.le, zero_add]
    have hi : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr h
    rw [thetaCenterUpper, indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hi)]
    have hf := (hurwitzEvenFEPair 0).hf_modif_FE t ht
    have hg : (hurwitzEvenFEPair 0).g_modif = (hurwitzEvenFEPair 0).f_modif := by
      simp [WeakFEPair.g_modif, WeakFEPair.f_modif, hurwitzEvenFEPair,
        evenKernel_eq_cosKernel_of_zero]
    rw [hg] at hf
    simp only [one_div] at hf
    change (hurwitzEvenFEPair 0).f_modif t⁻¹ =
      (1 * ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ)) • (hurwitzEvenFEPair 0).f_modif t at hf
    simp only [one_mul] at hf
    have hc := Complex.ofReal_cpow ht.le (1 / 2 : ℝ)
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hc
    rw [hf, ← mul_smul, Complex.cpow_neg, ← hc, inv_mul_cancel₀, one_smul]
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne'
  · simp [thetaCenterUpper, WeakFEPair.f_modif]
  · have hu : thetaCenterUpper t = (hurwitzEvenFEPair 0).f_modif t := by
      simp [thetaCenterUpper, h]
    rw [hu]
    have hi : t⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < t)).mpr h.le
    rw [thetaCenterUpper_eq_zero hi, smul_zero, add_zero]

/-- No convergence is assumed: it follows from the existing strong FE pair. -/
theorem thetaCenterLower_mellinConvergent :
    MellinConvergent (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) •
      thetaCenterUpper t⁻¹) (1 / 4 : ℂ) := by
  rw [MellinConvergent.cpow_smul]
  have h := (MellinConvergent.comp_rpow (f := thetaCenterUpper)
    (s := -(1 / 4 : ℂ)) (a := -1) (by norm_num)).mpr
      (by simpa using! thetaCenterUpper_mellinConvergent (1 / 4 : ℂ))
  simpa only [Real.rpow_neg_one, show (1 / 4 : ℂ) + -(1 / 2 : ℂ) = -(1 / 4 : ℂ) by norm_num]
    using! h

/-- Exact theta integral representation of the actual completed zeta at 1/2. -/
theorem completedRiemannZeta₀_center_eq_mellin :
    completedRiemannZeta₀ (1 / 2) = mellin thetaCenterUpper (1 / 4) := by
  have h := (hasMellin_add (thetaCenterUpper_mellinConvergent (1 / 4))
    thetaCenterLower_mellinConvergent).2
  have hl : mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) •
      thetaCenterUpper t⁻¹) (1 / 4 : ℂ) = mellin thetaCenterUpper (1 / 4) := by
    rw [mellin_cpow_smul, mellin_comp_inv]
    norm_num
  rw [hl] at h
  have he : mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ) =
      mellin (fun t : ℝ => thetaCenterUpper t +
        (t : ℂ) ^ (-(1 / 2 : ℂ)) • thetaCenterUpper t⁻¹) (1 / 4) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [thetaCenterKernel_split ht]
  change (hurwitzEvenFEPair 0).Λ₀ ((1 / 2 : ℂ) / 2) / 2 = _
  norm_num
  rw [WeakFEPair.Λ₀, he, h]
  ring

theorem thetaCenterUpper_mellin_eq_integral (s : ℂ) :
    mellin thetaCenterUpper s = ∫ t : ℝ in Ioi 1,
      (t : ℂ) ^ (s - 1) • (hurwitzEvenFEPair 0).f_modif t := by
  unfold mellin thetaCenterUpper
  simp only [← indicator_smul]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hs : Ioi (1 : ℝ) ∩ Ioi 0 = Ioi 1 := by
    ext t
    change (1 < t ∧ 0 < t) ↔ 1 < t
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by linarith⟩
  rw [hs]

/-- A common majorant uniform in the Mellin parameter on a half-plane. -/
theorem thetaCenterUpper_weighted_norm_bound_halfPlane {t : ℝ} (ht : 1 < t)
    {s : ℂ} (hs : s.re ≤ 1) :
    ‖(t : ℂ) ^ (s - 1) • thetaCenterUpper t‖ ≤ 4 * Real.exp (-t) := by
  have ht0 : 0 < t := by linarith
  rw [thetaCenterUpper_eq ht, norm_smul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
    Real.norm_of_nonneg (theta_center_tail_bounds ht.le).1]
  calc
    t ^ (s - 1).re * (cosKernel 0 t - 1) ≤ 1 * (cosKernel 0 t - 1) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos ht.le
        (by simpa using! sub_nonpos.mpr hs)) (theta_center_tail_bounds ht.le).1
    _ ≤ 4 * Real.exp (-t) := by simpa using! (theta_center_tail_bounds ht.le).2

theorem thetaCenterUpper_weighted_norm_bound {t : ℝ} (ht : 1 < t) :
    ‖(t : ℂ) ^ ((1 / 4 : ℂ) - 1) • thetaCenterUpper t‖ ≤ 4 * Real.exp (-t) := by
  exact thetaCenterUpper_weighted_norm_bound_halfPlane ht (by norm_num)

/-- Effective truncation of one common theta Mellin kernel. The estimate is
uniform in the stated half-plane and includes every truncation boundary T ≥ 1.
It does not estimate saddle errors or curvature. -/
theorem thetaCenterUpper_mellin_tail_norm_le {T : ℝ} (hT : 1 ≤ T)
    {s : ℂ} (hs : s.re ≤ 1) :
    ‖∫ t : ℝ in Ioi T, (t : ℂ) ^ (s - 1) • thetaCenterUpper t‖ ≤
      4 * Real.exp (-T) := by
  calc
    _ ≤ ∫ t : ℝ in Ioi T, 4 * Real.exp (-t) := by
      apply norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi T).const_mul 4)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change T < t at ht
      exact thetaCenterUpper_weighted_norm_bound_halfPlane (by linarith : 1 < t) hs
    _ = 4 * Real.exp (-T) := by rw [integral_const_mul, integral_exp_neg_Ioi]

/-- The remainder is defined once for the common Mellin kernel. -/
def thetaUpperMellinRemainder (T : ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi T, (t : ℂ) ^ (s - 1) • thetaCenterUpper t

theorem thetaUpperMellinRemainder_norm_le {T : ℝ} (hT : 1 ≤ T)
    {s : ℂ} (hs : s.re ≤ 1) :
    ‖thetaUpperMellinRemainder T s‖ ≤ 4 * Real.exp (-T) :=
  thetaCenterUpper_mellin_tail_norm_le hT hs

/-- This is the actual truncation error, including the truncation boundary
in the finite piece and avoiding any unproved endpoint trace assumption. -/
theorem thetaUpperMellinRemainder_eq_sub {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    thetaUpperMellinRemainder T s = mellin thetaCenterUpper s -
      ∫ t : ℝ in Ioc 0 T, (t : ℂ) ^ (s - 1) • thetaCenterUpper t := by
  have hT0 : 0 ≤ T := by linarith
  have hf := thetaCenterUpper_mellinConvergent s
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • thetaCenterUpper t) (Ioi 0) at hf
  have hd : Disjoint (Ioc (0 : ℝ) T) (Ioi T) := by
    refine disjoint_left.mpr ?_
    intro t ht hi
    exact (not_lt_of_ge ht.2) hi
  have hu := setIntegral_union hd measurableSet_Ioi
    (hf.mono_set Ioc_subset_Ioi_self)
    (hf.mono_set (fun t ht => hT0.trans_lt ht))
  rw [Ioc_union_Ioi_eq_Ioi hT0] at hu
  change mellin thetaCenterUpper s = _ + thetaUpperMellinRemainder T s at hu
  rw [hu]
  abel

/-- Explicit norm enclosure, with no floating point constants. -/
theorem completedRiemannZeta₀_center_norm_le :
    ‖completedRiemannZeta₀ (1 / 2)‖ ≤ 4 * Real.exp (-1) := by
  rw [completedRiemannZeta₀_center_eq_mellin, thetaCenterUpper_mellin_eq_integral]
  calc
    ‖∫ t : ℝ in Ioi 1, (t : ℂ) ^ ((1 / 4 : ℂ) - 1) •
      (hurwitzEvenFEPair 0).f_modif t‖ ≤ ∫ t : ℝ in Ioi 1, 4 * Real.exp (-t) := by
      apply norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 1).const_mul 4)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hu : (hurwitzEvenFEPair 0).f_modif t = thetaCenterUpper t := by
        simp [thetaCenterUpper, ht]
      rw [hu]
      exact thetaCenterUpper_weighted_norm_bound ht
    _ = 4 * Real.exp (-1) := by rw [integral_const_mul, integral_exp_neg_Ioi]

/-- The value of the actual entire Xi function at its center is positive. -/
theorem xiCompleted_center_re_pos : 0 < (xiCompleted (1 / 2)).re := by
  have h := (Complex.re_le_norm (completedRiemannZeta₀ (1 / 2))).trans
    completedRiemannZeta₀_center_norm_le
  have he : Real.exp (-1) < 1 := by
    simpa only [Real.exp_zero] using! (Real.exp_lt_exp.mpr (by norm_num : (-1 : ℝ) < 0))
  have hx : xiCompleted (1 / 2) = (1 / 2 : ℂ) - completedRiemannZeta₀ (1 / 2) / 8 := by
    unfold xiCompleted
    ring
  rw [hx]
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.div_ofNat_re, Complex.one_re]
  linarith

/-- The folded function has the same positive center normalization. -/
theorem foldedXi_zero_eq_center : foldedXi 0 = xiCompleted (1 / 2) := by
  simpa [centeredXi] using! foldedXi_sq 0

theorem xiMomentCoeff_zero_cast : (XiMomentCoeff 0 : ℂ) = xiCompleted (1 / 2) := by
  simpa [centeredXi] using! xiMomentCoeff_eq_centeredXi_taylor 0

theorem xiMomentCoeff_zero_pos : 0 < XiMomentCoeff 0 := by
  have h := congrArg Complex.re xiMomentCoeff_zero_cast
  simpa only [Complex.ofReal_re, ← h] using! xiCompleted_center_re_pos

theorem foldedXi_zero_re_pos : 0 < (foldedXi 0).re := by
  rw [foldedXi_zero_eq_center]
  exact xiCompleted_center_re_pos

namespace FinitePFStrict

theorem linearFactors_zero (t : ℕ → ℝ) (m : ℕ) (g : ℕ → ℝ) :
    linearFactors t m g 0 = g 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simpa [linearFactors, linearFactor] using! ih

/-- Actual Xi positivity supplies the quotient's center value automatically.
The genuinely analytic factor extraction and finite-PF premises remain. -/
theorem xi_contig_positive_of_factor_extraction_without_center {r : ℕ}
    (hextract : ∀ m : ℕ, ∃ (g : ℕ → ℝ) (t : ℕ → ℝ),
      FinitePF g r ∧ (∀ i, 0 < t i) ∧ XiMomentCoeff = linearFactors t m g) :
    ∀ k ≤ r, ∀ m, 0 < XiToeplitzContigMinor k m := by
  apply xi_contig_positive_of_factor_extraction
  intro m
  obtain ⟨g, t, hg, ht, heq⟩ := hextract m
  refine ⟨g, t, hg, ?_, ht, heq⟩
  have hc := congrFun heq 0
  rw [linearFactors_zero] at hc
  rw [← hc]
  exact xiMomentCoeff_zero_pos

end FinitePFStrict
end Reinmann
