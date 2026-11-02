/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.RegularizedEulerMaclaurin
public import Reinmann.StirlingAnalytic
public import Reinmann.ZetaJetRemainder
public import Reinmann.XiAdaptiveTiles
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

/-! Centre-independent error bounds for the pole-free Xi factorization.
Gamma means `Gamma(1+s/2)`, and zeta means the entire extension of `(s-1)zeta(s)`.
The unit-circle bounds hold also at height zero. -/
noncomputable section
namespace Reinmann.UniformXiRemainders
open Set Finset Metric Complex
open RegularizedEulerMaclaurin EulerMaclaurinAnalytic
open scoped Topology

theorem disk_re_bounds {c s : ℂ} (hl : (1 / 2 : ℝ) ≤ c.re) (hu : c.re ≤ 1)
    (hs : ‖s - c‖ ≤ 1) : (-1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 2 := by
  have h := (Complex.abs_re_le_norm (s - c)).trans hs
  rw [Complex.sub_re, abs_le] at h
  constructor <;> linarith

theorem disk_norm_bounds {c s : ℂ} (hc : c ∈ XiAdaptiveTiles.quarter (141 / 10))
    (hs : ‖s - c‖ ≤ 1) : ‖s‖ ≤ 16 ∧ ‖s - 1‖ ≤ 16 := by
  obtain ⟨hl, hu, hi0, hi⟩ := hc
  have hcn : ‖c‖ ≤ 15 := by
    have hsq : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg c, sq_nonneg (c.re - 1)]
  have hc1 : ‖c - 1‖ ≤ 15 := by
    have hsq : ‖c - 1‖ ^ 2 = (c.re - 1) ^ 2 + c.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
      ring
    nlinarith [norm_nonneg (c - 1), sq_nonneg c.re]
  constructor
  · calc ‖s‖ = ‖(s - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ 16 := by linarith
  · calc ‖s - 1‖ = ‖(s - c) + (c - 1)‖ := by congr 1; ring
      _ ≤ ‖s - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ 16 := by linarith

def gammaApprox (s : ℂ) : ℂ :=
  Complex.exp (StirlingGamma.mainTerm (1 + s / 2 + 12)) /
    ∏ j ∈ range 12, (1 + s / 2 + (j : ℂ))

def gammaError (s : ℂ) : ℂ := gammaFactor s - gammaApprox s
def zetaError (s : ℂ) : ℂ := regularZeta s - regularModel s 27

theorem gamma_norm_le_two {s : ℂ} (hl : (-1 / 2 : ℝ) ≤ s.re) (hu : s.re ≤ 2) :
    ‖gammaFactor s‖ ≤ 2 := by
  have hlo : (1 / 2 : ℝ) ≤ (1 + s / 2).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
    linarith
  have hhi : (1 + s / 2).re ≤ (2 : ℝ) := by
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
    linarith
  have hg := Real.convexOn_Gamma.le_max_of_mem_Icc
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ)) (by norm_num : (2 : ℝ) ∈ Set.Ioi (0 : ℝ)) ⟨hlo, hhi⟩
  have hh : Real.Gamma (1 / 2) ≤ (2 : ℝ) := by
    rw [Real.Gamma_one_half_eq]
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  have htwo : Real.Gamma 2 = 1 := by norm_num [Real.Gamma_nat_eq_factorial, Nat.factorial]
  exact (GammaHeightMajorant.gamma_norm_le_real (by linarith : 0 < (1 + s / 2).re)).trans
    (hg.trans (max_le hh (by rw [htwo]; norm_num)))

/-- At height at least five a two-factor recurrence gives a sharper bound. -/
theorem gamma_norm_le_one_high {s : ℂ} (hl : (-1 / 2 : ℝ) ≤ s.re) (hu : s.re ≤ 2)
    (hi : 5 ≤ s.im) : ‖gammaFactor s‖ ≤ 1 := by
  have hrlo : (2 : ℝ) ≤ (1 + s / 2).re + 2 := by
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
    linarith
  have hrhi : (1 + s / 2).re + 2 ≤ (4 : ℝ) := by
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
    linarith
  have him : (5 / 2 : ℝ) ≤ |(1 + s / 2).im| := by
    simp only [Complex.add_im, Complex.one_im, Complex.div_ofNat_im, zero_add]
    exact (by linarith : (5 / 2 : ℝ) ≤ s.im / 2).trans (le_abs_self _)
  have h := GammaHeightMajorant.gamma_norm_le_height (s := 1 + s / 2)
    (by norm_num : (0 : ℝ) < 5 / 2) him 2 (by linarith)
  have hg : Real.Gamma ((1 + s / 2).re + 2) ≤ 6 := by
    have hb := Real.Gamma_strictMonoOn_Ici.monotoneOn hrlo (by norm_num : (2 : ℝ) ≤ 4) hrhi
    have he : Real.Gamma 4 = 6 := by norm_num [Real.Gamma_nat_eq_factorial, Nat.factorial]
    exact hb.trans_eq he
  exact h.trans ((div_le_div_of_nonneg_right hg (by positivity)).trans (by norm_num))

theorem shifted_tail_norm_le {s : ℂ} (hl : (-1 / 2 : ℝ) ≤ s.re) :
    ‖StirlingSum.tail (1 + s / 2 + 12)‖ ≤ (1 / 10 ^ 14 : ℝ) := by
  have hr : (47 / 4 : ℝ) ≤ (1 + s / 2 + 12).re := by
    norm_num [Complex.add_re, Complex.div_re]
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 47 / 4) hr 11
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 11 * (47 / 4) ^ 11)
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 11))
  calc
    _ ≤ (6112 / 15015 : ℝ) / 12 * (1 / (11 * (1 + s / 2 + 12).re ^ 11)) :=
      StirlingSum.tail_norm_le _ (by linarith)
    _ ≤ (6112 / 15015 : ℝ) / 12 * (1 / (11 * (47 / 4) ^ 11)) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ ≤ _ := by norm_num

theorem gamma_identity {s : ℂ} (hs : -2 < s.re) :
    gammaFactor s = gammaApprox s * Complex.exp (StirlingSum.tail (1 + s / 2 + 12)) := by
  have hbase : 0 < (1 + s / 2).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
    linarith
  have hne (j : ℕ) : 1 + s / 2 + (j : ℂ) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    norm_num [Complex.add_re, Complex.div_re] at *
    linarith [Nat.cast_nonneg (α := ℝ) j]
  unfold gammaFactor gammaApprox
  rw [StirlingGamma.Gamma_eq_shift (1 + s / 2) 12
    (by norm_num [Complex.add_re, Complex.div_re] at *; linarith) (fun j _ => hne j),
    Complex.exp_add]
  ring

theorem gammaApprox_eq {s : ℂ} (hs : -2 < s.re) :
    gammaApprox s = gammaFactor s * Complex.exp (-StirlingSum.tail (1 + s / 2 + 12)) := by
  calc
    _ = gammaApprox s * (Complex.exp (StirlingSum.tail (1 + s / 2 + 12)) *
        Complex.exp (-StirlingSum.tail (1 + s / 2 + 12))) := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [gamma_identity hs]; ring

theorem gammaError_norm_le {s : ℂ} (hl : (-1 / 2 : ℝ) ≤ s.re) (hu : s.re ≤ 2) :
    ‖gammaError s‖ ≤ (4 / 10 ^ 14 : ℝ) := by
  have ht := shifted_tail_norm_le hl
  have he := Complex.norm_exp_sub_one_le (x := -StirlingSum.tail (1 + s / 2 + 12))
    (by rw [norm_neg]; linarith)
  simp only [norm_neg] at he
  have hb : ‖Complex.exp (-StirlingSum.tail (1 + s / 2 + 12)) - 1‖ ≤
      (2 / 10 ^ 14 : ℝ) := by exact he.trans (by linarith)
  have hform : gammaError s = gammaFactor s *
      (1 - Complex.exp (-StirlingSum.tail (1 + s / 2 + 12))) := by
    rw [gammaError, gammaApprox_eq (by linarith : -2 < s.re)]
    ring
  rw [hform, norm_mul, norm_sub_rev]
  exact (mul_le_mul (gamma_norm_le_two hl hu) hb (norm_nonneg _) (by norm_num)).trans_eq
    (by ring)

theorem gammaApprox_differentiableAt {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ gammaApprox s := by
  have hbase : 0 < (1 + s / 2).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
    linarith
  have hshift : DifferentiableAt ℂ (fun z : ℂ => 1 + z / 2 + 12) s :=
    ((differentiableAt_id.div_const 2).const_add 1).add_const 12
  have hmain := (StirlingAnalytic.mainTerm_differentiableAt _
    (by norm_num [Complex.add_re, Complex.div_re] at *; linarith)).comp s hshift
  have hprod : DifferentiableAt ℂ
      (fun z : ℂ => ∏ j ∈ range 12, (1 + z / 2 + (j : ℂ))) s := by
    apply DifferentiableAt.fun_finsetProd
    intro j _
    exact ((differentiableAt_id.div_const 2).const_add 1).add_const (j : ℂ)
  apply hmain.cexp.div hprod
  apply prod_ne_zero_iff.mpr
  intro j _
  apply Complex.ne_zero_of_re_pos
  norm_num [Complex.add_re, Complex.div_re] at *
  linarith [Nat.cast_nonneg (α := ℝ) j]

theorem gamma_coefficient_error_le {c : ℂ}
    (hl : (1 / 2 : ℝ) ≤ c.re) (hu : c.re ≤ 1) (n : ℕ) :
    ‖iteratedDeriv n gammaFactor c / (n.factorial : ℂ) -
      iteratedDeriv n gammaApprox c / (n.factorial : ℂ)‖ ≤ (4 / 10 ^ 14 : ℝ) := by
  have hF : DifferentiableOn ℂ gammaFactor (ball c 1) := by
    intro s hs
    exact (gammaFactor_differentiableAt
      (by have h := (disk_re_bounds hl hu (mem_ball_iff_norm.mp hs).le).1; linarith)).differentiableWithinAt
  have hG : DifferentiableOn ℂ gammaApprox (ball c 1) := by
    intro s hs
    exact (gammaApprox_differentiableAt
      (by have h := (disk_re_bounds hl hu (mem_ball_iff_norm.mp hs).le).1; linarith)).differentiableWithinAt
  have hE : DiffContOnCl ℂ gammaError (ball c 1) := by
    apply DifferentiableOn.diffContOnCl
    intro s hs
    rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)] at hs
    have hb := disk_re_bounds hl hu (mem_closedBall_iff_norm.mp hs)
    exact ((gammaFactor_differentiableAt (by linarith : -2 < s.re)).sub
      (gammaApprox_differentiableAt (by linarith : -2 < s.re))).differentiableWithinAt
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) hE (fun s hs =>
      gammaError_norm_le (disk_re_bounds hl hu (mem_sphere_iff_norm.mp hs).le).1
        (disk_re_bounds hl hu (mem_sphere_iff_norm.mp hs).le).2)
  have heq : iteratedDeriv n gammaError c =
      iteratedDeriv n gammaFactor c - iteratedDeriv n gammaApprox c := by
    exact iteratedDeriv_fun_sub
      (hF.analyticAt (ball_mem_nhds c (by norm_num))).contDiffAt
      (hG.analyticAt (ball_mem_nhds c (by norm_num))).contDiffAt
  rw [heq] at h
  simp only [one_pow, div_one] at h
  rw [← sub_div, norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr (h.trans_eq (by ring))

theorem zetaError_differentiable : Differentiable ℂ zetaError :=
  regularZeta_differentiable.sub (regularModel_differentiable 27 (by norm_num))

theorem zetaError_norm_le {c s : ℂ} (hc : c ∈ XiAdaptiveTiles.quarter (141 / 10))
    (hs : ‖s - c‖ ≤ 1) : ‖zetaError s‖ ≤ (6 / 10 ^ 8 : ℝ) := by
  have hre := (disk_re_bounds hc.1 hc.2.1 hs).1
  have hn := disk_norm_bounds hc hs
  have hpos : 0 < s.re + 11 := by linarith
  have hR := EulerMaclaurinTail.remainder_norm_le (by linarith : -11 < s.re)
    (by norm_num : (0 : ℝ) < 27)
  have hP := ZetaJetRemainder.rising_norm_le hn.1 12
  have ha := div_le_div_of_nonneg_right hP (Nat.cast_nonneg (α := ℝ) (12 : ℕ).factorial)
  have hexp : (27 : ℝ) ^ (-s.re - 11) ≤ (27 : ℝ) ^ (-10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hb : (6112 / 15015 : ℝ) * (27 : ℝ) ^ (-s.re - 11) / (s.re + 11) ≤
      (6112 / 15015 : ℝ) * (27 : ℝ) ^ (-10 : ℝ) / (21 / 2) := by
    calc
      _ ≤ (6112 / 15015 : ℝ) * (27 : ℝ) ^ (-10 : ℝ) / (s.re + 11) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have htail := hR.trans (mul_le_mul ha hb (by positivity)
    (by positivity : 0 ≤ (∏ j ∈ range 12, ((16 : ℝ) + j)) / ((12 : ℕ).factorial : ℝ)))
  rw [zetaError, regularZeta_eq_model_add_remainder (by linarith : -11 < s.re) 27
    (by norm_num), add_sub_cancel_left, norm_mul]
  apply (mul_le_mul hn.2 htail (norm_nonneg _) (by norm_num)).trans
  norm_num [Real.rpow_neg, Real.rpow_natCast, prod_range_succ]

/-- The same 6e-8 budget works for every centre, including height zero. -/
theorem zeta_coefficient_error_le {c : ℂ} (hc : c ∈ XiAdaptiveTiles.quarter (141 / 10))
    (n : ℕ) :
    ‖iteratedDeriv n regularZeta c / (n.factorial : ℂ) -
      iteratedDeriv n (fun z => regularModel z 27) c / (n.factorial : ℂ)‖ ≤
      (6 / 10 ^ 8 : ℝ) := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) zetaError_differentiable.diffContOnCl
    (fun z hz => zetaError_norm_le hc (mem_sphere_iff_norm.mp hz).le)
  have heq : iteratedDeriv n zetaError c = iteratedDeriv n regularZeta c -
      iteratedDeriv n (fun z => regularModel z 27) c := by
    exact iteratedDeriv_fun_sub (regularZeta_differentiable.analyticAt c).contDiffAt
      ((regularModel_differentiable 27 (by norm_num)).analyticAt c).contDiffAt
  rw [heq] at h
  simp only [one_pow, div_one] at h
  rw [← sub_div, norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr (h.trans_eq (by ring))

end Reinmann.UniformXiRemainders
