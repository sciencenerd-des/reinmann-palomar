/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.EulerMaclaurinAnalytic
public import Reinmann.JensenProgram
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

/-! Removing the zeta pole before evaluating Taylor jets. The value at one is
the proved residue, rather than Mathlib's junk value for zeta itself. -/
noncomputable section
namespace Reinmann.RegularizedEulerMaclaurin
open Set Filter Finset EulerMaclaurinFinite EulerMaclaurinZeta
open EulerMaclaurinAnalytic
open scoped Topology

def regularZeta : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

@[simp] theorem regularZeta_one : regularZeta 1 = 1 := by simp [regularZeta]

theorem regularZeta_of_ne {s : ℂ} (hs : s ≠ 1) :
    regularZeta s = (s - 1) * riemannZeta s := Function.update_of_ne hs _ _

theorem regularZeta_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    regularZeta =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact regularZeta_of_ne hz

theorem regularZeta_differentiableAt_of_ne {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ regularZeta s :=
  (((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq
    (regularZeta_eventuallyEq hs))

theorem regularZeta_differentiable : Differentiable ℂ regularZeta := by
  intro s
  by_cases hs : s = 1
  · subst s
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact regularZeta_differentiableAt_of_ne hz
    · simpa only [regularZeta, continuousAt_update_same] using! riemannZeta_residue_one
  · exact regularZeta_differentiableAt_of_ne hs

def regularModel (s : ℂ) (N : ℕ) : ℂ :=
  (s - 1) * (initialSum s N + power s 0 N / 2 + correction s N) + (N : ℂ) ^ (1 - s)

theorem regularModel_eq {s : ℂ} (hs : s ≠ 1) (N : ℕ) :
    regularModel s N = (s - 1) * finiteModel s N := by
  unfold regularModel finiteModel
  field_simp [sub_ne_zero.mpr hs]
  <;> ring

theorem regularModel_differentiable (N : ℕ) (hN : 0 < N) :
    Differentiable ℂ (fun s => regularModel s N) := by
  intro s
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbase : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : DifferentiableAt ℂ (fun z => initialSum z N) s := by
    apply DifferentiableAt.fun_sum
    intro n _
    exact power_differentiableAt s 0 (by positivity)
  exact ((differentiableAt_id.sub_const 1).mul
    ((hi.add ((power_differentiableAt s 0 hNr).div_const 2)).add
      (correction_differentiableAt s hNr))).add
    (((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hbase))

/-- The Euler--Maclaurin identity on a connected half-plane, including `s=1`. -/
theorem regularZeta_eq_model_add_remainder {s : ℂ} (hs : -11 < s.re)
    (N : ℕ) (hN : 0 < N) :
    regularZeta s = regularModel s N + (s - 1) * EulerMaclaurinTail.remainder s N := by
  let U : Set ℂ := {z | -11 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt (-11)).isPreconnected
  have hZ : AnalyticOnNhd ℂ regularZeta U := regularZeta_differentiable.differentiableOn.analyticOnNhd hU
  have hM : AnalyticOnNhd ℂ
      (fun z => regularModel z N + (z - 1) * EulerMaclaurinTail.remainder z N) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact ((regularModel_differentiable N hN z).add
      ((differentiableAt_id.sub_const 1).mul
        (remainder_differentiableAt hz N hN))).differentiableWithinAt
  have hpoint : (2 : ℂ) ∈ U := by norm_num [U]
  have hfg : regularZeta =ᶠ[𝓝 (2 : ℂ)]
      (fun z => regularModel z N + (z - 1) * EulerMaclaurinTail.remainder z N) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have h1 : z ≠ 1 := by intro h; simp [h] at hz
    rw [regularZeta_of_ne h1, EulerMaclaurinZeta.zeta_eq_model_add_remainder hz N hN,
      regularModel_eq h1]
    ring
  exact hZ.eqOn_of_preconnected_of_eventuallyEq hM hconn hpoint hfg hs

def gammaFactor (s : ℂ) : ℂ := Complex.Gamma (1 + s / 2)
def piFactor (s : ℂ) : ℂ := Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))

theorem gammaFactor_differentiableAt {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ gammaFactor s := by
  have hr : 0 < (1 + s / 2).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]
    linarith
  exact (Complex.differentiableAt_Gamma _ (fun m hm => by
    have h := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) m])).comp s
    ((differentiableAt_id.div_const 2).const_add 1)

theorem piFactor_differentiable : Differentiable ℂ piFactor := by
  intro s
  exact (((differentiableAt_id.div_const 2).neg).mul_const _).cexp

theorem piFactor_eq_cpow (s : ℂ) : piFactor s = (Real.pi : ℂ) ^ (-s / 2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    ← Complex.ofReal_log Real.pi_pos.le]
  unfold piFactor
  congr 1
  ring

theorem xi_eq_regular_product_of_ne {s : ℂ} (hr : 0 < s.re) (h1 : s ≠ 1) :
    xiCompleted s = piFactor s * gammaFactor s * regularZeta s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  have hg : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hr
  have hz : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero h0]
    field_simp
  have hhalf : s / 2 ≠ 0 := div_ne_zero h0 (by norm_num)
  rw [xiCompleted_eq_product h0 h1, hz, Complex.Gammaℝ_def, regularZeta_of_ne h1,
    piFactor_eq_cpow]
  unfold gammaFactor
  rw [add_comm (1 : ℂ), Complex.Gamma_add_one _ hhalf]
  ring

/-- The pole-free evaluator agrees with actual Xi also at the pole of zeta. -/
theorem xi_eq_regular_product {s : ℂ} (hs : 0 < s.re) :
    xiCompleted s = piFactor s * gammaFactor s * regularZeta s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ xiCompleted U := differentiable_xiCompleted.differentiableOn.analyticOnNhd hU
  have hG : AnalyticOnNhd ℂ (fun z => piFactor z * gammaFactor z * regularZeta z) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    change 0 < z.re at hz
    exact (((piFactor_differentiable z).mul
      (gammaFactor_differentiableAt (by linarith : -2 < z.re))).mul
      (regularZeta_differentiable z)).differentiableWithinAt
  have hfg : xiCompleted =ᶠ[𝓝 (2 : ℂ)]
      (fun z => piFactor z * gammaFactor z * regularZeta z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact xi_eq_regular_product_of_ne (by linarith) (by intro h; simp [h] at hz)
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num [U] : (2 : ℂ) ∈ U) hfg hs

end Reinmann.RegularizedEulerMaclaurin
