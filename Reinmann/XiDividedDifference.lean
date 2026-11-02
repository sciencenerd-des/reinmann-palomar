/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.JensenProgram
public import Reinmann.PseudoHermitian
public import Reinmann.CompletedZetaConj
public import Mathlib.Analysis.Calculus.DSlope

@[expose] public section

/-!
# Arithmetic divided-difference kernel and its zero-state masses

The kernel is regular at reflected pairs: `dslope` supplies the derivative,
not Lean's totalized division by zero. Its spectral defect vanishes at Xi
zeros without RH. Its diagonal mass, however, is zero off the critical line
and also at multiple critical-line zeros. Nonzero mass for all zero states
would therefore require RH and simplicity. No such nonvanishing is asserted.

The bounded Fock operator obtained from the kernel's coefficients is a written
construction in `research/pseudo_hermitian/XI_DIVIDED_DIFFERENCE.md`, not a
formal Hilbert-space result in this module.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiDividedDifference

theorem xi_one_sub (s : ℂ) : xiCompleted (1 - s) = xiCompleted s := by
  unfold xiCompleted
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem xi_conj (s : ℂ) : xiCompleted (conj s) = conj (xiCompleted s) := by
  simp [xiCompleted, completedZeta₀_conj, map_add, map_mul, map_div₀, map_sub,
    map_ofNat]

theorem deriv_xi_one_sub (s : ℂ) :
    deriv xiCompleted (1 - s) = -deriv xiCompleted s := by
  have hlin : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using! (hasDerivAt_id s).const_sub 1
  have hcomp := ((differentiable_xiCompleted (1 - s)).hasDerivAt).comp s hlin
  rw [show (xiCompleted ∘ fun z : ℂ => 1 - z) = xiCompleted by
    funext z; simp [Function.comp, xi_one_sub]] at hcomp
  have h := hcomp.unique (differentiable_xiCompleted s).hasDerivAt
  linear_combination -h

theorem deriv_xi_conj (s : ℂ) :
    deriv xiCompleted (conj s) = conj (deriv xiCompleted s) := by
  have hcc := ((differentiable_xiCompleted (conj s)).hasDerivAt).conj_conj
  rw [Complex.conj_conj] at hcc
  have heq : xiCompleted =ᶠ[nhds s]
      (⇑(starRingEnd ℂ) ∘ xiCompleted ∘ ⇑(starRingEnd ℂ)) := by
    filter_upwards with z
    change xiCompleted z = conj (xiCompleted (conj z))
    rw [xi_conj, Complex.conj_conj]
  have h := (hcc.congr_of_eventuallyEq heq).deriv
  have hc := congrArg (starRingEnd ℂ) h
  simpa using! hc.symm

def kernel (s t : ℂ) : ℂ := I * dslope xiCompleted (1 - conj t) s

theorem kernel_of_ne {s t : ℂ} (h : s ≠ 1 - conj t) :
    kernel s t = I * ((xiCompleted s - conj (xiCompleted t)) / (s + conj t - 1)) := by
  rw [kernel, dslope_of_ne _ h, slope_def_field, xi_one_sub, xi_conj]
  congr 2
  ring

theorem kernel_at_reflection {s t : ℂ} (h : s = 1 - conj t) :
    kernel s t = I * deriv xiCompleted s := by
  rw [kernel, ← h, dslope_same]

theorem kernel_balance (s t : ℂ) :
    (s + conj t - 1) * kernel s t = I * (xiCompleted s - conj (xiCompleted t)) := by
  have h := sub_smul_dslope xiCompleted (1 - conj t) s
  simp only [smul_eq_mul, xi_one_sub, xi_conj] at h
  unfold kernel
  calc
    (s + conj t - 1) * (I * dslope xiCompleted (1 - conj t) s) =
        I * ((s - (1 - conj t)) * dslope xiCompleted (1 - conj t) s) := by ring
    _ = _ := by rw [h]

theorem kernel_spectral_defect (s t : ℂ) :
    (spectralParam s - conj (spectralParam t)) * kernel s t =
      xiCompleted s - conj (xiCompleted t) := by
  have hp : spectralParam s - conj (spectralParam t) = -I * (s + conj t - 1) := by
    simp only [spectralParam, map_mul, map_neg, map_sub, map_div₀, map_one,
      map_ofNat, Complex.conj_I]
    ring
  rw [hp, mul_assoc, kernel_balance, ← mul_assoc]
  simp

theorem kernel_hermitian (s t : ℂ) : kernel s t = conj (kernel t s) := by
  by_cases hs : s = 1 - conj t
  · have ht : t = 1 - conj s := by
      have h := congrArg (starRingEnd ℂ) hs
      simp only [map_sub, map_one, Complex.conj_conj] at h
      linear_combination h
    have hc : conj t = 1 - s := by linear_combination hs
    rw [kernel_at_reflection hs, kernel_at_reflection ht, map_mul,
      Complex.conj_I, ← deriv_xi_conj, hc, deriv_xi_one_sub]
    ring
  · have ht : t ≠ 1 - conj s := by
      intro ht
      apply hs
      have h := congrArg (starRingEnd ℂ) ht
      simp only [map_sub, map_one, Complex.conj_conj] at h
      linear_combination h
    rw [kernel_of_ne hs, kernel_of_ne ht]
    simp only [map_mul, map_div₀, map_sub, map_add, map_one, Complex.conj_I,
      Complex.conj_conj]
    rw [add_comm (conj t) s]
    ring

theorem kernel_zero_spectral_symmetry {s t : ℂ}
    (hs : xiCompleted s = 0) (ht : xiCompleted t = 0) :
    spectralParam s * kernel s t = conj (spectralParam t) * kernel s t := by
  have h := kernel_spectral_defect s t
  rw [hs, ht, map_zero, sub_zero] at h
  exact sub_eq_zero.mp (by simpa [sub_mul] using! h)

theorem reflected_self_iff (s : ℂ) : s = 1 - conj s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp

theorem kernel_mass_on_critical {s : ℂ} (hs : s.re = 1 / 2) :
    kernel s s = I * deriv xiCompleted s :=
  kernel_at_reflection ((reflected_self_iff s).mpr hs)

theorem kernel_mass_off_critical {s : ℂ} (hz : xiCompleted s = 0)
    (hs : s.re ≠ 1 / 2) : kernel s s = 0 := by
  rw [kernel_of_ne (mt (reflected_self_iff s).mp hs), hz]
  simp

/-- For this arithmetic form, non-isotropy demands simplicity as well as criticality. -/
theorem kernel_mass_ne_zero_iff {s : ℂ} (hz : xiCompleted s = 0) :
    kernel s s ≠ 0 ↔ s.re = 1 / 2 ∧ deriv xiCompleted s ≠ 0 := by
  by_cases hs : s.re = 1 / 2
  · rw [kernel_mass_on_critical hs]
    simp [hs, Complex.I_ne_zero]
  · rw [kernel_mass_off_critical hz hs]
    constructor
    · intro h
      exact False.elim (h rfl)
    · intro h
      exact False.elim (hs h.1)

/-- A multiple critical-line zero would be isotropic, even if RH holds. -/
theorem kernel_mass_at_multiple_zero {s : ℂ} (hz : xiCompleted s = 0)
    (hd : deriv xiCompleted s = 0) : kernel s s = 0 := by
  by_cases hs : s.re = 1 / 2
  · rw [kernel_mass_on_critical hs, hd, mul_zero]
  · exact kernel_mass_off_critical hz hs

end Reinmann.XiDividedDifference
