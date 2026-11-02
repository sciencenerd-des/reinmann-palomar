/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.CompletedZetaConj
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# The Real Critical-Line Slice and On-Line Zero Detection

We turn the critical-line realness of the completed zeta into a genuine
*real-variable* object and apply real oscillation theory.

* `completedRiemannZeta_real_on_critical_line`: `Λ` is real on `Re s = 1/2`
  (inherited from `Λ₀` realness plus `1/s + 1/(1-s) = 2·Re(1/s)` being real there).
* `Zslice : ℝ → ℝ`, `Zslice t = Re Λ(1/2 + it)`, is **continuous** and equals the
  full complex value: `Λ(1/2+it) = (Zslice t : ℂ)`.
* `Zslice_eq_zero_iff`: `Zslice t = 0 ↔ Λ(1/2+it) = 0`, and a zero of `Λ` on the
  line is a zero of `ζ` on the line.
* `riemannZeta_critical_zero_of_sign_change`: **a sign change of `Zslice` forces a
  zero of `ζ` on the critical line** (Hardy's method, via the intermediate value
  theorem).

These are genuine, unconditional, *on-line* results about the distribution of
critical-line zeros — not equivalent to RH (RH is about the *off-line* exclusion).
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Reinmann

/-! ### Geometry of the critical-line point -/

theorem linePoint_re (t : ℝ) : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
theorem linePoint_im (t : ℝ) : (1 / 2 + (t : ℂ) * I).im = t := by simp

theorem linePoint_ne_zero (t : ℝ) : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [linePoint_re] at this
  norm_num at this

theorem linePoint_ne_one (t : ℝ) : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [linePoint_re] at this
  norm_num at this

/-! ### Λ is real on the critical line -/

/-- The completed zeta `Λ` is real-valued on the critical line `Re s = 1/2`. -/
theorem completedRiemannZeta_real_on_critical_line {s : ℂ} (hs : s.re = 1 / 2) :
    (completedRiemannZeta s).im = 0 := by
  have hline : (1 : ℂ) - s = conj s := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hs]; norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring
  rw [completedRiemannZeta_eq, hline, Complex.sub_im, Complex.sub_im,
    completedZeta₀_real_on_critical_line hs]
  have h1 : (1 / conj s).im = -(1 / s).im := by
    rw [show (1 : ℂ) / conj s = conj (1 / s) by rw [map_div₀, map_one], Complex.conj_im]
  rw [h1]; ring

/-! ### The real-valued slice -/

/-- The real critical-line slice `Z(t) = Re Λ(1/2 + it)`. -/
def Zslice (t : ℝ) : ℝ := (completedRiemannZeta (1 / 2 + (t : ℂ) * I)).re

/-- On the line the complex value is the real cast of the slice. -/
theorem completedRiemannZeta_critical_eq_ofReal (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I) = (Zslice t : ℂ) := by
  apply Complex.ext
  · simp [Zslice]
  · rw [Complex.ofReal_im]
    exact completedRiemannZeta_real_on_critical_line (linePoint_re t)

/-- The real slice is continuous (`Λ` is differentiable along the line, which avoids
the poles at `0` and `1`). -/
theorem continuous_Zslice : Continuous Zslice := by
  have hcont : Continuous (fun t : ℝ => completedRiemannZeta (1 / 2 + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hline_cont : ContinuousAt (fun t : ℝ => (1 / 2 + (t : ℂ) * I)) t := by fun_prop
    have hΛ_cont : ContinuousAt completedRiemannZeta (1 / 2 + (t : ℂ) * I) :=
      (differentiableAt_completedZeta (linePoint_ne_zero t)
        (linePoint_ne_one t)).continuousAt
    exact ContinuousAt.comp (g := completedRiemannZeta)
      (f := fun t : ℝ => (1 / 2 + (t : ℂ) * I)) hΛ_cont hline_cont
  exact Complex.continuous_re.comp hcont

/-! ### Zero detection -/

theorem Zslice_eq_zero_iff (t : ℝ) :
    Zslice t = 0 ↔ completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  rw [completedRiemannZeta_critical_eq_ofReal, Complex.ofReal_eq_zero]

/-- A zero of the real slice is a zero of `ζ` on the critical line. -/
theorem riemannZeta_critical_zero_of_Zslice_zero {t : ℝ} (h : Zslice t = 0) :
    riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hΛ : completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0 := (Zslice_eq_zero_iff t).mp h
  rw [riemannZeta_def_of_ne_zero (linePoint_ne_zero t), hΛ, zero_div]

/-! ### Oscillation: sign changes detect critical-line zeros -/

/-- **Hardy's method (verified).** A sign change of the real slice `Zslice` on an
interval forces a zero of `ζ` strictly inside it, on the critical line. -/
theorem riemannZeta_critical_zero_of_sign_change {a b : ℝ} (hab : a < b)
    (ha : Zslice a < 0) (hb : 0 < Zslice b) :
    ∃ t : ℝ, a < t ∧ t < b ∧ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hsub := intermediate_value_Ioo hab.le continuous_Zslice.continuousOn
  have h0mem : (0 : ℝ) ∈ Set.Ioo (Zslice a) (Zslice b) := ⟨ha, hb⟩
  obtain ⟨t, htmem, hzt⟩ := hsub h0mem
  exact ⟨t, htmem.1, htmem.2, riemannZeta_critical_zero_of_Zslice_zero hzt⟩

/-- Symmetric sign-change form (`Zslice a > 0 > Zslice b`). -/
theorem riemannZeta_critical_zero_of_sign_change' {a b : ℝ} (hab : a < b)
    (ha : 0 < Zslice a) (hb : Zslice b < 0) :
    ∃ t : ℝ, a < t ∧ t < b ∧ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  have hsub := intermediate_value_Ioo' hab.le continuous_Zslice.continuousOn
  have h0mem : (0 : ℝ) ∈ Set.Ioo (Zslice b) (Zslice a) := ⟨hb, ha⟩
  obtain ⟨t, htmem, hzt⟩ := hsub h0mem
  exact ⟨t, htmem.1, htmem.2, riemannZeta_critical_zero_of_Zslice_zero hzt⟩

end Reinmann
