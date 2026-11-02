/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.RiemannSpine
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-!
# Reflection Symmetry of the Completed Zeta Derivative Λ₀′

## Motivation (de Branges / Hermite–Biehler route)

The de Branges / Hermite–Biehler picture is cleanest on the *completed* zeta, which
is entire and carries the exact functional-equation symmetry `Λ₀(1-s) = Λ₀(s)`
(`completedRiemannZeta₀_one_sub`). Differentiating this symmetry gives an
unconditional anti-symmetry of the derivative across the critical line `Re = 1/2`:

* `deriv_completedZeta₀_one_sub`: `Λ₀′(1-s) = -Λ₀′(s)`;
* `deriv_completedZeta₀_half`: `Λ₀′(1/2) = 0` (the completed zeta has a critical
  point exactly at the center of symmetry).

Both are entire-function facts, unconditional, and not equivalent to RH. They are
the reflection analogue of the conjugation symmetry `ζ′(s̄) = ζ̄′(s)` and pair
`Λ₀′`-zeros across the critical line: `Λ₀′(s) = 0 ⇔ Λ₀′(1-s) = 0`.
-/

noncomputable section

open Complex

namespace Reinmann

/-- **Reflection anti-symmetry of Λ₀′.** Differentiating the completed
functional equation `Λ₀(1-s) = Λ₀(s)` gives `Λ₀′(1-s) = -Λ₀′(s)`. -/
theorem deriv_completedZeta₀_one_sub (s : ℂ) :
    deriv completedRiemannZeta₀ (1 - s) = -deriv completedRiemannZeta₀ s := by
  have hΛ : HasDerivAt completedRiemannZeta₀
      (deriv completedRiemannZeta₀ (1 - s)) (1 - s) :=
    (differentiable_completedZeta₀ (1 - s)).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using! (hasDerivAt_id s).const_sub 1
  have hcomp := hΛ.comp s hlin
  rw [show (completedRiemannZeta₀ ∘ fun z : ℂ => 1 - z) = completedRiemannZeta₀ by
        funext z; simp [Function.comp, completedRiemannZeta₀_one_sub z]] at hcomp
  have hd : HasDerivAt completedRiemannZeta₀ (deriv completedRiemannZeta₀ s) s :=
    (differentiable_completedZeta₀ s).hasDerivAt
  have huniq := hcomp.unique hd
  linear_combination -huniq

/-- **Critical point at the center.** `Λ₀′(1/2) = 0`. -/
theorem deriv_completedZeta₀_half : deriv completedRiemannZeta₀ (1 / 2 : ℂ) = 0 := by
  have h := deriv_completedZeta₀_one_sub (1 / 2 : ℂ)
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h
  -- h : Λ₀′(1/2) = -Λ₀′(1/2)
  have h2 : (2 : ℂ) * deriv completedRiemannZeta₀ (1 / 2 : ℂ) = 0 := by
    linear_combination h
  simpa using! h2

/-- **Λ₀′ zeros are paired across the critical line.** -/
theorem deriv_completedZeta₀_zero_one_sub {s : ℂ}
    (h : deriv completedRiemannZeta₀ s = 0) :
    deriv completedRiemannZeta₀ (1 - s) = 0 := by
  rw [deriv_completedZeta₀_one_sub, h, neg_zero]

end Reinmann
