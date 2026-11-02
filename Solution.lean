/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import XiRectangle.Final

/-!
# Solution

The proof lives in the vendored `Reinmann` and `XiRectangle` libraries
(from `sciencenerd-des/reinmann`, ported to Lean's module system). This file
restates the two Challenge theorems verbatim and closes them with the
library's `rectangle_nonzero` (a 44-tile certified covering of the
rectangle by interval Taylor models, every rounding step checked by rational
arithmetic in the kernel) and the elementary implication
`ζ(s) = 0 → ξ(s) = 0` in the open strip.
-/

public section

namespace ReinmannPalomar

/-- Riemann's entire `ξ(s) = 1/2 + s(s-1)/2 · Λ₀(s)` has no zero in the closed
rectangle `0 ≤ Re s ≤ 1`, `|Im s| ≤ 141/10`. -/
theorem xi_ne_zero_low_rectangle (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (hT : |s.im| ≤ 141 / 10) :
    (1 / 2 : ℂ) + s * (s - 1) / 2 * completedRiemannZeta₀ s ≠ 0 :=
  Reinmann.XiRectangle.rectangle_nonzero h0 h1 hT

/-- Mathlib's `riemannZeta` has no zero `s` with `0 < Re s < 1` and
`|Im s| ≤ 141/10`. -/
theorem riemannZeta_ne_zero_low_strip (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hT : |s.im| ≤ 141 / 10) :
    riemannZeta s ≠ 0 := fun hz =>
  Reinmann.XiRectangle.rectangle_nonzero h0.le h1.le hT
    (Reinmann.XiAnnihilator.xi_zero_of_strip_zero hz h0 h1)

end ReinmannPalomar
