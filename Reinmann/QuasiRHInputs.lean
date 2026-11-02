/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.RiemannSpine
public import Reinmann.KnownZeroFreeRegions
public import Reinmann.FinitePFBaseline
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Zero-free half-planes, folded zero angles and finite Pólya-frequency order

This file connects two inputs to the existing reduction chain:

* a fixed zero-free half-plane `ZetaZeroFreeRightOf σ`. With `σ = 7/8` this is the
  claimed quasi-Riemann hypothesis of OpenAI's manuscript *The Quasi-Riemann
  Hypothesis: A Zero-Free Half-Plane Re s > 7/8* (30 September 2026). That claim is
  kernel-checked in an external Lean library as
  `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (toolchain v4.34.1), which is not
  imported here. It is carried as the named proposition
  `QuasiRiemannHypothesisSevenEighths` and is never an axiom.
* the sector route to finite Pólya-frequency order of the folded ξ coefficients
  (Katkova 2007, Theorem B, after Schoenberg 1955). Write `z = (s - 1/2)^2`. A zero
  `1/2 + x + iγ` with `γ ≠ 0` lies at angle `2·arctan(|x|/|γ|)` from the negative
  real axis. `XiFoldedZeroAngleBound m` says this angle is at most `π/(m+1)`, so the
  folded zero avoids the sector `|arg z| < mπ/(m+1)`. The analytic step from that
  zero geometry to `FinitePF XiMomentCoeff m` needs the canonical product, positive
  center value, Schoenberg's polynomial sector theorem and locally uniform limits.
  It is carried as `KatkovaSectorBridge m`.

## Proved here

* `zetaZeroFreeRightOf_half_iff_riemannHypothesis`: zero-freeness to the right of
  `1/2` is RH.
* `riemannHypothesis_iff_of_zeroFreeRightOf`: under a half-plane at `σ`, RH reduces
  to the band `1/2 < Re s ≤ σ`; for `σ = 7/8` this is the narrowed formal gap.
* `abs_re_sub_half_le_of_zeroFreeRightOf`: a half-plane at `σ` confines every
  critical-strip zero to `|Re s - 1/2| ≤ σ - 1/2`, by functional-equation reflection.
* `angleBound_of_strip`, together with the explicit `π` estimates `strip_numeric_43`
  and `strip_numeric_58`: strip width plus first-zero height gives the angle bound.
* `xi_finitePF43_of_classical`: PF₄₃, from the classical strip plus the named inputs.
* `xi_finitePF58_of_quasiRH`: PF₅₈, from the 7/8 half-plane plus the same inputs.
* `forall_angleBound_iff_riemannHypothesis`: the angle bound at **every** order is
  exactly RH. No fixed order is RH-strength, and the unbounded-order statement is.

The order improvement 43 → 58 is a constant improvement, not progress toward RH.
-/

noncomputable section

namespace Reinmann

open Real

/-! ### Zero-free half-planes -/

/-- `ζ` has no zero strictly to the right of `σ`. -/
def ZetaZeroFreeRightOf (σ : ℝ) : Prop :=
  ∀ s : ℂ, σ < s.re → riemannZeta s ≠ 0

/-- The claimed quasi-Riemann hypothesis with exponent `7/8` (OpenAI, 2026; checked
in an external Lean library, unrefereed). A named external input, never an axiom. -/
def QuasiRiemannHypothesisSevenEighths : Prop :=
  ZetaZeroFreeRightOf (7 / 8)

theorem zetaZeroFreeRightOf_mono {σ τ : ℝ} (hστ : σ ≤ τ)
    (h : ZetaZeroFreeRightOf σ) : ZetaZeroFreeRightOf τ :=
  fun s hs => h s (lt_of_le_of_lt hστ hs)

/-- The classical half-plane `Re s > 1` (in fact `Re s ≥ 1`, from Mathlib). -/
theorem zetaZeroFreeRightOf_one : ZetaZeroFreeRightOf 1 :=
  fun s hs => zeroFreeRegion_re_ge_one s hs.le

/-- Zero-freeness to the right of `1/2` is exactly the Riemann Hypothesis. -/
theorem zetaZeroFreeRightOf_half_iff_riemannHypothesis :
    ZetaZeroFreeRightOf (1 / 2) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_rightHalfStripZeroFree (fun s h1 _ => h s h1)
  · intro h s hs
    by_cases h1 : s.re < 1
    · exact rightHalfStripZeroFree_of_riemannHypothesis h s hs h1
    · exact zeroFreeRegion_re_ge_one s (not_lt.mp h1)

/-- Under a half-plane at `σ`, RH is equivalent to zero-freeness of the band
`1/2 < Re s ≤ σ`. -/
theorem riemannHypothesis_iff_of_zeroFreeRightOf {σ : ℝ}
    (h : ZetaZeroFreeRightOf σ) :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ σ → riemannZeta s ≠ 0 := by
  rw [← zetaZeroFreeRightOf_half_iff_riemannHypothesis]
  constructor
  · intro hh s h1 _
    exact hh s h1
  · intro hh s h1
    by_cases h2 : s.re ≤ σ
    · exact hh s h1 h2
    · exact h s (not_le.mp h2)

/-- The narrowed formal gap under the 7/8 half-plane. -/
theorem riemannHypothesis_iff_band_of_quasiRH
    (hq : QuasiRiemannHypothesisSevenEighths) :
    RiemannHypothesis ↔
      ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 7 / 8 → riemannZeta s ≠ 0 :=
  riemannHypothesis_iff_of_zeroFreeRightOf hq

/-! ### Critical-strip zeros and their distance from the line -/

/-- A zero of `ζ` in the open critical strip. -/
def IsCriticalStripZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- Unconditionally, critical-strip zeros satisfy `|Re s - 1/2| ≤ 1/2`. -/
theorem abs_re_sub_half_le_half {s : ℂ} (hs : IsCriticalStripZero s) :
    |s.re - 1 / 2| ≤ 1 / 2 := by
  obtain ⟨-, h0, h1⟩ := hs
  rw [abs_le]
  constructor <;> linarith

/-- A half-plane at `σ ≥ 1/2` confines strip zeros to `|Re s - 1/2| ≤ σ - 1/2`. The
left side uses the reflection `s ↦ 1 - s` of strip zeros. -/
theorem abs_re_sub_half_le_of_zeroFreeRightOf {σ : ℝ}
    (h : ZetaZeroFreeRightOf σ) {s : ℂ} (hs : IsCriticalStripZero s) :
    |s.re - 1 / 2| ≤ σ - 1 / 2 := by
  obtain ⟨hz, h0, h1⟩ := hs
  have hle : s.re ≤ σ := not_lt.mp (fun hlt => h s hlt hz)
  have hrefl : riemannZeta (1 - s) = 0 := strip_zero_reflects h0 h1 hz
  have hle' : (1 - s).re ≤ σ := not_lt.mp (fun hlt => h (1 - s) hlt hrefl)
  rw [Complex.sub_re, Complex.one_re] at hle'
  rw [abs_le]
  constructor <;> linarith

/-- Under the 7/8 half-plane, strip zeros satisfy `|Re s - 1/2| ≤ 3/8`. -/
theorem abs_re_sub_half_le_of_quasiRH (hq : QuasiRiemannHypothesisSevenEighths)
    {s : ℂ} (hs : IsCriticalStripZero s) : |s.re - 1 / 2| ≤ 3 / 8 := by
  have := abs_re_sub_half_le_of_zeroFreeRightOf hq hs
  linarith

/-! ### Folded-zero angles -/

/-- The half-angle `θ_m = π / (2(m+1))` of the excluded neighbourhood of the
negative axis in Schoenberg–Katkova Theorem B. -/
def pfHalfAngle (m : ℕ) : ℝ := π / (2 * ((m : ℝ) + 1))

theorem pfHalfAngle_pos (m : ℕ) : 0 < pfHalfAngle m := by
  unfold pfHalfAngle
  positivity

theorem pfHalfAngle_le_quarter {m : ℕ} (hm : 0 < m) : pfHalfAngle m ≤ π / 4 := by
  unfold pfHalfAngle
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  apply div_le_div_of_nonneg_left pi_pos.le (by norm_num)
  linarith

theorem pfHalfAngle_lt_half_pi {m : ℕ} (hm : 0 < m) : pfHalfAngle m < π / 2 := by
  have := pfHalfAngle_le_quarter hm
  linarith [pi_pos]

/-- Angle bound of order `m` for the folded zeros of `ξ`. For a zero
`1/2 + x + iγ`, `|x| ≤ |γ| · tan θ_m` is equivalent, when `γ ≠ 0`, to
`2·arctan(|x|/|γ|) ≤ π/(m+1)`: the folded zero `(x + iγ)^2` lies outside the open
sector `|arg z| < mπ/(m+1)`. -/
def XiFoldedZeroAngleBound (m : ℕ) : Prop :=
  ∀ s : ℂ, IsCriticalStripZero s → |s.re - 1 / 2| ≤ |s.im| * tan (pfHalfAngle m)

/-- Named classical input: no critical-strip zero has ordinate below `γ₀`. For
`γ₀ = 141/10` this is the classical fact that the lowest zero has ordinate
`14.1347…`. Not formalized here. -/
def ZetaNoLowStripZero (γ₀ : ℝ) : Prop :=
  ∀ s : ℂ, IsCriticalStripZero s → γ₀ ≤ |s.im|

/-- Named classical bridge (Katkova 2007, Theorem B, after Schoenberg 1955): the
order-`m` angle bound for the folded zeros gives PF of order `m` for the folded ξ
coefficients. It requires the Hadamard canonical product of `ξ(1/2 + √z)`, the
positive center value, Schoenberg's polynomial sector theorem and closure under
locally uniform limits. Not formalized; never an axiom. -/
def KatkovaSectorBridge (m : ℕ) : Prop :=
  XiFoldedZeroAngleBound m → FinitePF XiMomentCoeff m

/-- Strip half-width `w` plus first-zero height `γ₀` gives the order-`m` angle bound
whenever `w ≤ γ₀ θ_m`, using `θ < tan θ` on `(0, π/2)`. -/
theorem angleBound_of_strip {w γ₀ : ℝ} {m : ℕ} (hm : 0 < m) (hγ₀ : 0 < γ₀)
    (hlow : ZetaNoLowStripZero γ₀)
    (hstrip : ∀ s : ℂ, IsCriticalStripZero s → |s.re - 1 / 2| ≤ w)
    (hnum : w ≤ γ₀ * pfHalfAngle m) : XiFoldedZeroAngleBound m := by
  intro s hs
  have hθ := pfHalfAngle_pos m
  have htan : pfHalfAngle m < tan (pfHalfAngle m) :=
    lt_tan hθ (pfHalfAngle_lt_half_pi hm)
  have him : γ₀ ≤ |s.im| := hlow s hs
  calc |s.re - 1 / 2| ≤ w := hstrip s hs
    _ ≤ γ₀ * pfHalfAngle m := hnum
    _ ≤ |s.im| * tan (pfHalfAngle m) :=
        mul_le_mul him htan.le hθ.le (hγ₀.le.trans him)

/-- Numerical check for order 43: `1/2 ≤ (141/10) · π/88`, i.e. `π ≥ 3.1206…`. -/
theorem strip_numeric_43 : (1 / 2 : ℝ) ≤ (141 / 10) * pfHalfAngle 43 := by
  unfold pfHalfAngle
  have := pi_gt_d4
  norm_num
  linarith

/-- Numerical check for order 58: `3/8 ≤ (141/10) · π/118`, i.e. `π ≥ 3.1383…`. -/
theorem strip_numeric_58 : (3 / 8 : ℝ) ≤ (141 / 10) * pfHalfAngle 58 := by
  unfold pfHalfAngle
  have := pi_gt_d4
  norm_num
  linarith

/-- PF₄₃ for the folded ξ coefficients, from the classical strip, the first-zero
height and the named sector bridge. This is the repository's conservative
classical baseline. -/
theorem xi_finitePF43_of_classical (hlow : ZetaNoLowStripZero (141 / 10))
    (hB : KatkovaSectorBridge 43) : FinitePF XiMomentCoeff 43 :=
  hB (angleBound_of_strip (by norm_num) (by norm_num) hlow
    (fun _ hs => abs_re_sub_half_le_half hs) strip_numeric_43)

/-- PF₅₈ for the folded ξ coefficients under the 7/8 half-plane. -/
theorem xi_finitePF58_of_quasiRH (hq : QuasiRiemannHypothesisSevenEighths)
    (hlow : ZetaNoLowStripZero (141 / 10)) (hB : KatkovaSectorBridge 58) :
    FinitePF XiMomentCoeff 58 :=
  hB (angleBound_of_strip (by norm_num) (by norm_num) hlow
    (fun _ hs => abs_re_sub_half_le_of_quasiRH hq hs) strip_numeric_58)

/-- The order-58 baseline contains the order-43 baseline. -/
theorem xi_finitePF43_of_quasiRH (hq : QuasiRiemannHypothesisSevenEighths)
    (hlow : ZetaNoLowStripZero (141 / 10)) (hB : KatkovaSectorBridge 58) :
    FinitePF XiMomentCoeff 43 :=
  finitePF_mono (xi_finitePF58_of_quasiRH hq hlow hB) (by norm_num)

/-! ### Every order at once is exactly RH -/

/-- `tan θ ≤ 2θ` on `[0, π/4]`. -/
theorem tan_le_two_mul_of_le_quarter {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 4) :
    tan θ ≤ 2 * θ := by
  have hpi := pi_lt_d2
  have hθ : θ ≤ 4 / 5 := by linarith
  have hcos : 1 / 2 ≤ cos θ := by
    have := one_sub_sq_div_two_le_cos (x := θ)
    nlinarith
  have hcpos : 0 < cos θ := by linarith
  rw [tan_eq_sin_div_cos, div_le_iff₀ hcpos]
  have := sin_le h0
  nlinarith

/-- RH gives the angle bound at every order: every strip zero has `x = 0`. -/
theorem angleBound_of_riemannHypothesis (hrh : RiemannHypothesis) {m : ℕ}
    (hm : 0 < m) : XiFoldedZeroAngleBound m := by
  intro s hs
  obtain ⟨hz, h0, h1⟩ := hs
  have hre : s.re = 1 / 2 := rh_implies_all_zeros_at_half hrh s hz h0 h1
  have htan : 0 ≤ tan (pfHalfAngle m) :=
    tan_nonneg_of_nonneg_of_le_pi_div_two (pfHalfAngle_pos m).le
      (pfHalfAngle_lt_half_pi hm).le
  rw [hre, sub_self, abs_zero]
  exact mul_nonneg (abs_nonneg _) htan

/-- The angle bound at every order forces every strip zero onto the line. -/
theorem riemannHypothesis_of_forall_angleBound
    (h : ∀ m : ℕ, 0 < m → XiFoldedZeroAngleBound m) : RiemannHypothesis := by
  rw [← zetaZeroFreeRightOf_half_iff_riemannHypothesis]
  intro s hs hz
  by_cases h1 : s.re < 1
  swap
  · exact zeroFreeRegion_re_ge_one s (not_lt.mp h1) hz
  have hstrip : IsCriticalStripZero s := ⟨hz, by linarith, h1⟩
  set x := |s.re - 1 / 2| with hx
  have hxpos : 0 < x := by
    rw [hx, abs_pos]
    linarith
  set g := |s.im|
  -- Choose `m` with `g·π < (m+1)·x`.
  obtain ⟨n, hn⟩ := exists_nat_gt (g * π / x)
  have hm : 0 < n + 1 := Nat.succ_pos n
  have hbound := h (n + 1) hm s hstrip
  have hθ0 := (pfHalfAngle_pos (n + 1)).le
  have hθ1 := pfHalfAngle_le_quarter hm
  have htan := tan_le_two_mul_of_le_quarter hθ0 hθ1
  have hg : 0 ≤ g := abs_nonneg _
  -- `x ≤ g · tan θ ≤ g · 2θ = g · π/(n+2)`.
  have hchain : x ≤ g * (2 * pfHalfAngle (n + 1)) :=
    hbound.trans (mul_le_mul_of_nonneg_left htan hg)
  have heq : 2 * pfHalfAngle (n + 1) = π / ((n : ℝ) + 2) := by
    unfold pfHalfAngle
    push_cast
    field_simp
    ring
  rw [heq] at hchain
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hlt : g * π < ((n : ℝ) + 2) * x := by
    have := (div_lt_iff₀ hxpos).mp hn
    nlinarith
  rw [← mul_div_assoc] at hchain
  have : x * ((n : ℝ) + 2) ≤ g * π := (le_div_iff₀ hn2).mp hchain
  linarith

/-- The folded-zero angle bound at every positive order is exactly RH. Each fixed
order follows from finitely many zero locations; all orders together are
RH-strength. -/
theorem forall_angleBound_iff_riemannHypothesis :
    (∀ m : ℕ, 0 < m → XiFoldedZeroAngleBound m) ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_forall_angleBound,
    fun hrh _ hm => angleBound_of_riemannHypothesis hrh hm⟩

end Reinmann
