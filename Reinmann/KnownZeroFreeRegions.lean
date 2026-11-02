/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.RiemannSpine
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Nonvanishing

@[expose] public section

/-!
# Known Zero-Free Regions for Riemann Zeta

This file formalizes what IS known about zero-free regions of the Riemann zeta function,
which are weaker than RH but still significant results.

## Main Results

* `zeroFreeRegion_re_ge_one`: No zeros for Re(s) ≥ 1 (classical result, in Mathlib)
* Properties of the "classical" zero-free region near Re(s) = 1

## Classical Results

The following are known (but not all formalized here):
1. No zeros for Re(s) ≥ 1 (de la Vallée Poussin, 1896)
2. No zeros for Re(s) ≥ 1 - c/log(|Im(s)|) for some c > 0
3. At most one real zero in (0,1) (if it exists, called Siegel zero)
4. Zero density estimates: N(σ, T) ≪ T^(c(1-σ)) for σ > 1/2

These results are significantly weaker than RH but represent major achievements.

-/

noncomputable section

namespace Reinmann

/-! ### Known Zero-Free Region: Re(s) ≥ 1 -/

/-- The classical zero-free region: no zeros for Re(s) ≥ 1.
    This is already in Mathlib. -/
theorem zeroFreeRegion_re_ge_one (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-! ### Properties That Would Follow from RH -/

/-- If RH holds, then all nontrivial zeros have Re(s) = 1/2 exactly. -/
theorem rh_implies_all_zeros_at_half (hrh : RiemannHypothesis) (s : ℂ)
    (hz : riemannZeta s = 0) (hpos : 0 < s.re) (hlt : s.re < 1) :
    s.re = 1/2 := by
  -- RH says no zeros with 1/2 < Re(s) < 1
  by_contra hneq
  -- Either s.re < 1/2 or s.re > 1/2
  cases lt_or_gt_of_ne hneq with
  | inl hless =>
    -- If s.re < 1/2, then by functional equation, 1-s has Re > 1/2
    have h_reflect : riemannZeta (1 - s) = 0 := strip_zero_reflects hpos hlt hz
    have h_reflect_re : 1/2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have h_reflect_lt : (1 - s).re < 1 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    -- But RH says no zeros in right half
    rw [riemannHypothesis_iff_rightHalfStripZeroFree] at hrh
    exact hrh (1 - s) h_reflect_re h_reflect_lt h_reflect
  | inr hgreater =>
    -- If s.re > 1/2, this directly contradicts RH
    rw [riemannHypothesis_iff_rightHalfStripZeroFree] at hrh
    exact hrh s hgreater hlt hz

/-- If RH holds, the strip (0, 1) contains zeros only on the critical line. -/
theorem rh_implies_strip_zeros_on_line (hrh : RiemannHypothesis) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) (hz : riemannZeta s = 0) :
    OnCriticalLine s :=
  rh_implies_all_zeros_at_half hrh s hz hpos hlt

/-! ### Contrapositive Formulations -/

/-- If there exists a zero off the critical line in the strip, then RH is false. -/
theorem offLine_strip_zero_refutes_rh :
    (∃ s : ℂ, 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1/2 ∧ riemannZeta s = 0) →
    ¬RiemannHypothesis := by
  intro ⟨s, hpos, hlt, hneq, hz⟩ hrh
  have : s.re = 1/2 := rh_implies_all_zeros_at_half hrh s hz hpos hlt
  exact hneq this

/-- Finding any zero with Re(s) > 1/2 in the strip would refute RH. -/
theorem rightHalf_strip_zero_refutes_rh :
    (∃ s : ℂ, 1/2 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0) →
    ¬RiemannHypothesis := by
  intro ⟨s, hhalf, hlt, hz⟩ hrh
  have : s.re = 1/2 := rh_implies_all_zeros_at_half hrh s hz (by linarith) hlt
  linarith

/-! ### What We Know vs What We Need -/

/-- We know: no zeros for Re(s) ≥ 1.
    We need to prove: no zeros for 1/2 < Re(s) < 1.
    The gap is the open half-strip. -/
theorem rh_gap_is_open_half_strip :
    RiemannHypothesis ↔
    (∀ s : ℂ, 1/2 < s.re → s.re < 1 → riemannZeta s ≠ 0) :=
  riemannHypothesis_iff_rightHalfStripZeroFree

/-- The classical result gets us to Re(s) ≥ 1.
    RH would extend this to Re(s) ≥ 1/2.
    The difference is the "critical strip gap". -/
theorem critical_strip_gap_characterization :
    RiemannHypothesis ↔ ¬∃ s : ℂ, 1/2 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 := by
  rw [riemannHypothesis_iff_rightHalfStripZeroFree]
  simp only [RightHalfStripZeroFree]
  push Not
  rfl

/-! ### Density and Distribution Properties -/

/-- The functional equation forces pairing of zeros regardless of RH.
    If s is a zero in the strip, then 1-s is also a zero. -/
theorem functional_equation_pairs_zeros (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 :=
  strip_zero_reflects hpos hlt hz

/-- Under RH, the functional equation pairing becomes symmetric about the critical line.
    Since all zeros have Re(s) = 1/2, the pair 1-s has Re(1-s) = 1/2 as well. -/
theorem rh_implies_symmetric_pairing :
    RiemannHypothesis →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
    s.re = 1/2 ∧ (1 - s).re = 1/2 := by
  intro hrh s hpos hlt hz
  have hs_line : s.re = 1/2 := rh_implies_all_zeros_at_half hrh s hz hpos hlt
  constructor
  · exact hs_line
  · simp only [Complex.sub_re, Complex.one_re]
    linarith

end Reinmann
