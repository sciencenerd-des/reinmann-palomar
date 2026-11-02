/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal, OpenAI Codex
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-!
# Riemann Hypothesis proof spine

This file records a Lean-checked reduction toward mathlib's
`RiemannHypothesis` target. It verifies known supporting facts from mathlib and
isolates the remaining obligations without asserting that those obligations are
proved.
-/

noncomputable section

namespace Reinmann

/--
One of the standard negative even zeros of the Riemann zeta function.
-/
def IsTrivialZetaZero (s : Complex) : Prop :=
  ∃ n : Nat, s = (-2 : Complex) * ((n : Complex) + 1)

/--
The critical line in the complex plane.
-/
def OnCriticalLine (s : Complex) : Prop :=
  s.re = 1 / 2

/--
The central remaining obligation after using existing mathlib facts.
-/
structure CriticalStripObligations where
  strip_zero_on_line :
    ∀ s : Complex, 0 < s.re -> s.re < 1 -> riemannZeta s = 0 -> OnCriticalLine s

/--
A one-sided zero-free formulation for the open right half of the critical
strip. Because strip zeros reflect under `s ↦ 1 - s`, this is enough to imply
the full critical-strip obligation.
-/
def RightHalfStripZeroFree : Prop :=
  ∀ s : Complex, 1 / 2 < s.re -> s.re < 1 -> riemannZeta s ≠ 0

/--
A concrete counterexample target for the one-sided zero-free formulation.
-/
def RightHalfStripCounterexample (s : Complex) : Prop :=
  1 / 2 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0

/--
The reflected companion shape of a right-half strip counterexample.
-/
def LeftHalfStripCounterexample (s : Complex) : Prop :=
  0 < s.re ∧ s.re < 1 / 2 ∧ riemannZeta s = 0

/--
The left-half counterpart of `RightHalfStripZeroFree`.
-/
def LeftHalfStripZeroFree : Prop :=
  ∀ s : Complex, 0 < s.re -> s.re < 1 / 2 -> riemannZeta s ≠ 0

/--
A zero in the open critical strip but not on the critical line.
-/
def CriticalStripOffLineZero (s : Complex) : Prop :=
  0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 ∧ s.re ≠ 1 / 2

/--
The geometric involution `s ↦ 1 - conjugate s`. Its fixed points are exactly
the critical line. Mapping zeta zeros through this involution would additionally
require conjugation symmetry of `riemannZeta`, which is not asserted here.
-/
def zetaInvolution (s : Complex) : Complex :=
  1 - starRingEnd Complex s

/--
The geometric involution has order two.
-/
theorem zetaInvolution_involutive (s : Complex) :
    zetaInvolution (zetaInvolution s) = s := by
  simp only [zetaInvolution, map_sub, map_one]
  rw [Complex.conj_conj]
  ring

/--
The geometric involution preserves the open critical strip.
-/
theorem zetaInvolution_preserves_strip {s : Complex}
    (h : 0 < s.re ∧ s.re < 1) :
    0 < (zetaInvolution s).re ∧ (zetaInvolution s).re < 1 := by
  simp only [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/--
Fixed points of the geometric involution have real part `1 / 2`.
-/
theorem zetaInvolution_fixed_iff_re_eq_half (s : Complex) :
    zetaInvolution s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre : (zetaInvolution s).re = s.re := by rw [h]
    simp only [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp only [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp only [zetaInvolution, Complex.sub_im, Complex.one_im, Complex.conj_im,
        zero_sub, neg_neg]

/--
Fixed points of the geometric involution are exactly points on the critical
line.
-/
theorem zetaInvolution_fixed_iff_onCriticalLine (s : Complex) :
    zetaInvolution s = s ↔ OnCriticalLine s := by
  rw [zetaInvolution_fixed_iff_re_eq_half, OnCriticalLine]

/--
A point away from the critical line is not fixed by the geometric involution.
-/
theorem zetaInvolution_not_fixed_if_not_onCriticalLine {s : Complex}
    (h : ¬ OnCriticalLine s) : zetaInvolution s ≠ s := by
  intro hfixed
  exact h ((zetaInvolution_fixed_iff_onCriticalLine s).mp hfixed)

/--
Points in the right half of the critical strip are not fixed by the geometric
involution.
-/
theorem zetaInvolution_not_fixed_in_right_half {s : Complex}
    (hhalf : 1 / 2 < s.re) : zetaInvolution s ≠ s := by
  apply zetaInvolution_not_fixed_if_not_onCriticalLine
  intro hline
  simp only [OnCriticalLine] at hline
  linarith

/--
The geometric involution swaps the left and right open half-strips.
-/
theorem zetaInvolution_left_half_iff_image_right_half {s : Complex} :
    s.re < 1 / 2 ↔ 1 / 2 < (zetaInvolution s).re := by
  simp only [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]
  constructor <;> intro h <;> linarith

/--
The image of a point in the right half lies in the left half.
-/
theorem zetaInvolution_image_right_half_in_left {s : Complex}
    (hhalf : 1 / 2 < s.re) :
    (zetaInvolution s).re < 1 / 2 := by
  simp only [zetaInvolution, Complex.sub_re, Complex.one_re, Complex.conj_re]
  linarith

/--
Mathlib already proves that the Riemann zeta function has no zeros on
`re s >= 1`.
-/
theorem no_zeta_zeros_on_or_right_of_one {s : Complex}
    (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/--
Mathlib already proves the standard negative even zeros.
-/
theorem trivial_negative_even_zeta_zero (n : Nat) :
    riemannZeta ((-2 : Complex) * ((n : Complex) + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/--
A point strictly to the right of the critical line cannot be one of the
standard negative even zeros.
-/
theorem not_trivial_of_re_gt_half {s : Complex}
    (hs : (1 / 2 : Real) < s.re) : ¬ IsTrivialZetaZero s := by
  intro htrivial
  rcases htrivial with ⟨n, hs_eq⟩
  have hre := congrArg Complex.re hs_eq
  norm_num [IsTrivialZetaZero, Complex.mul_re, Complex.add_re, Complex.natCast_re] at hre
  have hn_nonneg : 0 ≤ (n : Real) := Nat.cast_nonneg n
  linarith

/--
The zeta value at zero is not a zero. Mathlib records `ζ(0) = -1 / 2`.
-/
theorem riemannZeta_zero_ne_zero : riemannZeta (0 : Complex) ≠ 0 := by
  rw [riemannZeta_zero]
  norm_num

/--
A point with positive real part is not a nonpositive integer.
-/
theorem ne_neg_nat_of_re_pos {s : Complex} (hs : 0 < s.re) :
    ∀ n : Nat, s ≠ -(n : Complex) := by
  intro n hs_eq
  have hre := congrArg Complex.re hs_eq
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hn_nonneg : 0 ≤ (n : Real) := Nat.cast_nonneg n
  linarith

/--
A point with real part strictly less than one is not `1`.
-/
theorem ne_one_of_re_lt_one {s : Complex} (hs : s.re < 1) : s ≠ 1 := by
  intro hs_eq
  have hre := congrArg Complex.re hs_eq
  simp only [Complex.one_re] at hre
  linarith

/--
If `s` is on or left of the imaginary axis, then `1 - s` is not a
nonpositive integer. This is the side condition needed to apply
`riemannZeta_one_sub` to `1 - s`.
-/
theorem one_sub_ne_neg_nat_of_re_nonpos {s : Complex} (hs : s.re ≤ 0) :
    ∀ n : Nat, 1 - s ≠ -(n : Complex) := by
  intro n hn
  have hre := congrArg Complex.re hn
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re] at hre
  norm_num at hre
  have hn_nonneg : 0 ≤ (n : Real) := Nat.cast_nonneg n
  linarith

/--
Analytic reduction for the left half-plane: any zeta zero with `s.re <= 0`
forces the cosine factor in the functional equation to vanish.
-/
theorem cos_factor_zero_of_left_zero {s : Complex}
    (hs : s.re ≤ 0) (hz : riemannZeta s = 0) :
    Complex.cos (Real.pi * (1 - s) / 2) = 0 := by
  by_cases hs0 : s = 0
  · subst s
    exact False.elim (riemannZeta_zero_ne_zero hz)
  · have honeSub_re : 1 ≤ (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hzeta_one_sub : riemannZeta (1 - s) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re honeSub_re
    have hnot_neg_nat : ∀ n : Nat, 1 - s ≠ -(n : Complex) :=
      one_sub_ne_neg_nat_of_re_nonpos hs
    have honeSub_ne_one : 1 - s ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    have hfe := riemannZeta_one_sub (s := 1 - s) hnot_neg_nat honeSub_ne_one
    have hfe_norm : riemannZeta s =
        2 * (2 * ↑Real.pi) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
          Complex.cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) := by
      simpa using! hfe
    have hprod : 2 * (2 * ↑Real.pi) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
        Complex.cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s) = 0 := by
      rw [hz] at hfe_norm
      simpa using! hfe_norm.symm
    rcases mul_eq_zero.mp hprod with hprod_nozeta | hzeta
    · rcases mul_eq_zero.mp hprod_nozeta with hprod_nocos | hcos
      · rcases mul_eq_zero.mp hprod_nocos with hprod_nogamma | hgamma
        · rcases mul_eq_zero.mp hprod_nogamma with htwo | hpow
          · norm_num at htwo
          · have hbase : (2 * (↑Real.pi : Complex)) ≠ 0 := by
              norm_num [Real.pi_ne_zero]
            have hpow_ne : (2 * (↑Real.pi : Complex)) ^ (-(1 - s)) ≠ 0 := by
              rw [Ne, Complex.cpow_eq_zero_iff]
              exact not_and_of_not_left _ hbase
            exact False.elim (hpow_ne hpow)
        · have hgamma_ne : Complex.Gamma (1 - s) ≠ 0 :=
            Complex.Gamma_ne_zero hnot_neg_nat
          exact False.elim (hgamma_ne hgamma)
      · exact hcos
    · exact False.elim (hzeta_one_sub hzeta)

/--
Zeros of the Riemann zeta function on or left of the imaginary axis are exactly
the standard negative even zeros.
-/
theorem left_of_strip_zero_is_trivial {s : Complex}
    (hs : s.re ≤ 0) (hz : riemannZeta s = 0) : IsTrivialZetaZero s := by
  have hcos := cos_factor_zero_of_left_zero hs hz
  rcases Complex.cos_eq_zero_iff.mp hcos with ⟨k, hk⟩
  have hpi : (↑Real.pi : Complex) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hpi2 : (↑Real.pi : Complex) / 2 ≠ 0 :=
    div_ne_zero hpi two_ne_zero
  have hk_scaled : ((↑Real.pi : Complex) / 2) * (1 - s) =
      ((↑Real.pi : Complex) / 2) * (2 * (k : Complex) + 1) := by
    linear_combination hk
  have hraw : 1 - s = 2 * (k : Complex) + 1 :=
    mul_left_cancel₀ hpi2 hk_scaled
  have hsk : s = -2 * (k : Complex) := by
    linear_combination -hraw
  have hk_nonneg : 0 ≤ k := by
    have hlecast : (-2 * (k : Complex)).re ≤ 0 := by
      simpa [hsk] using! hs
    norm_num [Complex.mul_re, Complex.neg_re, Complex.intCast_re] at hlecast ⊢
    linarith
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have hs0 : s = 0 := by
      simp [hsk, hk0]
    have hz_at_zero : riemannZeta (0 : Complex) = 0 := by
      simpa [hs0] using! hz
    exact riemannZeta_zero_ne_zero hz_at_zero
  have hk_pos : 0 < k := lt_of_le_of_ne hk_nonneg (Ne.symm hk_ne_zero)
  obtain ⟨n, hkn⟩ : ∃ n : Nat, (k : Complex) = (n : Complex) + 1 := by
    refine ⟨k.toNat - 1, ?_⟩
    have hknat : (k.toNat : Int) = k :=
      Int.toNat_of_nonneg (le_of_lt hk_pos)
    have hknat_ne_zero : k.toNat ≠ 0 := by
      intro hzero
      have hk_le_zero : k ≤ 0 := Int.toNat_eq_zero.mp hzero
      linarith
    have hsucc : k.toNat - 1 + 1 = k.toNat := by omega
    have hsucc_int : ((k.toNat - 1 + 1 : Nat) : Int) = k := by
      rw [hsucc, hknat]
    have hcast : ((k.toNat - 1 : Nat) : Int) + 1 = k := by
      norm_num at hsucc_int ⊢
      exact hsucc_int
    exact_mod_cast hcast.symm
  refine ⟨n, ?_⟩
  rw [hsk, hkn]

/--
Reflection across the critical line preserves the open critical strip.
-/
theorem reflected_point_in_strip {s : Complex}
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    0 < (1 - s).re ∧ (1 - s).re < 1 := by
  constructor
  · rw [Complex.sub_re, Complex.one_re]
    linarith
  · rw [Complex.sub_re, Complex.one_re]
    linarith

/--
Inside the critical strip, a zeta zero reflects to another zeta zero under
`s ↦ 1 - s`.
-/
theorem strip_zero_reflects {s : Complex}
    (hpos : 0 < s.re) (hlt : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have hnot_neg_nat : ∀ n : Nat, s ≠ -(n : Complex) :=
    ne_neg_nat_of_re_pos hpos
  have hs_ne_one : s ≠ 1 :=
    ne_one_of_re_lt_one hlt
  have hfe := riemannZeta_one_sub (s := s) hnot_neg_nat hs_ne_one
  rw [hz] at hfe
  simpa using! hfe

/--
The non-zeta prefactor in the functional equation is nonzero throughout the
open critical strip.
-/
theorem functionalEquation_prefactor_ne_zero_in_strip {s : Complex}
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    2 * (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (↑Real.pi * s / 2) ≠ 0 := by
  have hnot_neg_nat : ∀ n : Nat, s ≠ -(n : Complex) :=
    ne_neg_nat_of_re_pos hpos
  have hbase : (2 * (↑Real.pi : Complex)) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hpow_ne : (2 * (↑Real.pi : Complex)) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact not_and_of_not_left _ hbase
  have hgamma_ne : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero hnot_neg_nat
  have hcos_ne : Complex.cos (↑Real.pi * s / 2) ≠ 0 := by
    intro hcos
    rcases Complex.cos_eq_zero_iff.mp hcos with ⟨k, hk⟩
    have hpi : (↑Real.pi : Complex) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hpi2 : (↑Real.pi : Complex) / 2 ≠ 0 :=
      div_ne_zero hpi two_ne_zero
    have hk_scaled : ((↑Real.pi : Complex) / 2) * s =
        ((↑Real.pi : Complex) / 2) * (2 * (k : Complex) + 1) := by
      linear_combination hk
    have hs_eq : s = 2 * (k : Complex) + 1 :=
      mul_left_cancel₀ hpi2 hk_scaled
    have hre : s.re = (2 * (k : Complex) + 1).re := by
      rw [hs_eq]
    norm_num [Complex.mul_re, Complex.add_re, Complex.intCast_re] at hre
    have hk_lt : (2 * k + 1 : Int) < 1 := by
      exact_mod_cast (by linarith : (2 * (k : Real) + 1) < 1)
    have hk_pos : 0 < (2 * k + 1 : Int) := by
      exact_mod_cast (by linarith : (0 : Real) < 2 * (k : Real) + 1)
    omega
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero two_ne_zero hpow_ne) hgamma_ne)
    hcos_ne

/--
Inside the critical strip, zerohood is equivalent for `s` and its reflection
`1 - s`.
-/
theorem strip_zero_reflection_iff {s : Complex}
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0 := by
  constructor
  · intro hz_reflect
    have hstrip := reflected_point_in_strip hpos hlt
    have h := strip_zero_reflects hstrip.1 hstrip.2 hz_reflect
    simpa using! h
  · intro hz
    exact strip_zero_reflects hpos hlt hz

/--
By reflection, it is enough to prove there are no zeros in the open right half
of the critical strip.
-/
theorem criticalStripObligations_of_rightHalfStripZeroFree
    (h : RightHalfStripZeroFree) : CriticalStripObligations where
  strip_zero_on_line := by
    intro s hpos hlt hz
    rcases lt_trichotomy s.re (1 / 2 : Real) with hleft | heq | hright
    · have hz_reflect := strip_zero_reflects hpos hlt hz
      have hstrip_reflect := reflected_point_in_strip hpos hlt
      have hright_reflect : 1 / 2 < (1 - s).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith
      exact False.elim ((h (1 - s) hright_reflect hstrip_reflect.2) hz_reflect)
    · exact heq
    · exact False.elim ((h s hright hlt) hz)

/--
A verified reduction: if the two remaining obligations are supplied, then
mathlib's formal statement of the Riemann Hypothesis follows.
-/
theorem riemannHypothesis_from_obligations
    (h : CriticalStripObligations) : RiemannHypothesis := by
  intro s hz hnotTrivial hsNotOne
  by_cases hle0 : s.re ≤ 0
  · exact False.elim (hnotTrivial (left_of_strip_zero_is_trivial hle0 hz))
  · have hpos : 0 < s.re := lt_of_not_ge hle0
    by_cases hge1 : 1 ≤ s.re
    · exact False.elim ((no_zeta_zeros_on_or_right_of_one hge1) hz)
    · have hlt1 : s.re < 1 := lt_of_not_ge hge1
      exact h.strip_zero_on_line s hpos hlt1 hz

/--
A one-sided zero-free theorem for the open right half of the critical strip
would prove mathlib's formal statement of the Riemann Hypothesis.
-/
theorem riemannHypothesis_of_rightHalfStripZeroFree
    (h : RightHalfStripZeroFree) : RiemannHypothesis :=
  riemannHypothesis_from_obligations
    (criticalStripObligations_of_rightHalfStripZeroFree h)

/--
Conversely, mathlib's formal Riemann Hypothesis statement rules out zeros in
the open right half of the critical strip.
-/
theorem rightHalfStripZeroFree_of_riemannHypothesis
    (h : RiemannHypothesis) : RightHalfStripZeroFree := by
  intro s hhalf hlt hz
  have hnotTrivial : ¬ IsTrivialZetaZero s :=
    not_trivial_of_re_gt_half hhalf
  have hs_ne_one : s ≠ 1 :=
    ne_one_of_re_lt_one hlt
  have hline : s.re = 1 / 2 :=
    h s hz hnotTrivial hs_ne_one
  linarith

/--
The one-sided zero-free target is equivalent to mathlib's formal Riemann
Hypothesis statement.
-/
theorem rightHalfStripZeroFree_iff_riemannHypothesis :
    RightHalfStripZeroFree ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_rightHalfStripZeroFree
  · exact rightHalfStripZeroFree_of_riemannHypothesis

/--
The right-half zero-free target is an RH-equivalent target.
-/
theorem riemannHypothesis_iff_rightHalfStripZeroFree :
    RiemannHypothesis ↔ RightHalfStripZeroFree :=
  rightHalfStripZeroFree_iff_riemannHypothesis.symm

/--
Mathlib's formal Riemann Hypothesis supplies the central critical-strip
obligation.
-/
theorem criticalStripObligations_of_riemannHypothesis
    (h : RiemannHypothesis) : CriticalStripObligations :=
  criticalStripObligations_of_rightHalfStripZeroFree
    (rightHalfStripZeroFree_of_riemannHypothesis h)

/--
Mathlib's formal Riemann Hypothesis supplies exactly the central critical-strip
obligation, and that obligation is enough to prove RH.
-/
theorem criticalStripObligations_iff_riemannHypothesis :
    CriticalStripObligations ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_from_obligations
  · exact criticalStripObligations_of_riemannHypothesis

/--
The native critical-strip obligation is an RH-equivalent target.
-/
theorem riemannHypothesis_iff_criticalStripObligations :
    RiemannHypothesis ↔ CriticalStripObligations :=
  criticalStripObligations_iff_riemannHypothesis.symm

/--
The one-sided zero-free target is equivalent to the nonexistence of a concrete
right-half strip counterexample.
-/
theorem rightHalfStripZeroFree_iff_no_rightHalfStripCounterexample :
    RightHalfStripZeroFree ↔ ¬ ∃ s : Complex, RightHalfStripCounterexample s := by
  constructor
  · intro hfree hcounter
    rcases hcounter with ⟨s, hhalf, hlt, hz⟩
    exact (hfree s hhalf hlt) hz
  · intro hno s hhalf hlt hzero
    exact hno ⟨s, hhalf, hlt, hzero⟩

/--
Every right-half strip counterexample reflects to a left-half strip
counterexample.
-/
theorem rightHalfCounterexample_reflects_left {s : Complex}
    (h : RightHalfStripCounterexample s) :
    LeftHalfStripCounterexample (1 - s) := by
  rcases h with ⟨hhalf, hlt, hz⟩
  have hpos : 0 < s.re := by linarith
  have hz_reflect : riemannZeta (1 - s) = 0 :=
    strip_zero_reflects hpos hlt hz
  refine ⟨?_, ?_, hz_reflect⟩
  · rw [Complex.sub_re, Complex.one_re]
    linarith
  · rw [Complex.sub_re, Complex.one_re]
    linarith

/--
Every left-half strip counterexample reflects to a right-half strip
counterexample.
-/
theorem leftHalfCounterexample_reflects_right {s : Complex}
    (h : LeftHalfStripCounterexample s) :
    RightHalfStripCounterexample (1 - s) := by
  rcases h with ⟨hpos, hleft, hz⟩
  have hlt : s.re < 1 := by linarith
  have hz_reflect : riemannZeta (1 - s) = 0 :=
    strip_zero_reflects hpos hlt hz
  refine ⟨?_, ?_, hz_reflect⟩
  · rw [Complex.sub_re, Complex.one_re]
    linarith
  · rw [Complex.sub_re, Complex.one_re]
    linarith

/--
Pointwise reflection equivalence for right-half counterexamples.
-/
theorem rightHalfCounterexample_reflection_iff {s : Complex} :
    RightHalfStripCounterexample s ↔ LeftHalfStripCounterexample (1 - s) := by
  constructor
  · exact rightHalfCounterexample_reflects_left
  · intro hleft_reflect
    have hright_reflect : RightHalfStripCounterexample (1 - (1 - s)) :=
      leftHalfCounterexample_reflects_right hleft_reflect
    simpa using! hright_reflect

/--
Pointwise reflection equivalence for left-half counterexamples.
-/
theorem leftHalfCounterexample_reflection_iff {s : Complex} :
    LeftHalfStripCounterexample s ↔ RightHalfStripCounterexample (1 - s) := by
  constructor
  · exact leftHalfCounterexample_reflects_right
  · intro hright_reflect
    have hleft_reflect : LeftHalfStripCounterexample (1 - (1 - s)) :=
      rightHalfCounterexample_reflects_left hright_reflect
    simpa using! hleft_reflect

/--
Counterexamples must occur in reflected pairs across the critical line.
-/
theorem exists_rightHalfCounterexample_iff_exists_leftHalfCounterexample :
    (∃ s : Complex, RightHalfStripCounterexample s) ↔
      ∃ s : Complex, LeftHalfStripCounterexample s := by
  constructor
  · intro h
    rcases h with ⟨s, hs⟩
    exact ⟨1 - s, rightHalfCounterexample_reflects_left hs⟩
  · intro h
    rcases h with ⟨s, hs⟩
    exact ⟨1 - s, leftHalfCounterexample_reflects_right hs⟩

/--
Zero-freeness on the left half of the critical strip is equivalent to
zero-freeness on the right half.
-/
theorem leftHalfStripZeroFree_iff_rightHalfStripZeroFree :
    LeftHalfStripZeroFree ↔ RightHalfStripZeroFree := by
  constructor
  · intro hleft s hhalf hlt hzero
    have hleftCounter : LeftHalfStripCounterexample (1 - s) :=
      rightHalfCounterexample_reflects_left ⟨hhalf, hlt, hzero⟩
    exact (hleft (1 - s) hleftCounter.1 hleftCounter.2.1) hleftCounter.2.2
  · intro hright s hpos hleft hzero
    have hrightCounter : RightHalfStripCounterexample (1 - s) :=
      leftHalfCounterexample_reflects_right ⟨hpos, hleft, hzero⟩
    exact (hright (1 - s) hrightCounter.1 hrightCounter.2.1) hrightCounter.2.2

/--
The left-half zero-free target is also equivalent to mathlib's formal Riemann
Hypothesis statement.
-/
theorem leftHalfStripZeroFree_iff_riemannHypothesis :
    LeftHalfStripZeroFree ↔ RiemannHypothesis := by
  exact leftHalfStripZeroFree_iff_rightHalfStripZeroFree.trans
    rightHalfStripZeroFree_iff_riemannHypothesis

/--
The left-half zero-free target is an RH-equivalent target.
-/
theorem riemannHypothesis_iff_leftHalfStripZeroFree :
    RiemannHypothesis ↔ LeftHalfStripZeroFree :=
  leftHalfStripZeroFree_iff_riemannHypothesis.symm

/--
A right-half counterexample is an off-line zero in the critical strip.
-/
theorem criticalStripOffLineZero_of_rightHalfCounterexample {s : Complex}
    (h : RightHalfStripCounterexample s) : CriticalStripOffLineZero s := by
  rcases h with ⟨hhalf, hlt, hz⟩
  refine ⟨by linarith, hlt, hz, ?_⟩
  linarith

/--
A left-half counterexample is an off-line zero in the critical strip.
-/
theorem criticalStripOffLineZero_of_leftHalfCounterexample {s : Complex}
    (h : LeftHalfStripCounterexample s) : CriticalStripOffLineZero s := by
  rcases h with ⟨hpos, hleft, hz⟩
  refine ⟨hpos, by linarith, hz, ?_⟩
  linarith

/--
An off-line zero in the critical strip lies either to the right or to the left
of the critical line.
-/
theorem criticalStripOffLineZero_cases {s : Complex}
    (h : CriticalStripOffLineZero s) :
    RightHalfStripCounterexample s ∨ LeftHalfStripCounterexample s := by
  rcases h with ⟨hpos, hlt, hz, hoff⟩
  rcases lt_trichotomy s.re (1 / 2 : Real) with hleft | hline | hright
  · exact Or.inr ⟨hpos, hleft, hz⟩
  · exact False.elim (hoff hline)
  · exact Or.inl ⟨hright, hlt, hz⟩

/--
The existence of an off-line zero in the critical strip is equivalent to the
existence of a right-half strip counterexample.
-/
theorem exists_criticalStripOffLineZero_iff_exists_rightHalfCounterexample :
    (∃ s : Complex, CriticalStripOffLineZero s) ↔
      ∃ s : Complex, RightHalfStripCounterexample s := by
  constructor
  · intro h
    rcases h with ⟨s, hs⟩
    rcases criticalStripOffLineZero_cases hs with hright | hleft
    · exact ⟨s, hright⟩
    · exact exists_rightHalfCounterexample_iff_exists_leftHalfCounterexample.mpr ⟨s, hleft⟩
  · intro h
    rcases h with ⟨s, hs⟩
    exact ⟨s, criticalStripOffLineZero_of_rightHalfCounterexample hs⟩

/--
Failure of mathlib's formal Riemann Hypothesis is equivalent to the existence
of a zeta zero in the open right half of the critical strip.
-/
theorem not_riemannHypothesis_iff_exists_rightHalfStrip_zero :
    ¬ RiemannHypothesis ↔
      ∃ s : Complex, 1 / 2 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 := by
  classical
  rw [← rightHalfStripZeroFree_iff_riemannHypothesis]
  unfold RightHalfStripZeroFree
  push Not
  exact Iff.rfl

/--
Failure of mathlib's formal Riemann Hypothesis is equivalent to the existence
of a concrete right-half strip counterexample.
-/
theorem not_riemannHypothesis_iff_exists_rightHalfStripCounterexample :
    ¬ RiemannHypothesis ↔ ∃ s : Complex, RightHalfStripCounterexample s := by
  rw [not_riemannHypothesis_iff_exists_rightHalfStrip_zero]
  rfl

/--
Mathlib's formal Riemann Hypothesis is equivalent to the nonexistence of a
right-half strip counterexample.
-/
theorem riemannHypothesis_iff_no_rightHalfStripCounterexample :
    RiemannHypothesis ↔ ¬ ∃ s : Complex, RightHalfStripCounterexample s := by
  rw [← rightHalfStripZeroFree_iff_riemannHypothesis]
  exact rightHalfStripZeroFree_iff_no_rightHalfStripCounterexample

/--
Failure of mathlib's formal Riemann Hypothesis is equivalently witnessed by a
left-half strip counterexample.
-/
theorem not_riemannHypothesis_iff_exists_leftHalfStripCounterexample :
    ¬ RiemannHypothesis ↔ ∃ s : Complex, LeftHalfStripCounterexample s := by
  rw [not_riemannHypothesis_iff_exists_rightHalfStripCounterexample]
  exact exists_rightHalfCounterexample_iff_exists_leftHalfCounterexample

/--
Mathlib's formal Riemann Hypothesis is equivalent to the nonexistence of a
left-half strip counterexample.
-/
theorem riemannHypothesis_iff_no_leftHalfStripCounterexample :
    RiemannHypothesis ↔ ¬ ∃ s : Complex, LeftHalfStripCounterexample s := by
  rw [← leftHalfStripZeroFree_iff_riemannHypothesis]
  unfold LeftHalfStripZeroFree LeftHalfStripCounterexample
  constructor
  · intro hfree hcounter
    rcases hcounter with ⟨s, hpos, hleft, hz⟩
    exact (hfree s hpos hleft) hz
  · intro hno s hpos hleft hzero
    exact hno ⟨s, hpos, hleft, hzero⟩

/--
Failure of mathlib's formal Riemann Hypothesis is equivalent to the existence
of an off-line zero in the open critical strip.
-/
theorem not_riemannHypothesis_iff_exists_criticalStripOffLineZero :
    ¬ RiemannHypothesis ↔ ∃ s : Complex, CriticalStripOffLineZero s := by
  rw [not_riemannHypothesis_iff_exists_rightHalfStripCounterexample]
  exact exists_criticalStripOffLineZero_iff_exists_rightHalfCounterexample.symm

/--
Mathlib's formal Riemann Hypothesis is equivalent to the nonexistence of an
off-line zero in the open critical strip.
-/
theorem riemannHypothesis_iff_no_criticalStripOffLineZero :
    RiemannHypothesis ↔ ¬ ∃ s : Complex, CriticalStripOffLineZero s := by
  exact riemannHypothesis_iff_no_rightHalfStripCounterexample.trans
    (not_congr exists_criticalStripOffLineZero_iff_exists_rightHalfCounterexample.symm)

/--
The no-off-line-zero formulation is equivalent to the native critical-strip
obligation.
-/
theorem noCriticalStripOffLineZero_iff_criticalStripObligations :
    (¬ ∃ s : Complex, CriticalStripOffLineZero s) ↔ CriticalStripObligations := by
  constructor
  · intro hno
    refine ⟨?_⟩
    intro s hpos hlt hz
    by_contra hoff
    exact hno ⟨s, hpos, hlt, hz, hoff⟩
  · intro hobl hbad
    rcases hbad with ⟨s, hpos, hlt, hz, hoff⟩
    have hline : OnCriticalLine s := hobl.strip_zero_on_line s hpos hlt hz
    exact hoff hline

/--
The native critical-strip obligation is equivalent to ruling out off-line zeros
in the open critical strip.
-/
theorem criticalStripObligations_iff_noCriticalStripOffLineZero :
    CriticalStripObligations ↔ ¬ ∃ s : Complex, CriticalStripOffLineZero s :=
  noCriticalStripOffLineZero_iff_criticalStripObligations.symm

/--
Ruling out off-line zeros supplies the native critical-strip obligation.
-/
theorem criticalStripObligations_of_noCriticalStripOffLineZero
    (h : ¬ ∃ s : Complex, CriticalStripOffLineZero s) : CriticalStripObligations :=
  noCriticalStripOffLineZero_iff_criticalStripObligations.mp h

/--
The native critical-strip obligation rules out off-line zeros.
-/
theorem noCriticalStripOffLineZero_of_criticalStripObligations
    (h : CriticalStripObligations) : ¬ ∃ s : Complex, CriticalStripOffLineZero s :=
  noCriticalStripOffLineZero_iff_criticalStripObligations.mpr h

/--
A registry entry for a target that is known to be equivalent to mathlib's
formal Riemann Hypothesis statement. This stores only the equivalence, not a
proof of the target.
-/
structure RHEquivalentTarget where
  target : Prop
  iff_riemannHypothesis : target ↔ RiemannHypothesis

/--
The native critical-strip obligation as an RH-equivalent target.
-/
def criticalStripObligationsTarget : RHEquivalentTarget where
  target := CriticalStripObligations
  iff_riemannHypothesis := criticalStripObligations_iff_riemannHypothesis

/--
The right-half zero-free formulation as an RH-equivalent target.
-/
def rightHalfStripZeroFreeTarget : RHEquivalentTarget where
  target := RightHalfStripZeroFree
  iff_riemannHypothesis := rightHalfStripZeroFree_iff_riemannHypothesis

/--
The left-half zero-free formulation as an RH-equivalent target.
-/
def leftHalfStripZeroFreeTarget : RHEquivalentTarget where
  target := LeftHalfStripZeroFree
  iff_riemannHypothesis := leftHalfStripZeroFree_iff_riemannHypothesis

/--
The no-off-line-zero formulation as an RH-equivalent target.
-/
def noCriticalStripOffLineZeroTarget : RHEquivalentTarget where
  target := ¬ ∃ s : Complex, CriticalStripOffLineZero s
  iff_riemannHypothesis := riemannHypothesis_iff_no_criticalStripOffLineZero.symm

/--
The no-right-half-counterexample formulation as an RH-equivalent target.
-/
def noRightHalfCounterexampleTarget : RHEquivalentTarget where
  target := ¬ ∃ s : Complex, RightHalfStripCounterexample s
  iff_riemannHypothesis := riemannHypothesis_iff_no_rightHalfStripCounterexample.symm

/--
The no-left-half-counterexample formulation as an RH-equivalent target.
-/
def noLeftHalfCounterexampleTarget : RHEquivalentTarget where
  target := ¬ ∃ s : Complex, LeftHalfStripCounterexample s
  iff_riemannHypothesis := riemannHypothesis_iff_no_leftHalfStripCounterexample.symm

/--
Any registered target implies mathlib's formal Riemann Hypothesis statement.
-/
theorem riemannHypothesis_of_target (t : RHEquivalentTarget)
    (h : t.target) : RiemannHypothesis :=
  t.iff_riemannHypothesis.mp h

/--
Mathlib's formal Riemann Hypothesis statement implies any registered target.
-/
theorem target_of_riemannHypothesis (t : RHEquivalentTarget)
    (h : RiemannHypothesis) : t.target :=
  t.iff_riemannHypothesis.mpr h

end Reinmann
