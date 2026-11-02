/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.ConjugateHalfPlane
public import Reinmann.CompletedZetaPrime
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-!
# Conjugation Symmetry of Λ₀ and Λ₀′, and Critical-Line Realness

Completing the de Branges / Hardy-`Z` picture. We prove unconditionally:

* `completedZeta₀_conj`: `Λ₀(s̄) = Λ̄₀(s)` (conjugation symmetry of the entire
  completed zeta), via the factorisation `Λ(s) = π^{-s/2} Γ(s/2) ∑ n^{-s}` on
  `Re s > 1` and the identity theorem;
* `deriv_completedZeta₀_conj`: `Λ₀′(s̄) = Λ̄₀′(s)`;
* `re_deriv_completedZeta₀_eq_zero_on_critical_line`: **`Re Λ₀′ = 0` on the critical
  line** `Re s = 1/2`.

The last is the structural realness behind the Hardy `Z`-function: combining the
reflection anti-symmetry `Λ₀′(1-s) = -Λ₀′(s)` with conjugation, on the line
`1 - s = s̄`, forcing `Λ₀′(s) = -Λ̄₀′(s)`, i.e. `Re Λ₀′(s) = 0`.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Reinmann

/-! ### Conjugation on the convergence half-plane -/

/-- On `Re s > 1`, `Λ(s̄) = Λ̄(s)` from the factorisation into `π`-power, `Γ`, and the
Dirichlet series. -/
theorem completedZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hs_conj : 1 < (conj s).re := by simpa using! hs
  rw [completedZeta_eq_tsum_of_one_lt_re hs_conj, completedZeta_eq_tsum_of_one_lt_re hs,
    map_mul, map_mul]
  congr 1
  · congr 1
    · -- π-power factor
      rw [conj_ofReal_cpow Real.pi Real.pi_pos (-s / 2)]
      congr 1
      simp only [map_div₀, map_neg, map_ofNat]
    · -- Gamma factor
      rw [← Complex.Gamma_conj]
      congr 1
      simp only [map_div₀, map_ofNat]
  · -- Dirichlet series factor
    rw [conj_tsum_nat]
    congr 1
    funext n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      simp [Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs),
        Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs_conj)]
    · exact (conj_inv_natCast_cpow n (Nat.pos_of_ne_zero hn) s).symm

/-- On `Re s > 1`, `Λ₀(s̄) = Λ̄₀(s)` (transfer through `Λ₀ = Λ + 1/s + 1/(1-s)`). -/
theorem completedZeta₀_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  have hΛ := completedZeta_conj_of_one_lt_re hs
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq] at hΛ
  simp only [map_sub, map_div₀, map_one] at hΛ
  -- hΛ : Λ₀(s̄) - 1/s̄ - 1/(1-s̄) = conj(Λ₀ s) - 1/s̄ - 1/(1 - s̄)
  linear_combination hΛ

/-! ### Conjugation everywhere via the identity theorem -/

private theorem completedZeta₀_analyticOnNhd :
    AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
  differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ

private theorem reflectedCompletedZeta₀_analyticOnNhd :
    AnalyticOnNhd ℂ (fun z : ℂ => conj (completedRiemannZeta₀ (conj z))) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro z _
  have hcc := (differentiable_completedZeta₀ (conj z)).conj_conj
  rw [Complex.conj_conj] at hcc
  exact hcc.differentiableWithinAt

/-- **Conjugation symmetry of Λ₀** (everywhere). -/
theorem completedZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  set g : ℂ → ℂ := fun z => conj (completedRiemannZeta₀ (conj z)) with hg
  have hfg : completedRiemannZeta₀ =ᶠ[nhds (2 : ℂ)] g := by
    refine Filter.eventuallyEq_of_mem
      (s := {z : ℂ | 1 < z.re})
      (one_lt_re_halfPlane_isOpen.mem_nhds (by norm_num)) ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    have h := completedZeta₀_conj_of_one_lt_re hz
    change completedRiemannZeta₀ z = conj (completedRiemannZeta₀ (conj z))
    rw [h, Complex.conj_conj]
  have hEq : Set.EqOn completedRiemannZeta₀ g Set.univ :=
    completedZeta₀_analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      reflectedCompletedZeta₀_analyticOnNhd isPreconnected_univ (Set.mem_univ _) hfg
  have hval := hEq (Set.mem_univ (conj s))
  rw [hg] at hval
  simpa [Complex.conj_conj] using! hval

/-! ### Conjugation of the derivative -/

/-- **Conjugation symmetry of Λ₀′.** -/
theorem deriv_completedZeta₀_conj (s : ℂ) :
    deriv completedRiemannZeta₀ (conj s) = conj (deriv completedRiemannZeta₀ s) := by
  have hf : HasDerivAt completedRiemannZeta₀
      (deriv completedRiemannZeta₀ (conj s)) (conj s) :=
    (differentiable_completedZeta₀ (conj s)).hasDerivAt
  have hcc := hf.conj_conj
  rw [Complex.conj_conj] at hcc
  have heq : completedRiemannZeta₀ =ᶠ[nhds s]
      (⇑(starRingEnd ℂ) ∘ completedRiemannZeta₀ ∘ ⇑(starRingEnd ℂ)) := by
    filter_upwards with z
    change completedRiemannZeta₀ z = conj (completedRiemannZeta₀ (conj z))
    rw [completedZeta₀_conj z, Complex.conj_conj]
  have hζ : HasDerivAt completedRiemannZeta₀
      (conj (deriv completedRiemannZeta₀ (conj s))) s :=
    hcc.congr_of_eventuallyEq heq
  have huniq : deriv completedRiemannZeta₀ s
      = conj (deriv completedRiemannZeta₀ (conj s)) := hζ.deriv
  have h2 := congrArg (starRingEnd ℂ) huniq
  rw [Complex.conj_conj] at h2
  exact h2.symm

/-! ### Critical-line realness -/

/-- **`Re Λ₀′ = 0` on the critical line.** For `s` with `Re s = 1/2`,
`(Λ₀′(s)).re = 0`. This is the structural realness underlying the Hardy
`Z`-function: reflection (`Λ₀′(1-s) = -Λ₀′(s)`) and conjugation
(`Λ₀′(s̄) = Λ̄₀′(s)`) coincide on the line `1 - s = s̄`. -/
theorem re_deriv_completedZeta₀_eq_zero_on_critical_line {s : ℂ}
    (hs : s.re = 1 / 2) : (deriv completedRiemannZeta₀ s).re = 0 := by
  have hline : (1 : ℂ) - s = conj s := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hs]; norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring
  -- conj (Λ₀′ s) = Λ₀′(s̄) = Λ₀′(1-s) = -Λ₀′(s)
  have hconj : deriv completedRiemannZeta₀ (conj s) = conj (deriv completedRiemannZeta₀ s) :=
    deriv_completedZeta₀_conj s
  have hreflect : deriv completedRiemannZeta₀ (1 - s) = -deriv completedRiemannZeta₀ s :=
    deriv_completedZeta₀_one_sub s
  rw [hline] at hreflect
  -- hreflect : Λ₀′(s̄) = -Λ₀′(s);  hconj : Λ₀′(s̄) = conj(Λ₀′ s)
  have hkey : conj (deriv completedRiemannZeta₀ s) = -deriv completedRiemannZeta₀ s := by
    rw [← hconj, hreflect]
  -- take real parts
  have hre := congrArg Complex.re hkey
  rw [Complex.conj_re, Complex.neg_re] at hre
  linarith

/-! ### Z-function realness of Λ₀ on the critical line -/

/-- **The completed zeta Λ₀ is real on the critical line.** For `Re s = 1/2`,
`(Λ₀ s).im = 0`. This is the structural source of the Hardy `Z`-function's
realness: on the line `1 - s = s̄`, so the functional equation `Λ₀(1-s) = Λ₀(s)`
and conjugation `Λ₀(s̄) = Λ̄₀(s)` together give `Λ₀(s) = Λ̄₀(s)`. -/
theorem completedZeta₀_real_on_critical_line {s : ℂ} (hs : s.re = 1 / 2) :
    (completedRiemannZeta₀ s).im = 0 := by
  have hline : (1 : ℂ) - s = conj s := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hs]; norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring
  have hfe : completedRiemannZeta₀ (conj s) = completedRiemannZeta₀ s := by
    rw [← hline]; exact completedRiemannZeta₀_one_sub s
  have hconj : completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) :=
    completedZeta₀_conj s
  have hself : conj (completedRiemannZeta₀ s) = completedRiemannZeta₀ s := by
    rw [← hconj, hfe]
  exact Complex.conj_eq_iff_im.mp hself

end Reinmann
