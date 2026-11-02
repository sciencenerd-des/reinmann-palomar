/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.XiTotalPositivity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# The Correct Total-Positivity Route for Ξ: Pólya Frequency / Toeplitz (not Hankel)

`XiTotalPositivity` routed the Laguerre–Pólya program through **Hankel**
determinants of the signed moment sequence `μ_n = (-1)^n · XiCoeff n`.  This file
records, and partially proves, a *correction*: the Hankel/moment machine is the
wrong one for an entire function, and the correct object is the **Toeplitz**
matrix `[μ_{i-j}]` — i.e. the **Pólya frequency (PF) sequence** condition, whose
characterization is the **Aissen–Edrei–Schoenberg–Whitney theorem** (1951).

**Correctness note (2026-06-06).** `XiCoeff`/`Ξ` are now the coefficients of
**Riemann's `ξ`** (see `JensenProgram`), not of `Λ₀`.  So the classical Pólya /
Csordas–Norfolk–Varga statements quoted below genuinely apply to this `Ξ`.  Those
classical results are cited as **external inputs (not formalized here)**; what is
proved in Lean is only the extraction/algebra explicitly listed under "What is
proved here".

## Why Toeplitz, not Hankel (the structural point — classical, not original)

* **Hamburger / Stieltjes (Hankel).** A sequence `(μ_n)` has positive-semidefinite
  Hankel matrices `[μ_{i+j}]` iff `μ_n = ∫ x^n dν` for a positive measure `ν`.
  These are *moment* sequences; their generating function is a Cauchy/Stieltjes
  transform `∫ dν/(1-xz)` — a function with **poles**, never an entire product.
  Consequently Hankel positivity forces **log-convexity** `μ_n² ≤ μ_{n-1}μ_{n+1}`.

* **Edrei–ASW (Toeplitz).** A sequence `(a_n)` (with `a_n = 0` for `n<0`) is a
  *Pólya frequency sequence* — every minor of the Toeplitz matrix `[a_{i-j}]` is
  `≥ 0` — iff its generating function is
  `∑ a_n z^n = e^{γ z} ∏_i (1 + α_i z) / ∏_j (1 - β_j z)`, `γ, α_i, β_j ≥ 0`.
  With **no poles** (`β_j` absent) this is exactly a Laguerre–Pólya function with
  only nonpositive real zeros.  PF sequences are **log-concave**:
  `a_n² ≥ a_{n-1} a_{n+1}` (the `2×2` Toeplitz minor).

## Matching the proven Riemann-ξ result

Write `Ξ(t) = F(t²)`, `F(u) = ∑ b_n u^n`, `b_n = XiCoeff n`.  RH says every zero
of `Ξ` is real, i.e. every zero of `F` is real and positive, i.e.
`F(-u) = ∑ (-1)^n b_n u^n = ∑ XiMomentCoeff_n · u^n` has only negative real zeros
and lies in Laguerre–Pólya.  By Edrei–ASW this is exactly:

> **the signed sequence `XiMomentCoeff` is a Pólya frequency sequence.**

The `2×2` rung of this is `XiMomentCoeff_{n+1}² ≥ XiMomentCoeff_n · XiMomentCoeff_{n+2}`,
which is precisely the **Turán inequality** `XiTuran2 n` — and the Riemann-ξ
Turán inequalities are a classical theorem of **Csordas–Norfolk–Varga** (external,
**not formalized here**).  So the corrected Toeplitz route's first rung is backed
by an existing classical theorem, whereas the Hankel route demanded the opposite
(log-convex) inequality, which is false for a genuine Laguerre–Pólya product.

## What is proved here (unconditional)

* `XiToeplitzTotalPositive` — full PF condition (all minors of `[μ_{i-j}] ≥ 0`).
* `xiMomentCoeff_nonneg_of_toeplitzTP` — `1×1` minors give `μ_n ≥ 0`.
* `xiToeplitzMinor2_eq`, `xiToeplitzMinor2_nonneg_iff_turan2` — the `2×2` minor
  *is* the Turán determinant (log-concavity), with the correct sign.
* `xiTuran2All_of_toeplitzTP` — PF positivity implies *all* Turán inequalities
  (`XiTuran2`); conversely the order-`2` rung is backed by the external CNV theorem.

## What remains (the honest frontier, via Edrei–ASW — a theorem, not RH)

* `XiToeplitzTPToScaledFiniteBridge` — PF positivity ⟹ finite real-rooted
  approximants.  This is the Edrei–ASW payload: a *universal* classical theorem
  about sequences, provable without RH.  The RH-hard hypothesis is establishing
  `XiToeplitzTotalPositive` for Ξ's coefficients (the all-order minors); the
  finite ranks through 43 have a classical sector baseline, not yet formalized
  here. The RH-equivalent frontier is positivity at every rank. Strictness of
  fixed-rank contiguous minors is a separate, weaker question; see
  `research/STRICT_FINITE_PF_FROM_REAL_ZEROS_2026_10_06.md`.
-/

noncomputable section

open Matrix

namespace Reinmann

/-! ## Toeplitz matrix of the signed Ξ moment sequence -/

/-- Entry of the (lower-triangular) Toeplitz matrix of the signed `Ξ` moment
sequence: `T(i,j) = μ_{i-j}` if `j ≤ i`, else `0`, where `μ_n = (-1)^n XiCoeff n`. -/
def XiToeplitzEntry (i j : ℕ) : ℝ :=
  if j ≤ i then XiMomentCoeff (i - j) else 0

theorem xiToeplitzEntry_sub (i j : ℕ) (h : j ≤ i) :
    XiToeplitzEntry i j = XiMomentCoeff (i - j) := if_pos h

/-- **Pólya frequency (total positivity) condition for the signed `Ξ` moments.**
Every minor of the infinite Toeplitz matrix `[μ_{i-j}]` is nonnegative.  This is
the honest full PF condition (arbitrary strictly-monotone row/column selections),
not merely contiguous blocks.  By Edrei–ASW it is equivalent to `Ξ` lying in the
Laguerre–Pólya class, hence to RH. -/
def XiToeplitzTotalPositive : Prop :=
  ∀ (k : ℕ) (rows cols : Fin k → ℕ),
    StrictMono rows → StrictMono cols →
    0 ≤ (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det

/-! ## `1×1` minors: nonnegativity of the signed moments -/

theorem xiMomentCoeff_nonneg_of_toeplitzTP
    (h : XiToeplitzTotalPositive) (n : ℕ) : 0 ≤ XiMomentCoeff n := by
  have hrow : StrictMono (![n] : Fin 1 → ℕ) := by
    intro a b hab; fin_cases a; fin_cases b; simp_all
  have hcol : StrictMono (![0] : Fin 1 → ℕ) := by
    intro a b hab; fin_cases a; fin_cases b; simp_all
  have hdet := h 1 (![n]) (![0]) hrow hcol
  rw [Matrix.det_fin_one] at hdet
  simp only [Matrix.of_apply, Matrix.cons_val_zero] at hdet
  rw [xiToeplitzEntry_sub n 0 (Nat.zero_le _), Nat.sub_zero] at hdet
  exact hdet

/-! ## `2×2` minor: the Turán (log-concavity) determinant -/

/-- The canonical `2×2` Toeplitz (Pólya-frequency) minor of the signed moment
sequence: `μ_{n+1}² − μ_n·μ_{n+2}`.  Nonnegativity is **log-concavity**. -/
def XiToeplitzMinor2 (n : ℕ) : ℝ :=
  XiMomentCoeff (n + 1) ^ 2 - XiMomentCoeff n * XiMomentCoeff (n + 2)

/-- The signed sign factors cancel: the Toeplitz `2×2` minor of `μ` equals the
log-concavity determinant of the *unsigned* coefficients `b_n = XiCoeff n`. -/
theorem xiToeplitzMinor2_eq (n : ℕ) :
    XiToeplitzMinor2 n = XiCoeff (n + 1) ^ 2 - XiCoeff n * XiCoeff (n + 2) := by
  unfold XiToeplitzMinor2 XiMomentCoeff
  have h1 : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul]; exact Even.neg_one_pow ⟨n + 1, by ring⟩
  have h2 : (-1 : ℝ) ^ n * (-1) ^ (n + 2) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨n + 1, by ring⟩
  calc
    ((-1 : ℝ) ^ (n + 1) * XiCoeff (n + 1)) ^ 2
        - (-1) ^ n * XiCoeff n * ((-1) ^ (n + 2) * XiCoeff (n + 2))
      = ((-1 : ℝ) ^ (n + 1)) ^ 2 * XiCoeff (n + 1) ^ 2
        - ((-1) ^ n * (-1) ^ (n + 2)) * (XiCoeff n * XiCoeff (n + 2)) := by ring
    _ = XiCoeff (n + 1) ^ 2 - XiCoeff n * XiCoeff (n + 2) := by rw [h1, h2]; ring

/-- The `2×2` Toeplitz minor is nonnegative **iff** the Turán inequality holds.
This pins the *correct* curvature direction: Pólya-frequency ⟹ log-concavity,
matching the (proven) Csordas–Norfolk–Varga Turán inequalities for Ξ. -/
theorem xiToeplitzMinor2_nonneg_iff_turan2 (n : ℕ) :
    0 ≤ XiToeplitzMinor2 n ↔ XiTuran2 n := by
  rw [xiToeplitzMinor2_eq]
  unfold XiTuran2
  constructor <;> intro h <;> nlinarith

/-- A `2×2` Toeplitz minor of the signed `Ξ` moments, extracted from the PF
condition with rows `{n+1, n+2}` and columns `{0, 1}`. -/
theorem xiToeplitzMinor2_nonneg_of_toeplitzTP
    (h : XiToeplitzTotalPositive) (n : ℕ) : 0 ≤ XiToeplitzMinor2 n := by
  have hrows : StrictMono (![n + 1, n + 2] : Fin 2 → ℕ) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcols : StrictMono (![0, 1] : Fin 2 → ℕ) := by decide
  have hdet := h 2 (![n + 1, n + 2]) (![0, 1]) hrows hcols
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  rw [xiToeplitzEntry_sub (n + 1) 0 (Nat.zero_le _),
      xiToeplitzEntry_sub (n + 2) 1 (by omega),
      xiToeplitzEntry_sub (n + 1) 1 (by omega),
      xiToeplitzEntry_sub (n + 2) 0 (Nat.zero_le _),
      show n + 1 - 0 = n + 1 from rfl,
      show n + 2 - 1 = n + 1 from rfl,
      show n + 1 - 1 = n from rfl,
      show n + 2 - 0 = n + 2 from rfl] at hdet
  unfold XiToeplitzMinor2
  nlinarith [hdet]

/-- **The corrected route subsumes the CNV rung.** Pólya-frequency total
positivity of the signed `Ξ` moments implies *every* Turán inequality. -/
theorem xiTuran2_of_toeplitzTP (h : XiToeplitzTotalPositive) (n : ℕ) :
    XiTuran2 n :=
  (xiToeplitzMinor2_nonneg_iff_turan2 n).1 (xiToeplitzMinor2_nonneg_of_toeplitzTP h n)

theorem xiTuran2All_of_toeplitzTP (h : XiToeplitzTotalPositive) : XiTuran2All :=
  xiTuran2_of_toeplitzTP h

/-! ## `3×3` minor: the first frontier rung (order 3)

The `2×2` rung is backed by the external CNV theorem (not formalized here). The
genuine open frontier is order `≥ 3`. We
formalize the order-`3` Toeplitz (Pólya-frequency) minor directly via the PF
index selection, so its nonnegativity is an *immediate* consequence of
`XiToeplitzTotalPositive`, and we give its explicit algebraic expansion.

**Sign structure.** Every term of this `3×3` determinant is a product of three
signed moments `μ_{r+i-σ(i)} = (-1)^{r+i-σ(i)} b_{r+i-σ(i)}` whose indices sum to
`3r = 3(n+2)`, so each term carries the *same* factor `(-1)^{3(n+2)} = (-1)^n`.
Hence the signed minor equals `(-1)^n` times the unsigned `b`-determinant — the
correct alternating-positivity demand for a Laguerre–Pólya product, exactly as
the `2×2` case was sign-free. -/

/-- Row selection `{n+2, n+3, n+4}` for the order-`3` Toeplitz minor. -/
def xiToeplitzRows3 (n : ℕ) : Fin 3 → ℕ := ![n + 2, n + 3, n + 4]

/-- Column selection `{0, 1, 2}` for the order-`3` Toeplitz minor. -/
def xiToeplitzCols3 : Fin 3 → ℕ := ![0, 1, 2]

/-- The order-`3` contiguous Toeplitz minor of the signed `Ξ` moments, defined
through the PF index selection so that nonnegativity is immediate from the PF
condition. -/
def XiToeplitzMinor3 (n : ℕ) : ℝ :=
  (Matrix.of (fun a b => XiToeplitzEntry (xiToeplitzRows3 n a) (xiToeplitzCols3 b))).det

theorem xiToeplitzRows3_strictMono (n : ℕ) : StrictMono (xiToeplitzRows3 n) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp_all [xiToeplitzRows3, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem xiToeplitzCols3_strictMono : StrictMono xiToeplitzCols3 := by decide

/-- **Order-`3` rung is immediate from PF total positivity.** -/
theorem xiToeplitzMinor3_nonneg_of_toeplitzTP
    (h : XiToeplitzTotalPositive) (n : ℕ) : 0 ≤ XiToeplitzMinor3 n :=
  h 3 (xiToeplitzRows3 n) xiToeplitzCols3
    (xiToeplitzRows3_strictMono n) xiToeplitzCols3_strictMono

/-- The first genuinely new finite Toeplitz target beyond the classical
order-`2` Turán rung. -/
def XiToeplitzOrder3Positive : Prop :=
  ∀ n : ℕ, 0 ≤ XiToeplitzMinor3 n

/-- Full Pólya-frequency positivity includes the order-`3` frontier target. -/
theorem xiToeplitzOrder3Positive_of_toeplitzTP
    (h : XiToeplitzTotalPositive) : XiToeplitzOrder3Positive :=
  xiToeplitzMinor3_nonneg_of_toeplitzTP h

/-- Explicit algebraic expansion of the order-`3` signed Toeplitz minor. -/
theorem xiToeplitzMinor3_eq (n : ℕ) :
    XiToeplitzMinor3 n =
      XiMomentCoeff (n + 2) *
          (XiMomentCoeff (n + 2) ^ 2 - XiMomentCoeff (n + 1) * XiMomentCoeff (n + 3))
        - XiMomentCoeff (n + 1) *
          (XiMomentCoeff (n + 3) * XiMomentCoeff (n + 2)
            - XiMomentCoeff (n + 1) * XiMomentCoeff (n + 4))
        + XiMomentCoeff n *
          (XiMomentCoeff (n + 3) ^ 2 - XiMomentCoeff (n + 2) * XiMomentCoeff (n + 4)) := by
  unfold XiToeplitzMinor3
  rw [Matrix.det_fin_three]
  have r0 : xiToeplitzRows3 n 0 = n + 2 := rfl
  have r1 : xiToeplitzRows3 n 1 = n + 3 := rfl
  have r2 : xiToeplitzRows3 n 2 = n + 4 := rfl
  have c0 : xiToeplitzCols3 0 = 0 := rfl
  have c1 : xiToeplitzCols3 1 = 1 := rfl
  have c2 : xiToeplitzCols3 2 = 2 := rfl
  simp only [Matrix.of_apply, r0, r1, r2, c0, c1, c2]
  rw [xiToeplitzEntry_sub (n + 2) 0 (by omega), xiToeplitzEntry_sub (n + 3) 1 (by omega),
      xiToeplitzEntry_sub (n + 4) 2 (by omega), xiToeplitzEntry_sub (n + 2) 1 (by omega),
      xiToeplitzEntry_sub (n + 3) 2 (by omega), xiToeplitzEntry_sub (n + 4) 0 (by omega),
      xiToeplitzEntry_sub (n + 2) 2 (by omega), xiToeplitzEntry_sub (n + 3) 0 (by omega),
      xiToeplitzEntry_sub (n + 4) 1 (by omega),
      show n + 2 - 0 = n + 2 from rfl, show n + 3 - 1 = n + 2 from rfl,
      show n + 4 - 2 = n + 2 from rfl, show n + 2 - 1 = n + 1 from rfl,
      show n + 3 - 2 = n + 1 from rfl, show n + 4 - 0 = n + 4 from rfl,
      show n + 2 - 2 = n from rfl, show n + 3 - 0 = n + 3 from rfl,
      show n + 4 - 1 = n + 3 from rfl]
  ring

/-- **Sign reduction.** The order-`3` signed Toeplitz minor equals `(-1)^n` times
the unsigned `b`-coefficient `3×3` Toeplitz determinant — the correct
alternating-positivity demand of a Laguerre–Pólya product. -/
theorem xiToeplitzMinor3_sign_eq (n : ℕ) :
    XiToeplitzMinor3 n =
      (-1) ^ n *
        (XiCoeff (n + 2) *
            (XiCoeff (n + 2) ^ 2 - XiCoeff (n + 1) * XiCoeff (n + 3))
          - XiCoeff (n + 1) *
            (XiCoeff (n + 3) * XiCoeff (n + 2) - XiCoeff (n + 1) * XiCoeff (n + 4))
          + XiCoeff n *
            (XiCoeff (n + 3) ^ 2 - XiCoeff (n + 2) * XiCoeff (n + 4))) := by
  rw [xiToeplitzMinor3_eq]
  unfold XiMomentCoeff
  have e1 : (-1 : ℝ) ^ (n + 1) = -(-1) ^ n := by rw [pow_add]; ring
  have e2 : (-1 : ℝ) ^ (n + 2) = (-1) ^ n := by rw [pow_add]; ring
  have e3 : (-1 : ℝ) ^ (n + 3) = -(-1) ^ n := by rw [pow_add]; ring
  have e4 : (-1 : ℝ) ^ (n + 4) = (-1) ^ n := by rw [pow_add]; ring
  have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul]; exact Even.neg_one_pow ⟨n, by ring⟩
  rw [e1, e2, e3, e4]
  linear_combination
    ((-1 : ℝ) ^ n *
        (XiCoeff (n + 2) *
            (XiCoeff (n + 2) ^ 2 - XiCoeff (n + 1) * XiCoeff (n + 3))
          - XiCoeff (n + 1) *
            (XiCoeff (n + 3) * XiCoeff (n + 2) - XiCoeff (n + 1) * XiCoeff (n + 4))
          + XiCoeff n *
            (XiCoeff (n + 3) ^ 2 - XiCoeff (n + 2) * XiCoeff (n + 4)))) * hsq

/-! ## General contiguous minor: the whole ladder at once

Both the order-`2` and order-`3` extractions are instances of a single uniform
statement: for *every* order `k` and offset `m`, the contiguous Toeplitz minor
with rows `{m, m+1, …, m+k-1}` and columns `{0, 1, …, k-1}` is nonnegative under
the PF condition.  This is the genuine "all rungs" object; the open analytic
content is establishing `XiToeplitzTotalPositive` (proved for `k ≤ 2` via CNV). -/

theorem strictMono_addLeft_val (m k : ℕ) :
    StrictMono (fun i : Fin k => m + i.val) := by
  intro a b hab
  have h : a.val < b.val := hab
  change m + a.val < m + b.val
  omega

theorem strictMono_fin_val (k : ℕ) : StrictMono (fun j : Fin k => j.val) := by
  intro a b hab
  change a.val < b.val
  exact hab

/-- The order-`k`, offset-`m` contiguous Toeplitz minor of the signed `Ξ`
moments. -/
def XiToeplitzContigMinor (k m : ℕ) : ℝ :=
  (Matrix.of (fun i j : Fin k => XiToeplitzEntry (m + i.val) j.val)).det

/-- **The whole ladder.** Under PF total positivity, every contiguous Toeplitz
minor of the signed `Ξ` moments is nonnegative. -/
theorem xiToeplitzContigMinor_nonneg_of_toeplitzTP
    (h : XiToeplitzTotalPositive) (k m : ℕ) : 0 ≤ XiToeplitzContigMinor k m :=
  h k (fun i => m + i.val) (fun j => j.val)
    (strictMono_addLeft_val m k) (strictMono_fin_val k)

/-- The order-`2` rung is the `k = 2, m = n+1` instance of the general ladder. -/
theorem xiToeplitzMinor2_eq_contig (n : ℕ) :
    XiToeplitzMinor2 n = XiToeplitzContigMinor 2 (n + 1) := by
  rw [XiToeplitzContigMinor, Matrix.det_fin_two, XiToeplitzMinor2]
  simp only [Matrix.of_apply, Fin.val_zero, Fin.val_one]
  rw [xiToeplitzEntry_sub (n + 1 + 0) 0 (by omega),
      xiToeplitzEntry_sub (n + 1 + 1) 1 (by omega),
      xiToeplitzEntry_sub (n + 1 + 0) 1 (by omega),
      xiToeplitzEntry_sub (n + 1 + 1) 0 (by omega),
      show n + 1 + 0 - 0 = n + 1 from rfl, show n + 1 + 1 - 1 = n + 1 from rfl,
      show n + 1 + 0 - 1 = n from rfl, show n + 1 + 1 - 0 = n + 2 from rfl]
  ring

/-- The order-`3` frontier rung is the `k = 3, m = n+2` instance of the general
contiguous Toeplitz ladder. -/
theorem xiToeplitzMinor3_eq_contig (n : ℕ) :
    XiToeplitzMinor3 n = XiToeplitzContigMinor 3 (n + 2) := by
  unfold XiToeplitzMinor3 XiToeplitzContigMinor xiToeplitzRows3 xiToeplitzCols3
  congr
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## The Edrei–ASW bridge and the RH packaging -/

/-- **The Edrei–Aissen–Schoenberg–Whitney bridge.** Pólya-frequency (Toeplitz)
total positivity of the signed `Ξ` coefficients implies the finite real-rooted
(Laguerre–Pólya) approximation target.

This is the *correct* analytic payload (replacing the Hankel/moment bridge of
`XiTotalPositivity`).  Edrei–ASW is a universal theorem about sequences — it is
**not** RH; it is provable without assuming anything about ζ.  The RH-hard input
is the hypothesis `XiToeplitzTotalPositive` itself, whose `2×2` rung is backed by
the external CNV theorem (not formalized here) and whose frontier is order `≥ 3`. -/
def XiToeplitzTPToScaledFiniteBridge : Prop :=
  XiToeplitzTotalPositive → XiLaguerrePolyaScaledFiniteTarget

/-- A bundled witness for the corrected Toeplitz/Pólya-frequency route. -/
structure XiToeplitzPositivityWitness where
  toeplitzPositive : XiToeplitzTotalPositive
  toScaledFinite : XiToeplitzTPToScaledFiniteBridge
  closure : XiLaguerrePolyaClosureBridge
  polya : PolyaJensenBridge

/-- Pólya-frequency total positivity of the signed `Ξ` coefficients implies RH
once the Edrei–ASW bridge and the Laguerre–Pólya/Jensen closure are supplied. -/
theorem riemannHypothesis_of_xiToeplitzPositivity
    (w : XiToeplitzPositivityWitness) : RiemannHypothesis :=
  riemannHypothesis_of_xiLaguerrePolyaScaledFinite
    (w.toScaledFinite w.toeplitzPositive) w.closure w.polya

end Reinmann
