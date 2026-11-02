/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Rational complex disks and finite ordinary Taylor models. The arithmetic is
exact over rationals; rounding is a separately checked outward enlargement.
The degree - eight instance has exactly nine coefficients. -/
noncomputable section
namespace Reinmann.CertifiedTaylorModel
open Finset

abbrev QComplex := ℚ × ℚ

def value (a : QComplex) : ℂ := (a.1 : ℂ) + (a.2 : ℂ) * Complex.I

def size (a : QComplex) : ℚ := |a.1| + |a.2|

def qadd (a b : QComplex) : QComplex := (a.1 + b.1, a.2 + b.2)
def qmul (a b : QComplex) : QComplex :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

@[simp] theorem value_add (a b : QComplex) : value (qadd a b) = value a + value b := by
  simp only [value, qadd, Rat.cast_add]
  ring

@[simp] theorem value_mul (a b : QComplex) : value (qmul a b) = value a * value b := by
  apply Complex.ext <;> simp [value, qmul]

theorem size_nonneg (a : QComplex) : 0 ≤ size a := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem norm_value_le (a : QComplex) : ‖value a‖ ≤ (size a : ℝ) := by
  simpa [value, size] using! Complex.norm_le_abs_re_add_abs_im (value a)

structure Disk where
  centre : QComplex
  radius : ℚ
  radius_nonneg : 0 ≤ radius

def Contains (a : Disk) (z : ℂ) : Prop := ‖z - value a.centre‖ ≤ (a.radius : ℝ)

def exact (a : QComplex) : Disk := ⟨a, 0, le_rfl⟩
def zero : Disk := exact (0, 0)
def add (a b : Disk) : Disk :=
  ⟨qadd a.centre b.centre, a.radius + b.radius, add_nonneg a.radius_nonneg b.radius_nonneg⟩
def mul (a b : Disk) : Disk :=
  ⟨qmul a.centre b.centre,
    a.radius * size b.centre + size a.centre * b.radius + a.radius * b.radius,
    add_nonneg (add_nonneg (mul_nonneg a.radius_nonneg (size_nonneg _))
      (mul_nonneg (size_nonneg _) b.radius_nonneg))
      (mul_nonneg a.radius_nonneg b.radius_nonneg)⟩

theorem contains_exact (a : QComplex) : Contains (exact a) (value a) := by
  simp [Contains, exact]

theorem contains_zero : Contains zero 0 := by simp [Contains, zero, exact, value]

theorem contains_add {a b : Disk} {x y : ℂ} (hx : Contains a x) (hy : Contains b y) :
    Contains (add a b) (x + y) := by
  unfold Contains at *
  change ‖x + y - value (qadd a.centre b.centre)‖ ≤ ((a.radius + b.radius : ℚ) : ℝ)
  rw [value_add, Rat.cast_add]
  calc
    _ = ‖(x - value a.centre) + (y - value b.centre)‖ := by congr 1; ring
    _ ≤ ‖x - value a.centre‖+‖y - value b.centre‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem contains_mul {a b : Disk} {x y : ℂ} (hx : Contains a x) (hy : Contains b y) :
    Contains (mul a b) (x * y) := by
  unfold Contains at *
  change ‖x * y - value (qmul a.centre b.centre)‖ ≤ _
  rw [value_mul]
  have ha : 0 ≤ (a.radius : ℝ) := by exact_mod_cast a.radius_nonneg
  have hb : 0 ≤ (b.radius : ℝ) := by exact_mod_cast b.radius_nonneg
  calc
    _ = ‖(x - value a.centre) * value b.centre + value a.centre * (y - value b.centre) +
        (x - value a.centre) * (y - value b.centre)‖ := by congr 1; ring
    _ ≤ ‖x - value a.centre‖*‖value b.centre‖ + ‖value a.centre‖*‖y - value b.centre‖ +
        ‖x - value a.centre‖*‖y - value b.centre‖ := by
      calc
        _ ≤ ‖(x - value a.centre) * value b.centre + value a.centre * (y - value b.centre)‖ +
            ‖(x - value a.centre) * (y - value b.centre)‖ := norm_add_le _ _
        _ ≤ (‖(x - value a.centre) * value b.centre‖ + ‖value a.centre * (y - value b.centre)‖) +
            ‖(x - value a.centre) * (y - value b.centre)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ = _ := by simp only [norm_mul]
    _ ≤ (a.radius : ℝ) * (size b.centre : ℝ) + (size a.centre : ℝ) * (b.radius : ℝ)+
        (a.radius : ℝ) * (b.radius : ℝ) := by
      have hsa : 0 ≤ (size a.centre : ℝ) := by exact_mod_cast size_nonneg a.centre
      gcongr <;> exact norm_value_le _
    _ = _ := by simp only [mul, Rat.cast_add, Rat.cast_mul]

/-- Outward rounding, with a rational L1 bound on the displacement of centres. -/
theorem contains_round {a : Disk} {c : QComplex} {r : ℚ} (hr : 0 ≤ r)
    (h : a.radius + size (a.centre.1 - c.1, a.centre.2 - c.2) ≤ r)
    {z : ℂ} (hz : Contains a z) : Contains (⟨c, r, hr⟩ : Disk) z := by
  unfold Contains at *
  have hdisp : ‖value a.centre - value c‖ ≤
      (size (a.centre.1 - c.1, a.centre.2 - c.2) : ℝ) := by
    have hv : value a.centre - value c = value (a.centre.1 - c.1, a.centre.2 - c.2) := by
      simp only [value, Rat.cast_sub]
      ring
    rw [hv]
    exact norm_value_le _
  exact (calc
    ‖z - value c‖ = ‖(z - value a.centre) + (value a.centre - value c)‖ := by congr 1; ring
    _ ≤ ‖z - value a.centre‖+‖value a.centre - value c‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hz hdisp
    _ ≤ (r : ℝ) := by exact_mod_cast h)

def sum (a : ℕ → Disk) (n : ℕ) : Disk :=
  match n with
  | 0 => zero
  | k + 1 => add (sum a k) (a k)

theorem contains_sum {a : ℕ → Disk} {x : ℕ → ℂ} {n : ℕ}
    (h : ∀ k < n, Contains (a k) (x k)) :
    Contains (sum a n) (∑ k ∈ range n, x k) := by
  induction n with
  | zero => simpa [sum] using! contains_zero
  | succ n ih =>
    rw [sum_range_succ]
    exact contains_add (ih (fun k hk => h k (by omega))) (h n (by omega))

/-- Ordinary, factorial - normalized coefficients at an arbitrary centre. -/
def coefficient (f : ℂ → ℂ) (c : ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k f c / (k.factorial : ℂ)

theorem coefficient_add {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) (k : ℕ) :
    coefficient (fun z => f z + g z) c k = coefficient f c k + coefficient g c k := by
  simp only [coefficient, iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

theorem coefficient_mul {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) (k : ℕ) :
    coefficient (fun z => f z * g z) c k =
      ∑ i ∈ range (k + 1), coefficient f c i * coefficient g c (k - i) := by
  unfold coefficient
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, sum_div]
  apply sum_congr rfl
  intro i hi
  have hle : i ≤ k := Nat.le_of_lt_succ (mem_range.mp hi)
  have hfac : (k.choose i : ℂ) * (i.factorial : ℂ) * ((k - i).factorial : ℂ) =
      (k.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hi' : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hki : ((k - i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - i)
  field_simp [hk, hi', hki]
  linear_combination (iteratedDeriv i f c) * (iteratedDeriv (k - i) g c) * hfac

theorem coefficient_scale {f : ℂ → ℂ} {c : ℂ} (a : ℂ) (hf : AnalyticAt ℂ f c) (k : ℕ) :
    coefficient (fun z => a * f z) c k = a * coefficient f c k := by
  simp only [coefficient, iteratedDeriv_const_mul a hf.contDiffAt, mul_div_assoc]

abbrev Jet (d : ℕ) := Fin (d + 1) → Disk
abbrev Jet8 := Jet 8

def get {d : ℕ} (a : Jet d) (k : ℕ) : Disk := if h : k < d + 1 then a ⟨k, h⟩ else zero

def Sound {d : ℕ} (a : Jet d) (f : ℂ → ℂ) (c : ℂ) : Prop :=
  ∀ k : Fin (d + 1), Contains (a k) (coefficient f c k.val)

def jetAdd {d : ℕ} (a b : Jet d) : Jet d := fun k => add (a k) (b k)
def jetMul {d : ℕ} (a b : Jet d) : Jet d :=
  fun k => sum (fun i => mul (get a i) (get b (k.val - i))) (k.val + 1)
def jetScale {d : ℕ} (a : QComplex) (b : Jet d) : Jet d := fun k => mul (exact a) (b k)

theorem sound_add {d : ℕ} {a b : Jet d} {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) (ha : Sound a f c) (hb : Sound b g c) :
    Sound (jetAdd a b) (fun z => f z + g z) c := by
  intro k
  rw [coefficient_add hf hg]
  exact contains_add (ha k) (hb k)

theorem sound_mul {d : ℕ} {a b : Jet d} {f g : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) (ha : Sound a f c) (hb : Sound b g c) :
    Sound (jetMul a b) (fun z => f z * g z) c := by
  intro k
  rw [coefficient_mul hf hg]
  apply contains_sum
  intro i hi
  have hi' : i < d + 1 := by have := k.isLt; omega
  have hki : k.val - i < d + 1 := by have := k.isLt; omega
  exact contains_mul (by simpa [get, hi'] using! ha ⟨i, hi'⟩)
    (by simpa [get, hki] using! hb ⟨k.val - i, hki⟩)

theorem sound_scale {d : ℕ} {a : QComplex} {b : Jet d} {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hb : Sound b f c) :
    Sound (jetScale a b) (fun z => value a * f z) c := by
  intro k
  rw [coefficient_scale _ hf]
  exact contains_mul (contains_exact a) (hb k)

/-- Coefficientwise outward rounding can be inserted after every operation. -/
theorem sound_round {d : ℕ} {a b : Jet d} {f : ℂ → ℂ} {c : ℂ}
    (ha : Sound a f c)
    (h : ∀ k, (a k).radius + size ((a k).centre.1 - (b k).centre.1,
      (a k).centre.2 - (b k).centre.2) ≤ (b k).radius) : Sound b f c := by
  intro k
  exact contains_round (b k).radius_nonneg (h k) (ha k)

/-- Add a separately proved analytic remainder to a finite - model disk. -/
def inflate (a : Disk) (e : ℚ) (he : 0 ≤ e) : Disk :=
  ⟨a.centre, a.radius + e, add_nonneg a.radius_nonneg he⟩

theorem contains_inflate {a : Disk} {e : ℚ} (he : 0 ≤ e) {x y : ℂ}
    (hx : Contains a x) (hxy : ‖y - x‖ ≤ (e : ℝ)) : Contains (inflate a e he) y := by
  unfold Contains at *
  change ‖y - value a.centre‖ ≤ ((a.radius + e : ℚ) : ℝ)
  calc
    _ = ‖(y - x) + (x - value a.centre)‖ := by congr 1; ring
    _ ≤ ‖y - x‖+‖x - value a.centre‖ := norm_add_le _ _
    _ ≤ (e : ℝ) + (a.radius : ℝ) := add_le_add hxy hx
    _ = _ := by push_cast; ring

/-- Transfer all coefficients from the finite approximant to the actual function. -/
theorem sound_perturb {d : ℕ} {a : Jet d} {f g : ℂ → ℂ} {c : ℂ}
    {e : ℚ} (he : 0 ≤ e) (ha : Sound a f c)
    (herr : ∀ k : Fin (d + 1), ‖coefficient g c k.val - coefficient f c k.val‖ ≤ (e : ℝ)) :
    Sound (fun k => inflate (a k) e he) g c := by
  intro k
  exact contains_inflate he (ha k) (herr k)

/-- Rational arithmetic also supplies a norm majorant for each enclosed coefficient. -/
theorem norm_le_of_contains {a : Disk} {z : ℂ} (ha : Contains a z) :
    ‖z‖ ≤ ((size a.centre + a.radius : ℚ) : ℝ) := by
  calc
    _ = ‖(z - value a.centre) + value a.centre‖ := by congr 1; ring
    _ ≤ ‖z - value a.centre‖+‖value a.centre‖ := norm_add_le _ _
    _ ≤ (a.radius : ℝ) + (size a.centre : ℝ) := add_le_add ha (norm_value_le _)
    _ = _ := by push_cast; ring

/-- The zeroth ordinary coefficient is the function value used in the tile rule. -/
theorem centre_contains {d : ℕ} {a : Jet d} {f : ℂ → ℂ} {c : ℂ}
    (ha : Sound a f c) : Contains (a ⟨0, by omega⟩) (f c) := by
  simpa [coefficient] using! ha ⟨0, by omega⟩

end Reinmann.CertifiedTaylorModel
