/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.CertifiedTaylorModel
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

/-! Differential recurrences for the genuine ordinary coefficients of exp and
Log. These are the composition identities used by the finite Gamma model. -/
noncomputable section
namespace Reinmann.CertifiedTaylorComposition
open Finset Filter CertifiedTaylorModel
open scoped Topology

/-- Differentiating ordinary coefficients introduces precisely the next index. -/
theorem coefficient_deriv (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coefficient (deriv f) c n = (n + 1 : ℂ) * coefficient f c (n + 1) := by
  unfold coefficient
  rw [iteratedDeriv_succ', Nat.factorial_succ]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/-- An actual analytic germ, rather than a formal - series composition assumption. -/
theorem coefficient_exp_succ {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) (n : ℕ) :
    (n + 1 : ℂ) * coefficient (fun z => Complex.exp (f z)) c (n + 1) =
      ∑ i ∈ range (n + 1), (i + 1 : ℂ) * coefficient f c (i + 1)*
        coefficient (fun z => Complex.exp (f z)) c (n - i) := by
  have heq : deriv (fun z => Complex.exp (f z)) =ᶠ[𝓝 c]
      (fun z => deriv f z * Complex.exp (f z)) := by
    filter_upwards [hf.eventually_analyticAt] with z hz
    simpa only [mul_comm] using! deriv_cexp hz.differentiableAt
  rw [← coefficient_deriv]
  calc
    coefficient (deriv (fun z => Complex.exp (f z))) c n =
        coefficient (fun z => deriv f z * Complex.exp (f z)) c n := by
      unfold coefficient
      rw [heq.iteratedDeriv_eq n]
    _ = _ := by rw [coefficient_mul hf.deriv hf.cexp']; simp only [coefficient_deriv]

/-- The Log recurrence uses the analytic inverse germ; the branch condition is explicit. -/
theorem coefficient_log_succ {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c)
    (hc : f c ∈ Complex.slitPlane) (n : ℕ) :
    (n + 1 : ℂ) * coefficient (fun z => Complex.log (f z)) c (n + 1) =
      ∑ i ∈ range (n + 1), (i + 1 : ℂ) * coefficient f c (i + 1)*
        coefficient (fun z => (f z)⁻¹) c (n - i) := by
  have heq : deriv (fun z => Complex.log (f z)) =ᶠ[𝓝 c]
      (fun z => deriv f z * (f z)⁻¹) := by
    have hslit : ∀ᶠ z in 𝓝 c, f z ∈ Complex.slitPlane :=
      hf.continuousAt (Complex.isOpen_slitPlane.mem_nhds hc)
    filter_upwards [hf.eventually_analyticAt, hslit] with z hz hs
    simpa only [div_eq_mul_inv] using! (hz.differentiableAt.hasDerivAt.clog hs).deriv
  rw [← coefficient_deriv]
  have hi : AnalyticAt ℂ (fun z => (f z)⁻¹) c := hf.inv (Complex.slitPlane_ne_zero hc)
  calc
    coefficient (deriv (fun z => Complex.log (f z))) c n =
        coefficient (fun z => deriv f z * (f z)⁻¹) c n := by
      unfold coefficient
      rw [heq.iteratedDeriv_eq n]
    _ = _ := by rw [coefficient_mul hf.deriv hi]; simp only [coefficient_deriv]

/-- Multiplication by an inverse germ gives the exact nonconstant convolution. -/
theorem coefficient_inv_succ {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c)
    (hc : f c ≠ 0) (n : ℕ) :
    coefficient (fun z => (f z)⁻¹) c (n + 1) =
      -(f c)⁻¹ * ∑ i ∈ range (n + 1), coefficient f c (i + 1)*
        coefficient (fun z => (f z)⁻¹) c (n - i) := by
  have hi : AnalyticAt ℂ (fun z => (f z)⁻¹) c := hf.inv hc
  have heq : (fun z => f z * (f z)⁻¹) =ᶠ[𝓝 c] (fun _ => (1 : ℂ)) := by
    filter_upwards [hf.continuousAt.eventually_ne hc] with z hz
    exact mul_inv_cancel₀ hz
  have hzero : coefficient (fun z => f z * (f z)⁻¹) c (n + 1) = 0 := by
    unfold coefficient
    rw [heq.iteratedDeriv_eq, iteratedDeriv_const]
    simp
  rw [coefficient_mul hf hi, sum_range_succ'] at hzero
  simp only [Nat.add_sub_add_right, Nat.sub_zero, coefficient, iteratedDeriv_zero,
    Nat.factorial_zero, Nat.cast_one, div_one] at hzero
  have hh : f c * coefficient (fun z => (f z)⁻¹) c (n + 1) =
      -(∑ i ∈ range (n + 1), coefficient f c (i + 1)*
        coefficient (fun z => (f z)⁻¹) c (n - i)) := by
    exact eq_neg_of_add_eq_zero_right hzero
  calc
    _ = (f c)⁻¹ * (f c * coefficient (fun z => (f z)⁻¹) c (n + 1)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ = _ := by rw [hh]; ring

/-- A recurrence certificate may round every output coefficient. -/
theorem exp_coefficients_sound {d : ℕ} {a b : Jet d} {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (ha : Sound a f c)
    (hzero : Contains (b ⟨0, by omega⟩) (Complex.exp (f c)))
    (hstep : ∀ n (hn : n + 1 < d + 1),
      let raw := mul (exact (1 / (n + 1), 0))
        (sum (fun i => mul (exact (i + 1, 0))
          (mul (get a (i + 1)) (get b (n - i)))) (n + 1))
      raw.radius + size (raw.centre.1 - (b ⟨n + 1, hn⟩).centre.1,
        raw.centre.2 - (b ⟨n + 1, hn⟩).centre.2) ≤ (b ⟨n + 1, hn⟩).radius) :
    Sound b (fun z => Complex.exp (f z)) c := by
  have hb : ∀ n (hn : n < d + 1), Contains (b ⟨n, hn⟩)
      (coefficient (fun z => Complex.exp (f z)) c n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero => simpa [coefficient] using! hzero
      | succ n =>
        have hrec := coefficient_exp_succ hf n
        have hs : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        have hsum : Contains
            (sum (fun i => mul (exact (i + 1, 0))
              (mul (get a (i + 1)) (get b (n - i)))) (n + 1))
            (∑ i ∈ range (n + 1), (i + 1 : ℂ) * coefficient f c (i + 1)*
              coefficient (fun z => Complex.exp (f z)) c (n - i)) := by
          apply contains_sum
          intro i hi
          have hia : i + 1 < d + 1 := by omega
          have hib : n - i < d + 1 := by omega
          have hbi := ih (n - i) (by omega) hib
          have hai := ha ⟨i + 1, hia⟩
          have hh := contains_mul (contains_exact ((i + 1 : ℚ), 0))
            (contains_mul (by simpa [CertifiedTaylorModel.get, hia] using! hai) (by simpa [CertifiedTaylorModel.get, hib] using! hbi))
          simpa [value, mul_assoc, CertifiedTaylorModel.get, hia, hib] using! hh
        have hmul := contains_mul (contains_exact ((1 / (n + 1) : ℚ), 0)) hsum
        have hv : value ((1 / (n + 1) : ℚ), 0) = (n + 1 : ℂ)⁻¹ := by simp [value]
        rw [hv, ← hrec, ← mul_assoc, inv_mul_cancel₀ hs, one_mul] at hmul
        exact contains_round (b ⟨n + 1, hn⟩).radius_nonneg (hstep n hn) hmul
  intro k
  exact hb k.val k.isLt

/-- Reciprocal - model arithmetic, with an outward rational check at every step. -/
theorem inv_coefficients_sound {d : ℕ} {a b : Jet d} {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hc : f c ≠ 0) (ha : Sound a f c)
    (hzero : Contains (b ⟨0, by omega⟩) (f c)⁻¹)
    (hstep : ∀ n (hn : n + 1 < d + 1),
      let raw := mul (exact (-1, 0)) (mul (b ⟨0, by omega⟩)
        (sum (fun i => mul (get a (i + 1)) (get b (n - i))) (n + 1)))
      raw.radius + size (raw.centre.1 - (b ⟨n + 1, hn⟩).centre.1,
        raw.centre.2 - (b ⟨n + 1, hn⟩).centre.2) ≤ (b ⟨n + 1, hn⟩).radius) :
    Sound b (fun z => (f z)⁻¹) c := by
  have hb : ∀ n (hn : n < d + 1), Contains (b ⟨n, hn⟩)
      (coefficient (fun z => (f z)⁻¹) c n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      cases n with
      | zero => simpa [coefficient] using! hzero
      | succ n =>
        have hsum : Contains
            (sum (fun i => mul (get a (i + 1)) (get b (n - i))) (n + 1))
            (∑ i ∈ range (n + 1), coefficient f c (i + 1)*
              coefficient (fun z => (f z)⁻¹) c (n - i)) := by
          apply contains_sum
          intro i hi
          have hia : i + 1 < d + 1 := by omega
          have hib : n - i < d + 1 := by omega
          exact contains_mul
            (by simpa [CertifiedTaylorModel.get, hia] using! ha ⟨i + 1, hia⟩)
            (by simpa [CertifiedTaylorModel.get, hib] using! ih (n - i) (by omega) hib)
        have hh := contains_mul (contains_exact ((-1 : ℚ), 0)) (contains_mul hzero hsum)
        simp only [value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero, zero_mul,
          add_zero, neg_one_mul] at hh
        rw [← neg_mul, ← coefficient_inv_succ hf hc] at hh
        exact contains_round (b ⟨n + 1, hn⟩).radius_nonneg (hstep n hn) hh
  intro k
  exact hb k.val k.isLt

/-- Log jets follow from the inverse jet and one separately certified principal value. -/
theorem log_coefficients_sound {d : ℕ} {a b v : Jet d} {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hc : f c ∈ Complex.slitPlane)
    (ha : Sound a f c) (hv : Sound v (fun z => (f z)⁻¹) c)
    (hzero : Contains (b ⟨0, by omega⟩) (Complex.log (f c)))
    (hstep : ∀ n (hn : n + 1 < d + 1),
      let raw := mul (exact (1 / (n + 1), 0))
        (sum (fun i => mul (exact (i + 1, 0))
          (mul (get a (i + 1)) (get v (n - i)))) (n + 1))
      raw.radius + size (raw.centre.1 - (b ⟨n + 1, hn⟩).centre.1,
        raw.centre.2 - (b ⟨n + 1, hn⟩).centre.2) ≤ (b ⟨n + 1, hn⟩).radius) :
    Sound b (fun z => Complex.log (f z)) c := by
  intro k
  obtain ⟨n, hn⟩ := k
  cases n with
  | zero => simpa [coefficient] using! hzero
  | succ n =>
    have hsum : Contains
        (sum (fun i => mul (exact (i + 1, 0))
          (mul (get a (i + 1)) (get v (n - i)))) (n + 1))
        (∑ i ∈ range (n + 1), (i + 1 : ℂ) * coefficient f c (i + 1)*
          coefficient (fun z => (f z)⁻¹) c (n - i)) := by
      apply contains_sum
      intro i hi
      have hia : i + 1 < d + 1 := by omega
      have hiv : n - i < d + 1 := by omega
      have hh := contains_mul (contains_exact ((i + 1 : ℚ), 0))
        (contains_mul (ha ⟨i + 1, hia⟩) (hv ⟨n - i, hiv⟩))
      simpa [value, mul_assoc, CertifiedTaylorModel.get, hia, hiv] using! hh
    have hh := contains_mul (contains_exact ((1 / (n + 1) : ℚ), 0)) hsum
    have hv' : value ((1 / (n + 1) : ℚ), 0) = (n + 1 : ℂ)⁻¹ := by simp [value]
    have hs : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [hv', ← coefficient_log_succ hf hc n, ← mul_assoc, inv_mul_cancel₀ hs, one_mul] at hh
    exact contains_round (b ⟨n + 1, hn⟩).radius_nonneg (hstep n hn) hh

end Reinmann.CertifiedTaylorComposition
