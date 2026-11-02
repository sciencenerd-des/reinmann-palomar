/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile020Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨20,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5781/640)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((3/4), (5781/640))
  have he : value ((3/4), (5781/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((107/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21913600/326514361), (-7399680/326514361)), 0, by norm_num⟩
  | 1 => ⟨((-212725300428800/106611627939238321), (162153627648000/106611627939238321)), 0, by norm_num⟩
  | 2 => ⟨((437362359/8796093022208), (-2591289769/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-938985717/1125899906842624), (213558305/70368744177664)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-230686453/36028797018963968), (-8019297547/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 5 => ⟨((1701623825/1152921504606846976), (1055498241/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-3358142069/36893488147419103232), (-1958323499/18446744073709551616)), (13/36893488147419103232), by norm_num⟩
  | 7 => ⟨((5026225061/1180591620717411303424), (2988103005/1180591620717411303424)), (19/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-6480753429/37778931862957161709568), (-1386163199/37778931862957161709568)), (7/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((7461787689/1208925819614629174706176), (-861446981/1208925819614629174706176)), (41/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-3850126487/19342813113834066795298816), (56729699/604462909807314587353088)), (15/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1738045941/309485009821345068724781056), (-3345424223/618970019642690137449562112)), (11/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-629909425/4951760157141521099596496896), (2426411029/9903520314283042199192993792)), (1/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (5781/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (5781/1280)))⁻¹=value ((21913600/326514361), (-7399680/326514361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/326514361), (-7399680/326514361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2842599289/1073741824), (699334839/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((10956800/326514361), (-3699840/326514361)), 0, by norm_num⟩
  | 2 => ⟨((-53181325107200/106611627939238321), (40538406912000/106611627939238321)), 0, by norm_num⟩
  | 3 => ⟨((145787453/17592186044416), (-3455053025/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-938985717/9007199254740992), (213558305/562949953421312)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((-369098325/576460752303423488), (-3207719019/288230376151711744)), (9/576460752303423488), by norm_num⟩
  | 6 => ⟨((2268831767/18446744073709551616), (351832747/1152921504606846976)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-1918938325/295147905179352825856), (-2238083999/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 8 => ⟨((5026225061/18889465931478580854784), (2988103005/18889465931478580854784)), (19/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-5760669715/604462909807314587353088), (-616072533/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((5969430151/19342813113834066795298816), (-689157585/19342813113834066795298816)), (17/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-5600183981/618970019642690137449562112), (1320254813/309485009821345068724781056)), (11/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((579348647/2475880078570760549798248448), (-2230282815/9903520314283042199192993792)), (15/4951760157141521099596496896), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (123/20480)), 0, by norm_num⟩
  | 45 => ⟨((100653774953/4080638361600), (-244401/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-46894389336319/1915179604377600), (4915144638673/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((3426649403/137438953472), (-1136924951/137438953472)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-219600923/8589934592), (1153785549/137438953472)), (1/137438953472), by norm_num⟩
  | 41 => ⟨((3602936753/137438953472), (-1181099923/137438953472)), (1/137438953472), by norm_num⟩
  | 40 => ⟨((-1846842603/68719476736), (1210794585/137438953472)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((3788293445/137438953472), (-1241282421/137438953472)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-1943973989/68719476736), (1272989909/137438953472)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((3993099051/137438953472), (-1306321941/137438953472)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-256507749/8589934592), (670736019/68719476736)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((1055373885/34359738368), (-1378578457/137438953472)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-4345772501/137438953472), (1417797331/137438953472)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((4477585777/137438953472), (-1459312005/137438953472)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-2308821673/68719476736), (751665325/68719476736)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((4766743493/137438953472), (-48440227/4294967296)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-4925790815/137438953472), (1599845573/137438953472)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((5095814779/137438953472), (-1652904191/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-5277991989/137438953472), (1709602701/137438953472)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((5473673401/137438953472), (-110645559/8589934592)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-5684417843/137438953472), (917763945/68719476736)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((5912033589/137438953472), (-952856281/68719476736)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-3079315157/68719476736), (990738779/68719476736)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((6426684607/137438953472), (-2063515939/137438953472)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-3359561667/68719476736), (538160123/34359738368)), (1/68719476736), by norm_num⟩
  | 21 => ⟨((3519715403/68719476736), (-281226343/17179869184)), (1/68719476736), by norm_num⟩
  | 20 => ⟨((-1847947021/34359738368), (294520957/17179869184)), (1/68719476736), by norm_num⟩
  | 19 => ⟨((3890628109/68719476736), (-77283707/4294967296)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-513376283/8589934592), (325274575/17179869184)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((2174430251/34359738368), (-686384683/34359738368)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-4620953213/68719476736), (1452796271/68719476736)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((4929334951/68719476736), (-1542730761/68719476736)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-1320444535/17179869184), (822267107/34359738368)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((711055473/8589934592), (-880361191/34359738368)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-6162874771/68719476736), (1894576207/68719476736)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((3361764781/34359738368), (-256307099/8589934592)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-3698116625/34359738368), (139643125/4294967296)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((4109128425/34359738368), (-306792229/8589934592)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-4622721593/34359738368), (170154779/4294967296)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((1320676315/8589934592), (-1528208691/34359738368)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-1540485297/8589934592), (1741899429/34359738368)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((230974869/1073741824), (-1012572365/17179869184)), (1/17179869184), by norm_num⟩
  | 4 => ⟨((-4615452067/17179869184), (151162687/2147483648)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((3071244807/8589934592), (-750614781/8589934592)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-4586963317/8589934592), (990084565/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((4531503377/4294967296), (-364305653/2147483648)), (1/4294967296), by norm_num⟩
  | 0 => ⟨((-2151122927/17179869184), (5594678713/17179869184)), (1/8589934592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (5781/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (5781/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (5781/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((2842599289/1073741824), (699334839/2147483648)), (1/2147483648), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (5781/1280))) (z:=((-21/128), (5781/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((2842599289/1073741824), (699334839/2147483648))) (r:=(1/2147483648)) (by norm_num) ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((273587701/8388608), (2167537653/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((1940154849/1073741824), (11307323/67108864)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((920978800204800/106611627939238321), (-322281926806560/106611627939238321)), 0, by norm_num⟩
  | 3 => ⟨((-3070971081/35184372088832), (152857115/2199023255552)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((1224986231/1125899906842624), (-3882169633/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 5 => ⟨((-1456239857/144115188075855872), (783627795/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-33104345/288230376151711744), (-1245156047/1152921504606846976)), (85/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1776209881/147573952589676412928), (1888138771/73786976294838206464)), (115/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2547216457/4722366482869645213696), (-2611596875/4722366482869645213696)), (37/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1476980759/75557863725914323419136), (1482063913/151115727451828646838272)), (95/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-6100893311/9671406556917033397649408), (-203356665/2417851639229258349412352)), (63/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((5741449741/309485009821345068724781056), (-1161332929/309485009821345068724781056)), (655/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-4892153283/9903520314283042199192993792), (1437740583/4951760157141521099596496896)), (875/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((161390069/8388608), (3122711735/268435456)), (5/268435456), by norm_num⟩
  | 1 => ⟨((1403283937/1073741824), (11307323/67108864)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((920978800204800/106611627939238321), (-322281926806560/106611627939238321)), 0, by norm_num⟩
  | 3 => ⟨((-3070971081/35184372088832), (152857115/2199023255552)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((1224986231/1125899906842624), (-3882169633/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 5 => ⟨((-1456239857/144115188075855872), (783627795/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-33104345/288230376151711744), (-1245156047/1152921504606846976)), (85/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1776209881/147573952589676412928), (1888138771/73786976294838206464)), (115/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2547216457/4722366482869645213696), (-2611596875/4722366482869645213696)), (37/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1476980759/75557863725914323419136), (1482063913/151115727451828646838272)), (95/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-6100893311/9671406556917033397649408), (-203356665/2417851639229258349412352)), (63/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((5741449741/309485009821345068724781056), (-1161332929/309485009821345068724781056)), (655/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-4892153283/9903520314283042199192993792), (1437740583/4951760157141521099596496896)), (875/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3946810947/2147483648), 0), (1/4294967296), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3946810947/4294967296), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1352789473/67108864), (3122711735/268435456)), (3/134217728), by norm_num⟩
  | 1 => ⟨((1403283937/1073741824), (11307323/67108864)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((920978800204800/106611627939238321), (-322281926806560/106611627939238321)), 0, by norm_num⟩
  | 3 => ⟨((-3070971081/35184372088832), (152857115/2199023255552)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((1224986231/1125899906842624), (-3882169633/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 5 => ⟨((-1456239857/144115188075855872), (783627795/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-33104345/288230376151711744), (-1245156047/1152921504606846976)), (85/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1776209881/147573952589676412928), (1888138771/73786976294838206464)), (115/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2547216457/4722366482869645213696), (-2611596875/4722366482869645213696)), (37/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1476980759/75557863725914323419136), (1482063913/151115727451828646838272)), (95/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-6100893311/9671406556917033397649408), (-203356665/2417851639229258349412352)), (63/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((5741449741/309485009821345068724781056), (-1161332929/309485009821345068724781056)), (655/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-4892153283/9903520314283042199192993792), (1437740583/4951760157141521099596496896)), (875/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((425450600857600/106611627939238321), (-324307255296000/106611627939238321)), 0, by norm_num⟩
  | 1 => ⟨((-437362359/2199023255552), (2591289769/8796093022208)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((1408478575/281474976710656), (-640674915/35184372088832)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((230686453/4503599627370496), (4009648773/4503599627370496)), (7/9007199254740992), by norm_num⟩
  | 4 => ⟨((-2127029781/144115188075855872), (-5277491205/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((314825819/288230376151711744), (45898207/36028797018963968)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-274871683/4611686018427387904), (-2614590129/73786976294838206464)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((6480753429/2361183241434822606848), (1386163199/2361183241434822606848)), (23/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-4197255575/37778931862957161709568), (484563927/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1203164527/302231454903657293676544), (-283648495/151115727451828646838272)), (7/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-2389813169/19342813113834066795298816), (1149989577/9671406556917033397649408)), (11/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1889728275/618970019642690137449562112), (-113738017/19342813113834066795298816)), (33/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-768618661/19807040628566084398385987584), (622038139/2475880078570760549798248448)), (49/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((437362359/2199023255552), (-2591289769/8796093022208)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1408478575/140737488355328), (640674915/17592186044416)), (3/140737488355328), by norm_num⟩
  | 2 => ⟨((-21626855/140737488355328), (-6014473159/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 3 => ⟨((2127029781/36028797018963968), (5277491205/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 4 => ⟨((-1574129095/288230376151711744), (-229491035/36028797018963968)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((824615049/2305843009213693952), (490235649/2305843009213693952)), (9/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-2835329625/147573952589676412928), (-1212892799/295147905179352825856)), (17/295147905179352825856), by norm_num⟩
  | 7 => ⟨((2098627787/2361183241434822606848), (-484563927/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-5414240371/151115727451828646838272), (2552836455/151115727451828646838272)), (27/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((746816615/604462909807314587353088), (-1437486971/1208925819614629174706176)), (23/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-2598376377/77371252455336267181195264), (1251118187/19342813113834066795298816)), (37/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((576463995/1237940039285380274899124224), (-1866114417/618970019642690137449562112)), (29/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((428339643/19807040628566084398385987584), (4919563357/39614081257132168796771975168)), (23/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((938985717/140737488355328), (-213558305/8796093022208)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((230686453/1125899906842624), (4009648773/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-2127029781/18014398509481984), (-1319372801/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 3 => ⟨((2098838793/144115188075855872), (2447904373/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((-1374358415/1152921504606846976), (-817059415/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 5 => ⟨((2835329625/36893488147419103232), (606446399/36893488147419103232)), (15/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-2448399085/590295810358705651712), (282662291/590295810358705651712)), (17/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((3609493581/18889465931478580854784), (-850945485/9444732965739290427392)), (17/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-2240449845/302231454903657293676544), (269528807/37778931862957161709568)), (1/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((2165313647/9671406556917033397649408), (-1042598489/2417851639229258349412352)), (7/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-1056850657/309485009821345068724781056), (6842419529/309485009821345068724781056)), (3/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-428339643/2475880078570760549798248448), (-1229890839/1237940039285380274899124224)), (5/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((52807901/2475880078570760549798248448), (388444595/9903520314283042199192993792)), (17/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-230686453/2251799813685248), (-8019297547/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 1 => ⟨((2127029781/18014398509481984), (5277491205/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 2 => ⟨((-1574129095/72057594037927936), (-229491035/9007199254740992)), (7/144115188075855872), by norm_num⟩
  | 3 => ⟨((1374358415/576460752303423488), (817059415/576460752303423488)), (7/1152921504606846976), by norm_num⟩
  | 4 => ⟨((-3544162031/18446744073709551616), (-758057999/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 5 => ⟨((7345197255/590295810358705651712), (-847986873/590295810358705651712)), (3/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-3158306883/4722366482869645213696), (1489154599/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((2240449845/75557863725914323419136), (-2156230457/75557863725914323419136)), (1/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-2435977853/2417851639229258349412352), (293230825/151115727451828646838272)), (15/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((660531661/38685626227668133590597632), (-4276512205/38685626227668133590597632)), (29/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((588967009/618970019642690137449562112), (3382199807/618970019642690137449562112)), (53/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-2534779249/19807040628566084398385987584), (-1165333785/4951760157141521099596496896)), (47/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((2941404939/316912650057057350374175801344), (2724211477/316912650057057350374175801344)), (41/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1701623825/36028797018963968), (-1055498241/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 1 => ⟨((314825819/18014398509481984), (45898207/2251799813685248)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((-824615049/288230376151711744), (-490235649/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 3 => ⟨((2835329625/9223372036854775808), (606446399/9223372036854775808)), (15/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-7345197255/295147905179352825856), (847986873/295147905179352825856)), (25/295147905179352825856), by norm_num⟩
  | 5 => ⟨((947492065/590295810358705651712), (-1786985519/2361183241434822606848)), (17/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-3136629783/37778931862957161709568), (3018722639/37778931862957161709568)), (21/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((974391141/302231454903657293676544), (-3753354561/604462909807314587353088)), (25/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-297239247/4835703278458516698824704), (3848860985/9671406556917033397649408)), (27/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-588967009/154742504910672534362390528), (-3382199807/154742504910672534362390528)), (53/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((2788257173/4951760157141521099596496896), (2563734327/2475880078570760549798248448)), (13/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-3529685927/79228162514264337593543950336), (-3269053773/79228162514264337593543950336)), (3/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((1762196421/633825300114114700748351602688), (789969579/633825300114114700748351602688)), (45/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3358142069/576460752303423488), (-1958323499/288230376151711744)), (13/576460752303423488), by norm_num⟩
  | 1 => ⟨((274871683/144115188075855872), (163411883/144115188075855872)), (3/576460752303423488), by norm_num⟩
  | 2 => ⟨((-2835329625/9223372036854775808), (-606446399/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 3 => ⟨((2448399085/73786976294838206464), (-282662291/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-3158306883/1180591620717411303424), (1489154599/1180591620717411303424)), (15/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((3136629783/18889465931478580854784), (-3018722639/18889465931478580854784)), (11/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-1136789665/151115727451828646838272), (2189456827/151115727451828646838272)), (29/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((99079749/604462909807314587353088), (-5131814647/4835703278458516698824704)), (9/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((441725257/38685626227668133590597632), (5073299711/77371252455336267181195264)), (21/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-2323547645/1237940039285380274899124224), (-4272890545/1237940039285380274899124224)), (45/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((3235545433/19807040628566084398385987584), (2996632625/19807040628566084398385987584)), (23/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-1762196421/158456325028528675187087900672), (-789969579/158456325028528675187087900672)), (45/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((3268089485/5070602400912917605986812821504), (627925251/10141204801825835211973625643008)), (43/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5026225061/9223372036854775808), (-2988103005/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 1 => ⟨((1620188357/9223372036854775808), (693081599/18446744073709551616)), (21/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-2098627787/73786976294838206464), (484563927/147573952589676412928)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((3609493581/1180591620717411303424), (-1701890971/1180591620717411303424)), (17/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-2240449845/9444732965739290427392), (2156230457/9444732965739290427392)), (17/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((974391141/75557863725914323419136), (-58646165/2361183241434822606848)), (27/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-792637993/2417851639229258349412352), (5131814647/2417851639229258349412352)), (37/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-504828865/19342813113834066795298816), (-1449514203/9671406556917033397649408)), (49/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((2987418401/618970019642690137449562112), (5493716415/618970019642690137449562112)), (15/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-2311103881/4951760157141521099596496896), (-2140451875/4951760157141521099596496896)), (35/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((5538331609/158456325028528675187087900672), (2482761533/158456325028528675187087900672)), (75/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-2801219559/1267650600228229401496703205376), (-134555411/633825300114114700748351602688)), (39/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((2458588417/20282409603651670423947251286016), (-1150691143/40564819207303340847894502572032)), (77/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6480753429/147573952589676412928), (-1386163199/147573952589676412928)), (7/36893488147419103232), by norm_num⟩
  | 1 => ⟨((2098627787/147573952589676412928), (-484563927/295147905179352825856)), (9/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-5414240371/2361183241434822606848), (2552836455/2361183241434822606848)), (29/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((2240449845/9444732965739290427392), (-2156230457/9444732965739290427392)), (17/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-2435977853/151115727451828646838272), (4691693201/151115727451828646838272)), (9/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((297239247/604462909807314587353088), (-3848860985/1208925819614629174706176)), (31/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((441725257/9671406556917033397649408), (5073299711/19342813113834066795298816)), (23/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-93356825/9671406556917033397649408), (-5493716415/309485009821345068724781056)), (1/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((1299995933/1237940039285380274899124224), (2408008359/2475880078570760549798248448)), (41/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-3461457255/39614081257132168796771975168), (-775862979/19807040628566084398385987584)), (51/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((7703353787/1267650600228229401496703205376), (740054759/1267650600228229401496703205376)), (57/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-1843941313/5070602400912917605986812821504), (863018357/10141204801825835211973625643008)), (63/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((759831051/40564819207303340847894502572032), (-1886634337/162259276829213363391578010288128)), (65/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7461787689/2361183241434822606848), (861446981/2361183241434822606848)), (41/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((4812658107/4722366482869645213696), (-283648495/590295810358705651712)), (15/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((-746816615/4722366482869645213696), (1437486971/9444732965739290427392)), (13/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((2165313647/151115727451828646838272), (-1042598489/37778931862957161709568)), (33/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-165132915/302231454903657293676544), (2138256103/604462909807314587353088)), (37/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-1177934019/19342813113834066795298816), (-3382199807/9671406556917033397649408)), (67/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((2323547645/154742504910672534362390528), (4272890545/154742504910672534362390528)), (27/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-2311103881/1237940039285380274899124224), (-2140451875/1237940039285380274899124224)), (5/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((3461457255/19807040628566084398385987584), (775862979/9903520314283042199192993792)), (27/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-133738781/9903520314283042199192993792), (-411141533/316912650057057350374175801344)), (69/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((4507412097/5070602400912917605986812821504), (-527400107/2535301200456458802993406410752)), (83/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-253277017/5070602400912917605986812821504), (1257756225/40564819207303340847894502572032)), (95/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((3009519993/1298074214633706907132624082305024), (-3649300127/1298074214633706907132624082305024)), (103/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3850126487/18889465931478580854784), (56729699/590295810358705651712)), (15/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((149363323/2361183241434822606848), (-2299979153/37778931862957161709568)), (25/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-2598376377/302231454903657293676544), (5004472747/302231454903657293676544)), (23/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((1056850657/2417851639229258349412352), (-6842419529/2417851639229258349412352)), (31/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((1177934019/19342813113834066795298816), (3382199807/9671406556917033397649408)), (73/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-1394128587/77371252455336267181195264), (-2563734327/77371252455336267181195264)), (71/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((3235545433/1237940039285380274899124224), (2996632625/1237940039285380274899124224)), (61/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-5538331609/19807040628566084398385987584), (-2482761533/19807040628566084398385987584)), (95/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((3851676893/158456325028528675187087900672), (740054759/316912650057057350374175801344)), (135/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-4507412097/2535301200456458802993406410752), (527400107/1267650600228229401496703205376)), (91/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((2228837749/20282409603651670423947251286016), (-1383531847/20282409603651670423947251286016)), (57/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-3611423991/649037107316853453566312041152512), (547395019/81129638414606681695789005144064)), (17/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((131205073/649037107316853453566312041152512), (-2755472479/5192296858534827628530496329220096)), (155/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/979543083), (-616640/326514361)), 0, by norm_num⟩
  | 1 => ⟨((-53181325107200/319834883817714963), (13512802304000/106611627939238321)), 0, by norm_num⟩
  | 2 => ⟨((145787453/35184372088832), (-3455053025/562949953421312)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-312995239/4503599627370496), (4555910507/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 4 => ⟨((-307581937/576460752303423488), (-5346198365/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((2268831767/18446744073709551616), (351832747/1152921504606846976)), (11/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-2238761379/295147905179352825856), (-2611097999/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((3350816707/9444732965739290427392), (996034335/4722366482869645213696)), (13/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-2160251143/151115727451828646838272), (-924108799/302231454903657293676544)), (19/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((2487262563/4835703278458516698824704), (-574297987/9671406556917033397649408)), (7/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-5133501983/309485009821345068724781056), (2420467157/309485009821345068724781056)), (41/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((579348647/1237940039285380274899124224), (-2230282815/4951760157141521099596496896)), (15/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-1679758467/158456325028528675187087900672), (3235214705/158456325028528675187087900672)), (11/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5412659201/268435456), (780551195/67108864)), (7/268435456), by norm_num⟩
  | 1 => ⟨((701552699/536870912), (362106525/2147483648)), (3/4294967296), by norm_num⟩
  | 2 => ⟨((4751417021/549755813888), (-1665259991/549755813888)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-768354089/8796093022208), (2454612103/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1224385485/1125899906842624), (-975763305/562949953421312)), (23/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1438514609/144115188075855872), (6313001453/144115188075855872)), (65/144115188075855872), by norm_num⟩
  | 6 => ⟨((-564650167/4611686018427387904), (-2510711297/2305843009213693952)), (43/2305843009213693952), by norm_num⟩
  | 7 => ⟨((228570799/18446744073709551616), (3807403615/147573952589676412928)), (29/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-2614724305/4722366482869645213696), (-2626036075/4722366482869645213696)), (149/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((3031688473/151115727451828646838272), (1473090507/151115727451828646838272)), (191/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-391332203/604462909807314587353088), (-737787061/9671406556917033397649408)), (253/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((5886286903/309485009821345068724781056), (-1300725605/309485009821345068724781056)), (329/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-4997138187/9903520314283042199192993792), (3077682085/9903520314283042199192993792)), (439/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2488105865/4503599627370496), (1842694947/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((250396191/9007199254740992), (-3644728405/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 2 => ⟨((123032775/288230376151711744), (4276958691/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 3 => ⟨((-1512554511/9223372036854775808), (-3752882635/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 4 => ⟨((559690345/36893488147419103232), (1305548999/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-2345571695/2361183241434822606848), (-2788896137/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((63007325/1180591620717411303424), (431250773/37778931862957161709568)), (13/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-2984715075/1208925819614629174706176), (689157585/2417851639229258349412352)), (3/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((1925063243/19342813113834066795298816), (-56729699/1208925819614629174706176)), (5/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-4248556743/1237940039285380274899124224), (4088851829/1237940039285380274899124224)), (17/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((1847734313/19807040628566084398385987584), (-222421011/1237940039285380274899124224)), (7/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-12810311/9903520314283042199192993792), (2654029393/316912650057057350374175801344)), (21/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-609194159/10141204801825835211973625643008), (-3498356165/10141204801825835211973625643008)), (33/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5412659053/268435456), (390275625/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((5612421711/4294967296), (90526577/536870912)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((593927157/68719476736), (-208156989/68719476736)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-1536711063/17592186044416), (2454597787/35184372088832)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((2448805131/2251799813685248), (-1951506689/1125899906842624)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-1438657771/144115188075855872), (6312916343/144115188075855872)), (33/72057594037927936), by norm_num⟩
  | 6 => ⟨((-564404045/4611686018427387904), (-5021369951/4611686018427387904)), (87/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1828202047/147573952589676412928), (1903722839/73786976294838206464)), (117/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2614254319/4722366482869645213696), (-2626257675/4722366482869645213696)), (75/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1515584925/75557863725914323419136), (736794817/75557863725914323419136)), (3/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-3130206517/4835703278458516698824704), (-739524725/9671406556917033397649408)), (507/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((5885886581/309485009821345068724781056), (-1298133779/309485009821345068724781056)), (659/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-4997733103/9903520314283042199192993792), (1537132861/4951760157141521099596496896)), (879/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-93739257/1152921504606846976), (-6517270387/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 1 => ⟨((1728633727/18446744073709551616), (4289008725/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-1279292217/73786976294838206464), (-1492055999/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 3 => ⟨((4467755609/2361183241434822606848), (2656091559/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-2880334857/18889465931478580854784), (-1232145065/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((2984715075/302231454903657293676544), (-344578793/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-5133501981/9671406556917033397649408), (1210233579/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((1820810033/77371252455336267181195264), (-876182535/38685626227668133590597632)), (27/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-1979715335/2475880078570760549798248448), (3812931617/2475880078570760549798248448)), (13/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((1073626065/79228162514264337593543950336), (-3475514681/39614081257132168796771975168)), (3/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((957305107/1267650600228229401496703205376), (5497416829/1267650600228229401496703205376)), (11/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-32187673/316912650057057350374175801344), (-3788259669/20282409603651670423947251286016)), (39/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((2390475125/324518553658426726783156020576256), (2213962343/324518553658426726783156020576256)), (17/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5412659053/268435456), (390275625/33554432)), (9/268435456), by norm_num⟩
  | 1 => ⟨((5612421711/4294967296), (724212617/4294967296)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((2375708623/274877906944), (-1665255923/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-3073422059/35184372088832), (2454597827/35184372088832)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((612201197/562949953421312), (-3903013451/2251799813685248)), (25/2251799813685248), by norm_num⟩
  | 5 => ⟨((-359664087/36028797018963968), (6312916179/144115188075855872)), (67/144115188075855872), by norm_num⟩
  | 6 => ⟨((-564406493/4611686018427387904), (-5021368797/4611686018427387904)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((114262845/9223372036854775808), (118982573/4611686018427387904)), (59/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2614258095/4722366482869645213696), (-1313125201/2361183241434822606848)), (151/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1515585949/75557863725914323419136), (184197047/18889465931478580854784)), (193/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-3130202865/4835703278458516698824704), (-739482783/9671406556917033397649408)), (127/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((1471463787/77371252455336267181195264), (-1298191583/309485009821345068724781056)), (165/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-4997660151/9903520314283042199192993792), (3074333287/9903520314283042199192993792)), (55/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2046867547/590295810358705651712), (2387289599/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-5361306731/4722366482869645213696), (-1593654935/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 2 => ⟨((6912803657/37778931862957161709568), (739287039/18889465931478580854784)), (21/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-2984715075/151115727451828646838272), (344578793/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((1925063243/1208925819614629174706176), (-56729699/75557863725914323419136)), (19/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-3823701069/38685626227668133590597632), (1839983323/19342813113834066795298816)), (7/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((2771601469/618970019642690137449562112), (-667263033/77371252455336267181195264)), (9/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((-966263457/9903520314283042199192993792), (6255926427/9903520314283042199192993792)), (45/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-538484123/79228162514264337593543950336), (-6184593933/158456325028528675187087900672)), (13/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((354064403/316912650057057350374175801344), (5208857045/2535301200456458802993406410752)), (7/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-986070989/10141204801825835211973625643008), (-3653037867/40564819207303340847894502572032)), (57/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((4296402703/649037107316853453566312041152512), (1926021069/649037107316853453566312041152512)), (7/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-1991978353/5192296858534827628530496329220096), (-382735391/10384593717069655257060992658440192)), (53/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5412659053/268435456), (390275625/33554432)), (5/134217728), by norm_num⟩
  | 1 => ⟨((5612421711/4294967296), (724212617/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((2375708623/274877906944), (-1665255923/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-768355515/8796093022208), (2454597827/35184372088832)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((306100599/281474976710656), (-3903013453/2251799813685248)), (13/1125899906842624), by norm_num⟩
  | 5 => ⟨((-719328181/72057594037927936), (6312916193/144115188075855872)), (17/36028797018963968), by norm_num⟩
  | 6 => ⟨((-70550809/576460752303423488), (-5021368837/4611686018427387904)), (89/4611686018427387904), by norm_num⟩
  | 7 => ⟨((914102753/73786976294838206464), (3807442429/147573952589676412928)), (119/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2614258127/4722366482869645213696), (-1313125293/2361183241434822606848)), (19/590295810358705651712), by norm_num⟩
  | 9 => ⟨((3031172067/151115727451828646838272), (736788343/75557863725914323419136)), (97/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-3130203335/4835703278458516698824704), (-369741827/4835703278458516698824704)), (509/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((5885857197/309485009821345068724781056), (-1298190665/309485009821345068724781056)), (661/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-2498831975/4951760157141521099596496896), (1537166461/4951760157141521099596496896)), (881/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2793051983/75557863725914323419136), (-1194807337/151115727451828646838272)), (25/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((7235672909/604462909807314587353088), (-835342527/604462909807314587353088)), (1/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((-4666819983/2417851639229258349412352), (137526543/151115727451828646838272)), (13/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((482790539/2417851639229258349412352), (-3717138027/19342813113834066795298816)), (15/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((-1049849041/77371252455336267181195264), (2022009191/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((1024824879/2475880078570760549798248448), (-6635073483/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 6 => ⟨((761492699/19807040628566084398385987584), (4372945205/19807040628566084398385987584)), (41/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-160938365/19807040628566084398385987584), (-4735324587/316912650057057350374175801344)), (7/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((1120535215/1267650600228229401496703205376), (2075589697/2535301200456458802993406410752)), (9/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((-2983612987/40564819207303340847894502572032), (-668757315/20282409603651670423947251286016)), (45/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((6639927843/1298074214633706907132624082305024), (318946159/649037107316853453566312041152512)), (25/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-397347623/1298074214633706907132624082305024), (1487762285/20769187434139310514121985316880384)), (55/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((654938549/41538374868278621028243970633760768), (-813094933/83076749736557242056487941267521536)), (113/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5412659053/268435456), (390275625/33554432)), (11/268435456), by norm_num⟩
  | 1 => ⟨((5612421711/4294967296), (724212617/4294967296)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((2375708623/274877906944), (-1665255923/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-768355515/8796093022208), (2454597827/35184372088832)), (5/17592186044416), by norm_num⟩
  | 4 => ⟨((306100599/281474976710656), (-3903013453/2251799813685248)), (27/2251799813685248), by norm_num⟩
  | 5 => ⟨((-719328181/72057594037927936), (6312916193/144115188075855872)), (69/144115188075855872), by norm_num⟩
  | 6 => ⟨((-70550809/576460752303423488), (-1255342209/1152921504606846976)), (45/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1828205505/147573952589676412928), (3807442427/147573952589676412928)), (15/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-2614258123/4722366482869645213696), (-1313125291/2361183241434822606848)), (153/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((378896507/18889465931478580854784), (1473576681/151115727451828646838272)), (195/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-6260406621/9671406556917033397649408), (-739483649/9671406556917033397649408)), (255/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((2942928551/154742504910672534362390528), (-1298190643/309485009821345068724781056)), (331/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-2498831897/4951760157141521099596496896), (3074332825/9903520314283042199192993792)), (441/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3779953241/9671406556917033397649408), (-445565849/2417851639229258349412352)), (15/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((-293281989/2417851639229258349412352), (2258059231/19342813113834066795298816)), (25/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((1275508901/77371252455336267181195264), (-4913260135/154742504910672534362390528)), (23/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((-518794133/618970019642690137449562112), (6717708097/1237940039285380274899124224)), (31/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((-1156464737/9903520314283042199192993792), (-3320555095/4951760157141521099596496896)), (73/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((1368718895/39614081257132168796771975168), (5034014291/79228162514264337593543950336)), (71/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((-794143419/158456325028528675187087900672), (-2942015345/633825300114114700748351602688)), (61/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((169918399/316912650057057350374175801344), (2437510179/10141204801825835211973625643008)), (95/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((-7562950779/162259276829213363391578010288128), (-726566359/162259276829213363391578010288128)), (67/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((1106314755/324518553658426726783156020576256), (-1035575195/1298074214633706907132624082305024)), (45/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((-1094107233/5192296858534827628530496329220096), (2716630587/20769187434139310514121985316880384)), (113/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((3545601389/332306998946228968225951765070086144), (-4299344623/332306998946228968225951765070086144)), (135/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((-2061019211/5316911983139663491615228241121378304), (5410501273/5316911983139663491615228241121378304)), (153/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5412659053/268435456), (390275625/33554432)), (3/67108864), by norm_num⟩
  | 1 => ⟨((5612421711/4294967296), (724212617/4294967296)), (1/536870912), by norm_num⟩
  | 2 => ⟨((2375708623/274877906944), (-1665255923/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-768355515/8796093022208), (2454597827/35184372088832)), (11/35184372088832), by norm_num⟩
  | 4 => ⟨((306100599/281474976710656), (-3903013453/2251799813685248)), (7/562949953421312), by norm_num⟩
  | 5 => ⟨((-719328181/72057594037927936), (6312916193/144115188075855872)), (35/72057594037927936), by norm_num⟩
  | 6 => ⟨((-70550809/576460752303423488), (-1255342209/1152921504606846976)), (91/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1828205505/147573952589676412928), (3807442427/147573952589676412928)), (121/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2614258123/4722366482869645213696), (-1313125291/2361183241434822606848)), (77/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((3031172057/151115727451828646838272), (1473576681/151115727451828646838272)), (49/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-6260406623/9671406556917033397649408), (-90269/1180591620717411303424)), (511/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((5885857105/309485009821345068724781056), (-1298190647/309485009821345068724781056)), (663/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-2498831899/4951760157141521099596496896), (3074332835/9903520314283042199192993792)), (883/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((711428259824179/2097152), (-482230639235529/1048576)), (53833281/1048576), by norm_num⟩
  | 1 => ⟨((4166720691/8), (-4350065283/8)), (309/4), by norm_num⟩
  | 2 => ⟨((3101480827/8), (-632733721/2)), (235/4), by norm_num⟩
  | 3 => ⟨(188555568, (-961072987/8)), 30, by norm_num⟩
  | 4 => ⟨((1085644183/16), (-132760573/4)), (741/64), by norm_num⟩
  | 5 => ⟨((4953976331/256), (-111969521/16)), (923/256), by norm_num⟩
  | 6 => ⟨((2339373981/512), (-290109729/256)), (967/1024), by norm_num⟩
  | 7 => ⟨((1885043381/2048), (-542693525/4096)), (875/4096), by norm_num⟩
  | 8 => ⟨((2649489253/16384), (-245300319/32768)), (1399/32768), by norm_num⟩
  | 9 => ⟨((3302496461/131072), (39041809/32768)), (2005/262144), by norm_num⟩
  | 10 => ⟨((1849304577/524288), (512893221/1048576)), (653/524288), by norm_num⟩
  | 11 => ⟨((1880478109/4194304), (863022205/8388608)), (1563/8388608), by norm_num⟩
  | 12 => ⟨((3502117717/67108864), (562350825/33554432)), (1731/67108864), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1610241271849493/10141204801825835211973625643008), (-304567087821/2535301200456458802993406410752)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1813679109898169/633825300114114700748351602688), (-1494671849855/633825300114114700748351602688)), (71551/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((964529038153277/19807040628566084398385987584), (-421480142213/9903520314283042199192993792)), (40359/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1931329844889781/2475880078570760549798248448), (-1795065623989/2475880078570760549798248448)), (1343/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1813040351782647/154742504910672534362390528), (-1799289690381/154742504910672534362390528)), (21541/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((198604325588667/1208925819614629174706176), (-1691335443683/9671406556917033397649408)), (81005/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((323301736451011/151115727451828646838272), (-1484435713801/604462909807314587353088)), (35553/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((971905257564717/37778931862957161709568), (-605177905621/18889465931478580854784)), (115973/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((334907809649415/1180591620717411303424), (-1823008351713/4722366482869645213696)), (87355/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1679451407899237/590295810358705651712), (-2518846846151/590295810358705651712)), (120725/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1896170155197249/73786976294838206464), (-3166986924837/73786976294838206464)), (151831/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1904703849186129/9223372036854775808), (-3588383919911/9223372036854775808)), (43023/2305843009213693952), by norm_num⟩
  | 6 => ⟨((104767805559825/72057594037927936), (-452570957819/144115188075855872)), (43427/288230376151711744), by norm_num⟩
  | 5 => ⟨((1266969204333159/144115188075855872), (-1602295521167/72057594037927936)), (76917/72057594037927936), by norm_num⟩
  | 4 => ⟨((200122554356111/4503599627370496), (-4881055577939/36028797018963968)), (234481/36028797018963968), by norm_num⟩
  | 3 => ⟨((813641278176525/4503599627370496), (-6233352381667/9007199254740992)), (299747/9007199254740992), by norm_num⟩
  | 2 => ⟨((1254049321943087/2251799813685248), (-804494447105/281474976710656)), (309955/2251799813685248), by norm_num⟩
  | 1 => ⟨((661701078466401/562949953421312), (-10176744139679/1125899906842624)), (30707/70368744177664), by norm_num⟩
  | 0 => ⟨((1542699922729299/1125899906842624), (-22545527628759/1125899906842624)), (1093467/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1542699922729299/1125899906842624), (-22545527628759/1125899906842624)), (4171245579246139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2113344833152665/1125899906842624), (-15445859582809/281474976710656)), (1520157/562949953421312), by norm_num⟩
  | 2 => ⟨((495426942865977/140737488355328), (-115969198841025/562949953421312)), (5873589/562949953421312), by norm_num⟩
  | 3 => ⟨((869019708727019/70368744177664), (-204118555474599/140737488355328)), (683947/8796093022208), by norm_num⟩
  | 4 => ⟨((1322993551127165/8796093022208), (-157547794920557/4398046511104)), (9438375/4398046511104), by norm_num⟩
  | 5 => ⟨((1466406290250741/68719476736), (-5785225539573/536870912)), (54928151/68719476736), by norm_num⟩
  | 6 => ⟨((711428259824179/2097152), (-482230639235529/1048576)), (53833281/1048576), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((5412659053/268435456), (390275625/33554432)), (3/67108864), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2252800/36517561), (-7399680/36517561)), 0, by norm_num⟩
  | 1 => ⟨((24840078131200/1333532261388721), (16669999104000/1333532261388721)), 0, by norm_num⟩
  | 2 => ⟨((-4048599603/2199023255552), (3302202039/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-1677500115/17592186044416), (-4096389927/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((1867104261/70368744177664), (-348831273/140737488355328)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((-1277453369/2251799813685248), (6225562591/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 6 => ⟨((-4730800509/18014398509481984), (-1285830319/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 7 => ⟨((3251806787/144115188075855872), (-1599941071/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 8 => ⟨((447796433/288230376151711744), (3425313551/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-402291481/1152921504606846976), (303287225/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 10 => ⟨((605035185/147573952589676412928), (-2758247379/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 11 => ⟨((2161002629/590295810358705651712), (231458861/147573952589676412928)), (29/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-80229843/295147905179352825856), (3046206913/9444732965739290427392)), (1/295147905179352825856), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (5781/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (5781/1280)))⁻¹=value ((2252800/36517561), (-7399680/36517561)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/36517561), (-7399680/36517561))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3891200/42661561), (-7399680/42661561)), 0, by norm_num⟩
  | 1 => ⟨((19806913331200/1820008786956721), (28793634816000/1820008786956721)), 0, by norm_num⟩
  | 2 => ⟨((-2054289939/1099511627776), (244437871/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((1159805847/17592186044416), (-3028908355/17592186044416)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((3356635931/281474976710656), (1909754809/140737488355328)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((-1937317327/1125899906842624), (467660147/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | 6 => ⟨((1529415671/36028797018963968), (-3029478915/18014398509481984)), (11/36028797018963968), by norm_num⟩
  | 7 => ⟨((3645725651/288230376151711744), (3271685559/288230376151711744)), (13/288230376151711744), by norm_num⟩
  | 8 => ⟨((-3600025217/2305843009213693952), (1335761749/2305843009213693952)), (15/2305843009213693952), by norm_num⟩
  | 9 => ⟨((773381663/36893488147419103232), (-2985052583/18446744073709551616)), (33/36893488147419103232), by norm_num⟩
  | 10 => ⟨((1929956809/147573952589676412928), (2714729547/295147905179352825856)), (9/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-1645876287/1180591620717411303424), (843783939/1180591620717411303424)), (39/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((30135357/18889465931478580854784), (-5799052653/37778931862957161709568)), (21/9444732965739290427392), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (5781/1280)))⁻¹=value ((3891200/42661561), (-7399680/42661561)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/42661561), (-7399680/42661561))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-45989168742400/1557896156172721), (-45463633920000/1557896156172721)), 0, by norm_num⟩
  | 1 => ⟨((2128767929/274877906944), (-1825171603/549755813888)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((59980275/2199023255552), (5626652595/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-5674611925/35184372088832), (-2134963145/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((2055890557/140737488355328), (-1129293041/70368744177664)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((1298590643/1125899906842624), (2645121149/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 6 => ⟨((-5495508345/18014398509481984), (228909139/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 7 => ⟨((1428943961/144115188075855872), (-2417862461/72057594037927936)), (13/144115188075855872), by norm_num⟩
  | 8 => ⟨((3591198341/1152921504606846976), (689358169/288230376151711744)), (15/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-3411677263/9223372036854775808), (1049550371/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-1324921625/147573952589676412928), (-1718464883/36893488147419103232)), (41/147573952589676412928), by norm_num⟩
  | 11 => ⟨((5967881545/1180591620717411303424), (251971737/295147905179352825856)), (23/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-1291211327/4722366482869645213696), (4495970077/9444732965739290427392)), (13/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((27/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((614400/5786929), (-2466560/17360787)), 0, by norm_num⟩
  | 1 => ⟨((1343265996800/301396925259369), (505151488000/33488547251041)), 0, by norm_num⟩
  | 2 => ⟨((-5753316347/4398046511104), (-1064655611/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((3653425753/35184372088832), (-2365365931/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-207289533/281474976710656), (6161580721/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((-1662799781/2251799813685248), (-1426157665/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((758326913/9007199254740992), (-1357267151/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | 7 => ⟨((-902517203/288230376151711744), (2012049967/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 8 => ⟨((-3040712159/9223372036854775808), (-1367385783/2305843009213693952)), (29/9223372036854775808), by norm_num⟩
  | 9 => ⟨((4399707677/73786976294838206464), (1161635/144115188075855872)), (15/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-137904827/36893488147419103232), (2247798247/590295810358705651712)), (31/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-340387889/4722366482869645213696), (-4417103999/9444732965739290427392)), (31/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((5598759067/151115727451828646838272), (2977944163/151115727451828646838272)), (31/37778931862957161709568), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (5781/1280)))⁻¹=value ((614400/5786929), (-2466560/17360787)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/5786929), (-2466560/17360787))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-125075119/17179869184), (602404835/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((724768565/1099511627776), (-4459909521/2199023255552)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((322975495/1099511627776), (1259794945/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-4340797867/70368744177664), (1557487635/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((547855651/562949953421312), (-164246607/17592186044416)), (7/562949953421312), by norm_num⟩
  | 5 => ⟨((150281755/140737488355328), (2928764341/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 6 => ⟨((-4743562357/36028797018963968), (3147980405/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 7 => ⟨((-422588733/144115188075855872), (-5465542719/288230376151711744)), (17/288230376151711744), by norm_num⟩
  | 8 => ⟨((5011121931/2305843009213693952), (1405858911/2305843009213693952)), (21/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-3055059221/18446744073709551616), (1832985837/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-1903248871/147573952589676412928), (-3834637373/147573952589676412928)), (15/73786976294838206464), by norm_num⟩
  | 11 => ⟨((7528660861/2361183241434822606848), (-388034989/2361183241434822606848)), (17/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-2247567891/18889465931478580854784), (6131854751/18889465931478580854784)), (77/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((35/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7168000/64779961), (-7399680/64779961)), 0, by norm_num⟩
  | 1 => ⟨((1687520051200/4196443347161521), (53040906240000/4196443347161521)), 0, by norm_num⟩
  | 2 => ⟨((-3272760315/4398046511104), (-1487247843/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((2807625165/35184372088832), (-357665417/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-580480509/140737488355328), (1361989127/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-433841601/9007199254740992), (-2266562413/4503599627370496)), (9/9007199254740992), by norm_num⟩
  | 6 => ⟨((4526517045/144115188075855872), (904080499/36028797018963968)), (17/144115188075855872), by norm_num⟩
  | 7 => ⟨((-3655803357/1152921504606846976), (467612605/1152921504606846976)), (1/72057594037927936), by norm_num⟩
  | 8 => ⟨((2808845757/18446744073709551616), (-3754694713/18446744073709551616)), (15/9223372036854775808), by norm_num⟩
  | 9 => ⟨((118087953/36893488147419103232), (5890489681/295147905179352825856)), (55/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-3109564963/2361183241434822606848), (-2175520021/2361183241434822606848)), (51/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((4740665237/37778931862957161709568), (-915796557/37778931862957161709568)), (93/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-3359617577/604462909807314587353088), (5142804635/604462909807314587353088)), (21/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (5781/1280)))⁻¹=value ((7168000/64779961), (-7399680/64779961)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/64779961), (-7399680/64779961))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-748121089/1099511627776), (4190745995/4398046511104)), (3/4398046511104), by norm_num⟩
  | 1 => ⟨((-385947037/2199023255552), (-3441830775/8796093022208)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((6845576903/70368744177664), (687231065/70368744177664)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-2881577629/281474976710656), (4084540257/281474976710656)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-2749864437/2251799813685248), (-5701079267/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((7288682207/18014398509481984), (365879899/18014398509481984)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1013592391/36028797018963968), (210282729/4503599627370496)), (11/72057594037927936), by norm_num⟩
  | 7 => ⟨((-2075721383/576460752303423488), (-428982259/72057594037927936)), (15/576460752303423488), by norm_num⟩
  | 8 => ⟨((7833871521/9223372036854775808), (-526319103/9223372036854775808)), (19/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-362999951/9223372036854775808), (426925787/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-2215115119/295147905179352825856), (-2588923465/295147905179352825856)), (29/295147905179352825856), by norm_num⟩
  | 11 => ⟨((5904131611/4722366482869645213696), (-1538317523/4722366482869645213696)), (67/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-1006864441/37778931862957161709568), (5249003075/37778931862957161709568)), (39/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((43/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8806400/80754361), (-7399680/80754361)), 0, by norm_num⟩
  | 1 => ⟨((-11398708428800/6521266820518321), (65164541952000/6521266820518321)), 0, by norm_num⟩
  | 2 => ⟨((-1594355077/4398046511104), (-1374255699/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1702874393/35184372088832), (1229087643/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-3872211073/1125899906842624), (178041329/140737488355328)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((2334055861/18014398509481984), (-2040575771/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 6 => ⟨((955449171/288230376151711744), (5271444787/288230376151711744)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1174452291/1152921504606846976), (-487310317/576460752303423488)), (15/2305843009213693952), by norm_num⟩
  | 8 => ⟨((6956237063/73786976294838206464), (-42666467/73786976294838206464)), (49/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-1509359671/295147905179352825856), (1284132909/295147905179352825856)), (41/590295810358705651712), by norm_num⟩
  | 10 => ⟨((375444977/4722366482869645213696), (-2226739593/4722366482869645213696)), (67/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((2609561465/151115727451828646838272), (4435719773/151115727451828646838272)), (109/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-5528246231/2417851639229258349412352), (-1956828345/2417851639229258349412352)), (11/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (5781/1280)))⁻¹=value ((8806400/80754361), (-7399680/80754361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/80754361), (-7399680/80754361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((115341513/8796093022208), (2924860599/17592186044416)), (3/17592186044416), by norm_num⟩
  | 1 => ⟨((-4456209335/70368744177664), (-2466663387/70368744177664)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((4661941129/281474976710656), (-621998559/70368744177664)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-160345841/562949953421312), (2117444039/562949953421312)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-293839381/562949953421312), (-3443776951/9007199254740992)), (13/9007199254740992), by norm_num⟩
  | 5 => ⟨((51769637/562949953421312), (-1366455791/36028797018963968)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((-297750617/144115188075855872), (4021105733/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((-3377400655/2305843009213693952), (-2708491497/2305843009213693952)), (21/2305843009213693952), by norm_num⟩
  | 8 => ⟨((2039060605/9223372036854775808), (-803453427/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-285729399/73786976294838206464), (1054427567/36893488147419103232)), (9/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-802948667/295147905179352825856), (-2366654031/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((3274244207/9444732965739290427392), (-781194039/4722366482869645213696)), (13/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-226473103/151115727451828646838272), (6421946319/151115727451828646838272)), (15/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((51/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3481600/33335187), (-2466560/33335187)), 0, by norm_num⟩
  | 1 => ⟨((-1006270054400/370411564108323), (8587575296000/1111234692324969)), 0, by norm_num⟩
  | 2 => ⟨((-1266997611/8796093022208), (-4433826485/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((3683189883/140737488355328), (738660003/35184372088832)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-2413208693/1125899906842624), (-72119939/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((525427003/4503599627370496), (-653980249/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-1963639715/576460752303423488), (2336938247/288230376151711744)), (15/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1125966691/9223372036854775808), (-1266889763/2305843009213693952)), (23/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1970242925/73786976294838206464), (3567629411/147573952589676412928)), (17/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-2702125839/1180591620717411303424), (-162087813/590295810358705651712)), (49/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((4899241131/37778931862957161709568), (-2657278941/37778931862957161709568)), (71/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-2520546227/604462909807314587353088), (5120320355/604462909807314587353088)), (51/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-924919037/9671406556917033397649408), (-5770235721/9671406556917033397649408)), (147/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (5781/1280)))⁻¹=value ((3481600/33335187), (-2466560/33335187)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/33335187), (-2466560/33335187))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1924090645/140737488355328), (2307279965/140737488355328)), (9/281474976710656), by norm_num⟩
  | 1 => ⟨((-5926806717/562949953421312), (23725489/35184372088832)), (11/562949953421312), by norm_num⟩
  | 2 => ⟨((901080193/562949953421312), (-1448695937/562949953421312)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((585878221/2251799813685248), (5472065237/9007199254740992)), (15/9007199254740992), by norm_num⟩
  | 4 => ⟨((-4282676721/36028797018963968), (-421720029/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 5 => ⟨((3998290685/288230376151711744), (-1004540829/72057594037927936)), (23/288230376151711744), by norm_num⟩
  | 6 => ⟨((1401593455/2305843009213693952), (6574326853/2305843009213693952)), (35/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-3478281927/9223372036854775808), (-324442567/2305843009213693952)), (25/9223372036854775808), by norm_num⟩
  | 8 => ⟨((766333461/18446744073709551616), (-2365621847/73786976294838206464)), (33/73786976294838206464), by norm_num⟩
  | 9 => ⟨((858270607/1180591620717411303424), (7653389519/1180591620717411303424)), (21/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-3354116859/4722366482869645213696), (-1509778951/4722366482869645213696)), (53/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1376775737/18889465931478580854784), (-1983779387/37778931862957161709568)), (1/590295810358705651712), by norm_num⟩
  | 12 => ⟨((84960065/75557863725914323419136), (3018690747/302231454903657293676544)), (149/604462909807314587353088), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((59/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12083200/122533561), (-7399680/122533561)), 0, by norm_num⟩
  | 1 => ⟨((-45624229068800/15014473571340721), (89411813376000/15014473571340721)), 0, by norm_num⟩
  | 2 => ⟨((-263752525/8796093022208), (-6779480945/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((57678013/4398046511104), (1273356539/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-2686400717/2251799813685248), (-2234800715/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((664776603/9007199254740992), (-832651379/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((-3793225299/1152921504606846976), (1613081863/576460752303423488)), (13/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1433841997/18446744073709551616), (-4377643765/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 8 => ⟨((983747687/295147905179352825856), (4146189277/295147905179352825856)), (3/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-2779143515/4722366482869645213696), (-349453781/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1771521719/37778931862957161709568), (431404641/37778931862957161709568)), (21/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-802976991/302231454903657293676544), (1031024671/1208925819614629174706176)), (27/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((2035744227/19342813113834066795298816), (-2365077331/19342813113834066795298816)), (35/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (5781/1280)))⁻¹=value ((12083200/122533561), (-7399680/122533561)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/122533561), (-7399680/122533561))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2632572181/1125899906842624), (1781281157/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2559491513/2251799813685248), (3305083169/4503599627370496)), (1/281474976710656), by norm_num⟩
  | 2 => ⟨((40892747/1125899906842624), (-1895710117/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((2639598595/36028797018963968), (2379607027/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 4 => ⟨((-1350506577/72057594037927936), (275654129/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((769363109/576460752303423488), (-213791517/72057594037927936)), (21/1152921504606846976), by norm_num⟩
  | 6 => ⟨((18439523/72057594037927936), (496950445/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((-2631138693/36893488147419103232), (-341422903/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1716753581/295147905179352825856), (-4483579169/590295810358705651712)), (1/9223372036854775808), by norm_num⟩
  | 9 => ⟨((119747981/295147905179352825856), (5409435427/4722366482869645213696)), (83/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-5437850741/37778931862957161709568), (-1241549863/37778931862957161709568)), (105/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((914675701/75557863725914323419136), (-232442575/18889465931478580854784)), (129/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((73854419/151115727451828646838272), (4567992655/2417851639229258349412352)), (153/2417851639229258349412352), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((67/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13721600/148338361), (-7399680/148338361)), 0, by norm_num⟩
  | 1 => ⟨((-66763521228800/22004269344166321), (101535449088000/22004269344166321)), 0, by norm_num⟩
  | 2 => ⟨((222015923/8796093022208), (-5085814873/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((425251769/70368744177664), (3940785671/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1415711789/2251799813685248), (-2237424027/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((747047267/18014398509481984), (525793007/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-4842273819/2305843009213693952), (1606804493/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((22985417/288230376151711744), (-3121469315/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-931540737/590295810358705651712), (1742028115/295147905179352825856)), (15/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-701028203/9444732965739290427392), (-2950008559/9444732965739290427392)), (9/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((3392066377/302231454903657293676544), (3806589511/302231454903657293676544)), (21/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-1007320315/1208925819614629174706176), (-1463265077/4835703278458516698824704)), (49/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((7131358725/154742504910672534362390528), (-1050253359/154742504910672534362390528)), (113/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (5781/1280)))⁻¹=value ((13721600/148338361), (-7399680/148338361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/148338361), (-7399680/148338361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4607148945/18014398509481984), (-782985915/18014398509481984)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1428141191/18014398509481984), (4790899447/36028797018963968)), (21/36028797018963968), by norm_num⟩
  | 2 => ⟨((-2433065/140737488355328), (-220119715/4503599627370496)), (17/72057594037927936), by norm_num⟩
  | 3 => ⟨((1742407229/144115188075855872), (1234847677/288230376151711744)), (19/288230376151711744), by norm_num⟩
  | 4 => ⟨((-2546685511/1152921504606846976), (1605090993/1152921504606846976)), (9/576460752303423488), by norm_num⟩
  | 5 => ⟨((98904757/2305843009213693952), (-4247457241/9223372036854775808)), (33/9223372036854775808), by norm_num⟩
  | 6 => ⟨((4034310313/73786976294838206464), (1825317799/36893488147419103232)), (25/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-3125790217/295147905179352825856), (162697781/73786976294838206464)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((701252965/1180591620717411303424), (-50133895/36893488147419103232)), (53/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1909580059/18889465931478580854784), (3086278151/18889465931478580854784)), (69/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-7164326097/302231454903657293676544), (-270521427/302231454903657293676544)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1964081027/1208925819614629174706176), (-1385425061/604462909807314587353088)), (111/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((2349718109/19342813113834066795298816), (5743099781/19342813113834066795298816)), (133/9671406556917033397649408), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5120000/59139987), (-2466560/59139987)), 0, by norm_num⟩
  | 1 => ⟨((-3355080294400/1165846020786723), (12628787200000/3497538062360169)), 0, by norm_num⟩
  | 2 => ⟨((866849045/17592186044416), (-29729721/137438953472)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((1338651871/562949953421312), (5849661113/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-1439461777/4503599627370496), (-1802394697/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1598344479/72057594037927936), (384020511/36028797018963968)), (5/144115188075855872), by norm_num⟩
  | 6 => ⟨((-5453064707/4611686018427387904), (5433901/4611686018427387904)), (11/4611686018427387904), by norm_num⟩
  | 7 => ⟨((3774946823/73786976294838206464), (-1823217561/73786976294838206464)), (3/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-125385995/73786976294838206464), (157642973/73786976294838206464)), (13/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1095772195/37778931862957161709568), (-4832592371/37778931862957161709568)), (7/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((853503793/604462909807314587353088), (116019897/18889465931478580854784)), (15/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-228734927/1208925819614629174706176), (-4573144491/19342813113834066795298816)), (31/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((2030294697/154742504910672534362390528), (486556923/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (5781/1280)))⁻¹=value ((5120000/59139987), (-2466560/59139987)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/59139987), (-2466560/59139987))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2929634849/144115188075855872), (-2079499569/144115188075855872)), (17/144115188075855872), by norm_num⟩
  | 1 => ⟨((-546627087/288230376151711744), (4573385081/288230376151711744)), (3/36028797018963968), by norm_num⟩
  | 2 => ⟨((-2181315923/576460752303423488), (-1221173319/288230376151711744)), (21/576460752303423488), by norm_num⟩
  | 3 => ⟨((6813991061/4611686018427387904), (-66549463/2305843009213693952)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((-906316993/4611686018427387904), (2257111289/9223372036854775808)), (47/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-892032109/73786976294838206464), (-4157794527/73786976294838206464)), (11/18446744073709551616), by norm_num⟩
  | 6 => ⟨((5014746801/590295810358705651712), (77292097/18446744073709551616)), (69/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-3022370799/2361183241434822606848), (1483721509/2361183241434822606848)), (53/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((349957933/9444732965739290427392), (-1854109049/9444732965739290427392)), (19/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((682145119/37778931862957161709568), (2901303433/151115727451828646838272)), (101/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-3955034889/1208925819614629174706176), (276013059/604462909807314587353088)), (131/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((1713319731/9671406556917033397649408), (-3425381695/9671406556917033397649408)), (165/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1749947585/77371252455336267181195264), (767212045/19342813113834066795298816)), (101/38685626227668133590597632), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((83/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16998400/209778361), (-7399680/209778361)), 0, by norm_num⟩
  | 1 => ⟨((-117095169228800/44006960743846321), (125782720512000/44006960743846321)), 0, by norm_num⟩
  | 2 => ⟨((2019351527/35184372088832), (-2862795549/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((76669461/140737488355328), (1070352941/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1406974847/9007199254740992), (-5377701035/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((3341656741/288230376151711744), (2691983507/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-731463761/1152921504606846976), (-1604148057/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 7 => ⟨((2123000495/73786976294838206464), (-611419851/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-322487561/295147905179352825856), (1594528915/2361183241434822606848)), (25/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((611219891/18889465931478580854784), (-27526003/590295810358705651712)), (3/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-590624815/1208925819614629174706176), (5947783841/2417851639229258349412352)), (23/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-114083947/4835703278458516698824704), (-1047235545/9671406556917033397649408)), (43/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((3547423135/1237940039285380274899124224), (1228951105/309485009821345068724781056)), (81/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (5781/1280)))⁻¹=value ((16998400/209778361), (-7399680/209778361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/209778361), (-7399680/209778361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2624596625/2305843009213693952), (-4349468695/2305843009213693952)), (33/2305843009213693952), by norm_num⟩
  | 1 => ⟨((453296917/1152921504606846976), (417677939/288230376151711744)), (49/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-4589108431/9223372036854775808), (-2412926769/9223372036854775808)), (45/9223372036854775808), by norm_num⟩
  | 3 => ⟨((5293497469/36893488147419103232), (-1941833535/36893488147419103232)), (27/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-1797057141/147573952589676412928), (1159365971/36893488147419103232)), (55/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-1787472475/590295810358705651712), (-3321863337/590295810358705651712)), (13/147573952589676412928), by norm_num⟩
  | 6 => ⟨((4996782219/4722366482869645213696), (1012697035/4722366482869645213696)), (21/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-605440307/4722366482869645213696), (500771941/4722366482869645213696)), (33/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-90390587/151115727451828646838272), (-7184550405/302231454903657293676544)), (95/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((1561825731/604462909807314587353088), (2262346919/1208925819614629174706176)), (129/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-233730753/604462909807314587353088), (1181377331/9671406556917033397649408)), (85/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((594731489/38685626227668133590597632), (-1807260767/38685626227668133590597632)), (27/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((2124851043/618970019642690137449562112), (354363627/77371252455336267181195264)), (267/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((91/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((18636800/245413561), (-7399680/245413561)), 0, by norm_num⟩
  | 1 => ⟨((-146287525068800/60227815922700721), (137906356224000/60227815922700721)), 0, by norm_num⟩
  | 2 => ⟨((2030344215/35184372088832), (-2173691603/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-184826771/562949953421312), (3130885137/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1285860063/18014398509481984), (-973333973/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((3440641591/576460752303423488), (4110245195/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-3081722069/9223372036854775808), (-1667134307/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((4548710215/295147905179352825856), (538929729/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-5786888693/9444732965739290427392), (769805037/4722366482869645213696)), (27/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((3144291291/151115727451828646838272), (-2331233181/151115727451828646838272)), (3/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-2695802023/4835703278458516698824704), (271841033/302231454903657293676544)), (21/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((588607625/77371252455336267181195264), (-6585326309/154742504910672534362390528)), (9/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((436647137/1237940039285380274899124224), (4284699671/2475880078570760549798248448)), (31/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (5781/1280)))⁻¹=value ((18636800/245413561), (-7399680/245413561)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/245413561), (-7399680/245413561))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((68168221/2305843009213693952), (-6550989467/36893488147419103232)), (57/36893488147419103232), by norm_num⟩
  | 1 => ⟨((692726263/9223372036854775808), (3887801145/36893488147419103232)), (45/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-7395343107/147573952589676412928), (-285319929/36893488147419103232)), (85/147573952589676412928), by norm_num⟩
  | 3 => ⟨((835884829/73786976294838206464), (-324111763/36893488147419103232)), (27/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-649171461/2361183241434822606848), (7692564449/2361183241434822606848)), (113/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-258732635/590295810358705651712), (-1095346709/2361183241434822606848)), (109/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1043224123/9444732965739290427392), (-43563645/9444732965739290427392)), (91/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-3222750905/302231454903657293676544), (519798625/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-1365435497/2417851639229258349412352), (-5973019589/2417851639229258349412352)), (53/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((1505490665/4835703278458516698824704), (722901083/4835703278458516698824704)), (147/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-1537989071/38685626227668133590597632), (771875907/38685626227668133590597632)), (49/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((1197850085/1237940039285380274899124224), (-6645480147/1237940039285380274899124224)), (501/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((2193535735/4951760157141521099596496896), (2291282103/4951760157141521099596496896)), (313/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((99/8), (5781/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2252800/31591729), (-2466560/94775187)), 0, by norm_num⟩
  | 1 => ⟨((-19796026163200/8982336070884969), (5556666368000/2994112023628323)), 0, by norm_num⟩
  | 2 => ⟨((1915067007/35184372088832), (-1668603437/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-198843939/281474976710656), (4605054547/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-505041543/18014398509481984), (-2792683927/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((434780265/144115188075855872), (372003693/72057594037927936)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((-402937347/2305843009213693952), (-2671340823/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 7 => ⟨((4790235495/590295810358705651712), (852800147/295147905179352825856)), (15/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-385979645/1180591620717411303424), (48666617/18889465931478580854784)), (25/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((3512956461/302231454903657293676544), (-1313557289/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-3461158597/9671406556917033397649408), (92547765/302231454903657293676544)), (17/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((678958579/77371252455336267181195264), (-4820223577/309485009821345068724781056)), (27/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-272869901/2475880078570760549798248448), (6630556973/9903520314283042199192993792)), (85/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (5781/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (5781/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (5781/1280)))⁻¹=value ((2252800/31591729), (-2466560/94775187)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/31591729), (-2466560/94775187))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-92714973/36893488147419103232), (-495535433/36893488147419103232)), (45/295147905179352825856), by norm_num⟩
  | 1 => ⟨((2468225433/295147905179352825856), (3545380545/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 2 => ⟨((-4900788825/1180591620717411303424), (191077475/295147905179352825856)), (37/590295810358705651712), by norm_num⟩
  | 3 => ⟨((3394303043/4722366482869645213696), (-4714745611/4722366482869645213696)), (97/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((992588719/18889465931478580854784), (5372692761/18889465931478580854784)), (105/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-1847527747/37778931862957161709568), (-2352170383/75557863725914323419136)), (103/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((5987373447/604462909807314587353088), (-1650165867/604462909807314587353088)), (11/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-1740745213/2417851639229258349412352), (1795125507/1208925819614629174706176)), (71/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-1899773957/19342813113834066795298816), (-541060705/2417851639229258349412352)), (53/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((2514966241/77371252455336267181195264), (1432691613/154742504910672534362390528)), (149/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-2225305075/618970019642690137449562112), (49330841/19342813113834066795298816)), (403/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((240560601/9903520314283042199192993792), (-5404364111/9903520314283042199192993792)), (521/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((3950818493/79228162514264337593543950336), (3267431819/79228162514264337593543950336)), (41/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-966133465/137438953472), (-233695649/68719476736)), (259/274877906944), by norm_num⟩
  | 1 => ⟨((-414147557/137438953472), (-4088872693/549755813888)), (307/137438953472), by norm_num⟩
  | 2 => ⟨((353891803/274877906944), (-4070960969/1099511627776)), (711/274877906944), by norm_num⟩
  | 3 => ⟨((1131860997/1099511627776), (-1369381897/2199023255552)), (4401/2199023255552), by norm_num⟩
  | 4 => ⟨((4532728861/17592186044416), (450988847/17592186044416)), (10315/8796093022208), by norm_num⟩
  | 5 => ⟨((4662144361/140737488355328), (3581107259/140737488355328)), (39161/70368744177664), by norm_num⟩
  | 6 => ⟨((2960080627/1125899906842624), (1358596187/281474976710656)), (251137/1125899906842624), by norm_num⟩
  | 7 => ⟨((316472929/2251799813685248), (1489753187/2251799813685248)), (699885/9007199254740992), by norm_num⟩
  | 8 => ⟨((-129976523/18014398509481984), (1464803075/18014398509481984)), (216367/9007199254740992), by norm_num⟩
  | 9 => ⟨((-1057174739/288230376151711744), (4508928091/576460752303423488)), (3860309/576460752303423488), by norm_num⟩
  | 10 => ⟨((-585299005/1152921504606846976), (2663391247/4611686018427387904)), (3930353/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-3799991935/73786976294838206464), (3253160559/73786976294838206464)), (7382969/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-1679223039/295147905179352825856), (1764972705/590295810358705651712)), (12898947/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-966133465/137438953472), (-233695649/68719476736)), (519/549755813888), by norm_num⟩
  | 1 => ⟨((-414147557/137438953472), (-4088872693/549755813888)), (1229/549755813888), by norm_num⟩
  | 2 => ⟨((353891803/274877906944), (-4070960969/1099511627776)), (2845/1099511627776), by norm_num⟩
  | 3 => ⟨((1131860997/1099511627776), (-1369381897/2199023255552)), (8803/4398046511104), by norm_num⟩
  | 4 => ⟨((4532728861/17592186044416), (450988847/17592186044416)), (20631/17592186044416), by norm_num⟩
  | 5 => ⟨((4662144361/140737488355328), (3581107259/140737488355328)), (9791/17592186044416), by norm_num⟩
  | 6 => ⟨((2960080627/1125899906842624), (1358596187/281474976710656)), (251183/1125899906842624), by norm_num⟩
  | 7 => ⟨((316472929/2251799813685248), (1489753187/2251799813685248)), (350123/4503599627370496), by norm_num⟩
  | 8 => ⟨((-129976523/18014398509481984), (1464803075/18014398509481984)), (1733819/72057594037927936), by norm_num⟩
  | 9 => ⟨((-1057174739/288230376151711744), (4508928091/576460752303423488)), (485421/72057594037927936), by norm_num⟩
  | 10 => ⟨((-585299005/1152921504606846976), (2663391247/4611686018427387904)), (4022587/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-3799991935/73786976294838206464), (3253160559/73786976294838206464)), (8120839/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-1679223039/295147905179352825856), (1764972705/590295810358705651712)), (75207621/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile020Gamma
