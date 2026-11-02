/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile013Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3807/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3807/640))
  have he : value ((3/4), (3807/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/307587649), (-4872960/307587649)), 0, by norm_num⟩
  | 1 => ⟨((-228230062899200/94610161817347201), (106784096256000/94610161817347201)), 0, by norm_num⟩
  | 2 => ⟨((43341791989/562949953421312), (-33390778021/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-40941189665/18014398509481984), (49048261853/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((17117947041/288230376151711744), (-16571910799/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-22222720901/18446744073709551616), (84239067239/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((1989318151/295147905179352825856), (-50828351795/295147905179352825856)), (11/590295810358705651712), by norm_num⟩
  | 7 => ⟨((5308182005/4722366482869645213696), (14610808221/2361183241434822606848)), (9/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-26915738245/302231454903657293676544), (-15982026781/75557863725914323419136)), (7/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((46885618895/9671406556917033397649408), (16512179947/2417851639229258349412352)), (21/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-8773339711/38685626227668133590597632), (-63404027279/309485009821345068724781056)), (15/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((48038572459/4951760157141521099596496896), (425648359/77371252455336267181195264)), (11/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-15416025717/39614081257132168796771975168), (-4718904461/39614081257132168796771975168)), (1/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (3807/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (3807/1280)))⁻¹=value ((21913600/307587649), (-4872960/307587649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/307587649), (-4872960/307587649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89937301139/34359738368), (1879573809/8589934592)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((10956800/307587649), (-2436480/307587649)), 0, by norm_num⟩
  | 2 => ⟨((-57057515724800/94610161817347201), (26696024064000/94610161817347201)), 0, by norm_num⟩
  | 3 => ⟨((57789055985/4503599627370496), (-44521037361/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-40941189665/144115188075855872), (49048261853/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((13694357633/2305843009213693952), (-53030114557/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-14815147267/147573952589676412928), (56159378159/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 7 => ⟨((4547012917/9444732965739290427392), (-116179089817/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((5308182005/75557863725914323419136), (14610808221/37778931862957161709568)), (9/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-11962550331/2417851639229258349412352), (-28412492055/2417851639229258349412352)), (13/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((9377123779/38685626227668133590597632), (26419487915/77371252455336267181195264)), (9/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-51044885591/4951760157141521099596496896), (-46112019839/4951760157141521099596496896)), (23/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((64051429945/158456325028528675187087900672), (36321993301/158456325028528675187087900672)), (15/79228162514264337593543950336), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (81/20480)), 0, by norm_num⟩
  | 45 => ⟨((104571604337/4080638361600), (-160947/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-49678149063991/1915179604377600), (1114194653433/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((29096520713/1099511627776), (-6318928813/1099511627776)), (1/2199023255552), by norm_num⟩
  | 42 => ⟨((-29777878925/1099511627776), (3222706425/549755813888)), (1/2199023255552), by norm_num⟩
  | 41 => ⟨((15252330401/549755813888), (-13185641821/2199023255552)), (1/1099511627776), by norm_num⟩
  | 40 => ⟨((-62533861769/2199023255552), (6752105563/1099511627776)), (1/1099511627776), by norm_num⟩
  | 39 => ⟨((32067196753/1099511627776), (-13839871149/2199023255552)), (1/1099511627776), by norm_num⟩
  | 38 => ⟨((-65818406709/2199023255552), (14192461091/2199023255552)), (1/1099511627776), by norm_num⟩
  | 37 => ⟨((67593175569/2199023255552), (-1820418357/274877906944)), (1/1099511627776), by norm_num⟩
  | 36 => ⟨((-69466323483/2199023255552), (1869263091/274877906944)), (1/1099511627776), by norm_num⟩
  | 35 => ⟨((35723127951/1099511627776), (-15366410419/2199023255552)), (1/1099511627776), by norm_num⟩
  | 34 => ⟨((-36771182155/1099511627776), (15802101329/2199023255552)), (1/1099511627776), by norm_num⟩
  | 33 => ⟨((37882590433/1099511627776), (-16263224677/2199023255552)), (1/1099511627776), by norm_num⟩
  | 32 => ⟨((-39063276243/1099511627776), (523502317/68719476736)), (1/1099511627776), by norm_num⟩
  | 31 => ⟨((40319925377/1099511627776), (-4317807061/549755813888)), (1/1099511627776), by norm_num⟩
  | 30 => ⟨((-83320225019/2199023255552), (17823595641/2199023255552)), (1/1099511627776), by norm_num⟩
  | 29 => ⟨((43092454009/1099511627776), (-18412469629/2199023255552)), (1/2199023255552), by norm_num⟩
  | 28 => ⟨((-22313396697/549755813888), (9520796943/1099511627776)), (1/1099511627776), by norm_num⟩
  | 27 => ⟨((46274427873/1099511627776), (-19715242205/2199023255552)), (1/2199023255552), by norm_num⟩
  | 26 => ⟨((-48048386989/1099511627776), (10219157901/1099511627776)), (1/2199023255552), by norm_num⟩
  | 25 => ⟨((99927555823/2199023255552), (-21216462873/2199023255552)), (1/2199023255552), by norm_num⟩
  | 24 => ⟨((-104076433503/2199023255552), (1378514161/137438953472)), (1/2199023255552), by norm_num⟩
  | 23 => ⟨((54292371985/1099511627776), (-11482614835/1099511627776)), (1/2199023255552), by norm_num⟩
  | 22 => ⟨((-1773457985/34359738368), (5988101709/549755813888)), (1/1099511627776), by norm_num⟩
  | 21 => ⟨((59442110435/1099511627776), (-391067183/34359738368)), (1/1099511627776), by norm_num⟩
  | 20 => ⟨((-1950048873/34359738368), (13102717673/1099511627776)), (1/1099511627776), by norm_num⟩
  | 19 => ⟨((32835571419/549755813888), (-13749408461/1099511627776)), (1/1099511627776), by norm_num⟩
  | 18 => ⟨((-69302291915/1099511627776), (1807910481/137438953472)), (1/1099511627776), by norm_num⟩
  | 17 => ⟨((73358501217/1099511627776), (-3813848377/274877906944)), (1/1099511627776), by norm_num⟩
  | 16 => ⟨((-19479762751/274877906944), (16139352359/1099511627776)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((83084246715/1099511627776), (-17132131401/1099511627776)), (1/549755813888), by norm_num⟩
  | 14 => ⟨((-88982884915/1099511627776), (2281895073/137438953472)), (1/549755813888), by norm_num⟩
  | 13 => ⟨((47891572261/549755813888), (-4883974395/274877906944)), (1/549755813888), by norm_num⟩
  | 12 => ⟨((-51854444537/549755813888), (2626263715/137438953472)), (1/549755813888), by norm_num⟩
  | 11 => ⟨((113064800747/1099511627776), (-11362639389/549755813888)), (1/549755813888), by norm_num⟩
  | 10 => ⟨((-15534560595/137438953472), (1546614481/68719476736)), (1/549755813888), by norm_num⟩
  | 9 => ⟨((68978549817/549755813888), (-13580726855/549755813888)), (1/549755813888), by norm_num⟩
  | 8 => ⟨((-77511766787/549755813888), (15050419013/549755813888)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((44227808339/274877906944), (-1054860547/34359738368)), (1/549755813888), by norm_num⟩
  | 6 => ⟨((-103000832575/549755813888), (2401488255/68719476736)), (1/549755813888), by norm_num⟩
  | 5 => ⟨((61639230587/274877906944), (-2787330163/68719476736)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-19189907649/68719476736), (13287220129/274877906944)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((101749402173/274877906944), (-8224340169/137438953472)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((-2360540491/4294967296), (5403168213/68719476736)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((36955753881/34359738368), (-7907221073/68719476736)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-42624975675/274877906944), (30073180943/137438953472)), (1/137438953472), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (3807/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (3807/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (3807/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((89937301139/34359738368), (1879573809/8589934592)), (1/34359738368), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (3807/1280))) (z:=((-21/128), (3807/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((89937301139/34359738368), (1879573809/8589934592))) (r:=(1/34359738368)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((35486928047/1073741824), (11384101829/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((123073086651/68719476736), (7790467463/68719476736)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((871072846003200/94610161817347201), (-200705800790880/94610161817347201)), 0, by norm_num⟩
  | 3 => ⟨((-30097905747/281474976710656), (29257038639/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((62906704691/36028797018963968), (-12663017523/9007199254740992)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-9044135285/288230376151711744), (22933686901/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((20111036921/36893488147419103232), (-42373331975/36893488147419103232)), (81/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-8749986743/1180591620717411303424), (19676133173/590295810358705651712)), (105/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-380584545/75557863725914323419136), (-36350176565/37778931862957161709568)), (129/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((15418043173/2417851639229258349412352), (16538946593/604462909807314587353088)), (11/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-28517204309/77371252455336267181195264), (-58669731245/77371252455336267181195264)), (247/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((40040126939/2475880078570760549798248448), (24978175509/1237940039285380274899124224)), (327/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-25021390607/39614081257132168796771975168), (-39821844883/79228162514264337593543950336)), (423/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21125631151/1073741824), (16381117527/2147483648)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((88713348283/68719476736), (7790467463/68719476736)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((871072846003200/94610161817347201), (-200705800790880/94610161817347201)), 0, by norm_num⟩
  | 3 => ⟨((-30097905747/281474976710656), (29257038639/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((62906704691/36028797018963968), (-12663017523/9007199254740992)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-9044135285/288230376151711744), (22933686901/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((20111036921/36893488147419103232), (-42373331975/36893488147419103232)), (81/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-8749986743/1180591620717411303424), (19676133173/590295810358705651712)), (105/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-380584545/75557863725914323419136), (-36350176565/37778931862957161709568)), (129/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((15418043173/2417851639229258349412352), (16538946593/604462909807314587353088)), (11/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-28517204309/77371252455336267181195264), (-58669731245/77371252455336267181195264)), (247/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((40040126939/2475880078570760549798248448), (24978175509/1237940039285380274899124224)), (327/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-25021390607/39614081257132168796771975168), (-39821844883/79228162514264337593543950336)), (423/79228162514264337593543950336), by norm_num⟩
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
  | 0 => ⟨((126297950309/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((126297950309/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((88449335551/4294967296), (16381117527/2147483648)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((88713348283/68719476736), (7790467463/68719476736)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((871072846003200/94610161817347201), (-200705800790880/94610161817347201)), 0, by norm_num⟩
  | 3 => ⟨((-30097905747/281474976710656), (29257038639/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((62906704691/36028797018963968), (-12663017523/9007199254740992)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-9044135285/288230376151711744), (22933686901/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((20111036921/36893488147419103232), (-42373331975/36893488147419103232)), (81/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-8749986743/1180591620717411303424), (19676133173/590295810358705651712)), (105/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-380584545/75557863725914323419136), (-36350176565/37778931862957161709568)), (129/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((15418043173/2417851639229258349412352), (16538946593/604462909807314587353088)), (11/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-28517204309/77371252455336267181195264), (-58669731245/77371252455336267181195264)), (247/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((40040126939/2475880078570760549798248448), (24978175509/1237940039285380274899124224)), (327/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-25021390607/39614081257132168796771975168), (-39821844883/79228162514264337593543950336)), (423/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((456460125798400/94610161817347201), (-213568192512000/94610161817347201)), 0, by norm_num⟩
  | 1 => ⟨((-43341791989/140737488355328), (33390778021/140737488355328)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((61411784497/4503599627370496), (-18393098195/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-17117947041/36028797018963968), (16571910799/18014398509481984)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((13889200563/1152921504606846976), (-822647141/18014398509481984)), (7/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-1491988613/18446744073709551616), (19060631923/9223372036854775808)), (7/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-9289318509/590295810358705651712), (-51137828773/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 7 => ⟨((26915738245/18889465931478580854784), (15982026781/4722366482869645213696)), (11/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-52746321257/604462909807314587353088), (-74304809761/604462909807314587353088)), (9/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((43866698555/9671406556917033397649408), (39627517049/9671406556917033397649408)), (15/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-66053037131/309485009821345068724781056), (-37457055591/309485009821345068724781056)), (23/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((92496154301/9903520314283042199192993792), (14156713383/4951760157141521099596496896)), (35/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-60998593605/158456325028528675187087900672), (-4782046441/158456325028528675187087900672)), (53/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((43341791989/140737488355328), (-33390778021/140737488355328)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-61411784497/2251799813685248), (18393098195/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((12838460281/9007199254740992), (-49715732397/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 3 => ⟨((-13889200563/288230376151711744), (822647141/4503599627370496)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((3729971533/9223372036854775808), (-95303159615/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 5 => ⟨((3483494441/36893488147419103232), (76706743159/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-5887817741/590295810358705651712), (-55937093733/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 7 => ⟨((52746321257/75557863725914323419136), (2322025305/2361183241434822606848)), (15/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-24675017937/604462909807314587353088), (-5572619585/151115727451828646838272)), (7/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((41283148207/19342813113834066795298816), (46821319489/38685626227668133590597632)), (3/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-31795553041/309485009821345068724781056), (-19465480901/618970019642690137449562112)), (5/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((91497890407/19807040628566084398385987584), (7173069661/19807040628566084398385987584)), (1/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-15475280857/79228162514264337593543950336), (1094942353/39614081257132168796771975168)), (13/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((40941189665/2251799813685248), (-49048261853/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-17117947041/9007199254740992), (66287643197/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 2 => ⟨((27778401127/288230376151711744), (-105298834049/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 3 => ⟨((-4973295377/4611686018427387904), (63535439743/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-1451456017/4611686018427387904), (-31961142983/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 5 => ⟨((5887817741/147573952589676412928), (55937093733/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-3846085925/1180591620717411303424), (-5418059045/1180591620717411303424)), (1/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((8225005979/37778931862957161709568), (59441275573/302231454903657293676544)), (1/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-30962361155/2417851639229258349412352), (-2194749351/302231454903657293676544)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((52992588401/77371252455336267181195264), (4055308521/19342813113834066795298816)), (15/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-41936533103/1237940039285380274899124224), (-102739279/38685626227668133590597632)), (13/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((15475280857/9903520314283042199192993792), (-1094942353/4951760157141521099596496896)), (23/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-85425509139/1267650600228229401496703205376), (32094574019/1267650600228229401496703205376)), (39/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17117947041/18014398509481984), (-16571910799/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-13889200563/144115188075855872), (105298834049/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((3729971533/2305843009213693952), (-1489111869/36028797018963968)), (1/288230376151711744), by norm_num⟩
  | 3 => ⟨((1451456017/2305843009213693952), (31961142983/9223372036854775808)), (7/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-29439088705/295147905179352825856), (-34960683583/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 5 => ⟨((11538257775/1180591620717411303424), (16254177135/1180591620717411303424)), (13/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-57575041853/75557863725914323419136), (-26005558063/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((30962361155/604462909807314587353088), (2194749351/75557863725914323419136)), (15/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-59616661951/19342813113834066795298816), (-2281111043/2417851639229258349412352)), (1/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((104841332757/618970019642690137449562112), (8219142319/618970019642690137449562112)), (31/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-85114044713/9903520314283042199192993792), (3011091471/2475880078570760549798248448)), (15/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((32034565927/79228162514264337593543950336), (-12035465257/79228162514264337593543950336)), (27/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-22310191807/1267650600228229401496703205376), (29119055979/2535301200456458802993406410752)), (25/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22222720901/576460752303423488), (-84239067239/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 1 => ⟨((-1491988613/1152921504606846976), (19060631923/576460752303423488)), (3/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-3483494441/4611686018427387904), (-9588342895/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((5887817741/36893488147419103232), (55937093733/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-11538257775/590295810358705651712), (-16254177135/590295810358705651712)), (13/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((4318128139/2361183241434822606848), (7801667419/4722366482869645213696)), (9/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-43347305617/302231454903657293676544), (-49162385463/604462909807314587353088)), (11/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((47693329561/4835703278458516698824704), (29198221351/9671406556917033397649408)), (25/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-94357199481/154742504910672534362390528), (-7397228087/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((85114044713/2475880078570760549798248448), (-3011091471/618970019642690137449562112)), (29/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-70476045039/39614081257132168796771975168), (13239011783/19807040628566084398385987584)), (15/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((3346528771/39614081257132168796771975168), (-34942867175/633825300114114700748351602688)), (29/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-36959229495/10141204801825835211973625643008), (18913794193/5070602400912917605986812821504)), (27/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1989318151/4611686018427387904), (-50828351795/4611686018427387904)), (11/9223372036854775808), by norm_num⟩
  | 1 => ⟨((18578637019/36893488147419103232), (51137828773/18446744073709551616)), (11/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-23551270965/147573952589676412928), (-55937093733/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 3 => ⟨((3846085925/147573952589676412928), (5418059045/147573952589676412928)), (9/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-57575041853/18889465931478580854784), (-26005558063/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((43347305617/151115727451828646838272), (49162385463/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-55642217821/2417851639229258349412352), (-4258073947/604462909807314587353088)), (1/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((125809599309/77371252455336267181195264), (9862970783/77371252455336267181195264)), (19/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-63835533535/618970019642690137449562112), (9033274413/618970019642690137449562112)), (23/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((58730037533/9903520314283042199192993792), (-11032509819/4951760157141521099596496896)), (25/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-49082421975/158456325028528675187087900672), (16015480789/79228162514264337593543950336)), (27/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((36959229495/2535301200456458802993406410752), (-37827588387/2535301200456458802993406410752)), (27/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-48811643645/81129638414606681695789005144064), (19682964991/20282409603651670423947251286016)), (53/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5308182005/36893488147419103232), (-14610808221/18446744073709551616)), (9/73786976294838206464), by norm_num⟩
  | 1 => ⟨((26915738245/295147905179352825856), (63928107123/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-26373160629/1180591620717411303424), (-2322025305/73786976294838206464)), (15/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((65800047833/18889465931478580854784), (59441275573/18889465931478580854784)), (9/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-30962361155/75557863725914323419136), (-2194749351/9444732965739290427392)), (17/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((47693329561/1208925819614629174706176), (29198221351/2417851639229258349412352)), (7/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-31452399827/9671406556917033397649408), (-9862970783/38685626227668133590597632)), (41/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((18238723867/77371252455336267181195264), (-5161871093/154742504910672534362390528)), (27/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-75510048257/4951760157141521099596496896), (28369310963/4951760157141521099596496896)), (17/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((70117745679/79228162514264337593543950336), (-45758516539/79228162514264337593543950336)), (5/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((-58078789207/1267650600228229401496703205376), (59443353179/1267650600228229401496703205376)), (11/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((2614909481/1267650600228229401496703205376), (-67484451399/20282409603651670423947251286016)), (47/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-1513349239/20282409603651670423947251286016), (69294920221/324518553658426726783156020576256)), (3/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-26915738245/1180591620717411303424), (-15982026781/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 1 => ⟨((52746321257/4722366482869645213696), (2322025305/147573952589676412928)), (17/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-49350035875/18889465931478580854784), (-44580956679/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((61924722311/151115727451828646838272), (2194749351/9444732965739290427392)), (9/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-931510343/18889465931478580854784), (-2281111043/151115727451828646838272)), (19/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((94357199481/19342813113834066795298816), (7397228087/19342813113834066795298816)), (1/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-31917766767/77371252455336267181195264), (9033274413/154742504910672534362390528)), (25/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((147480563/4835703278458516698824704), (-28369310963/2475880078570760549798248448)), (35/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-78882463889/39614081257132168796771975168), (51478331107/39614081257132168796771975168)), (47/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((18149621627/158456325028528675187087900672), (-37152095737/316912650057057350374175801344)), (15/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-28764004291/5070602400912917605986812821504), (2899722521/316912650057057350374175801344)), (17/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((4540047717/20282409603651670423947251286016), (-25985595083/40564819207303340847894502572032)), (19/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-784067177/162259276829213363391578010288128), (106408239343/2596148429267413814265248164610048)), (41/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-46885618895/18889465931478580854784), (-16512179947/4722366482869645213696)), (21/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((43866698555/37778931862957161709568), (39627517049/37778931862957161709568)), (7/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((-41283148207/151115727451828646838272), (-46821319487/302231454903657293676544)), (25/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((26496294201/604462909807314587353088), (4055308521/302231454903657293676544)), (9/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((-52420666379/9671406556917033397649408), (-4109571159/9671406556917033397649408)), (19/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((85114044713/154742504910672534362390528), (-3011091471/38685626227668133590597632)), (35/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((-14682509383/309485009821345068724781056), (11032509819/618970019642690137449562112)), (15/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((35058872839/9903520314283042199192993792), (-45758516539/19807040628566084398385987584)), (43/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((-18149621627/79228162514264337593543950336), (37152095737/158456325028528675187087900672)), (31/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((998750149/79228162514264337593543950336), (-12887655649/633825300114114700748351602688)), (41/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-22195788839/40564819207303340847894502572032), (3970021471/2535301200456458802993406410752)), (25/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((8363383221/649037107316853453566312041152512), (-17734706557/162259276829213363391578010288128)), (29/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((462011235/649037107316853453566312041152512), (72609914583/10384593717069655257060992658440192)), (33/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8773339711/37778931862957161709568), (-63404027279/302231454903657293676544)), (15/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((66053037131/604462909807314587353088), (37457055591/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-31795553041/1208925819614629174706176), (-4866370225/604462909807314587353088)), (11/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((83873066207/19342813113834066795298816), (6575313855/19342813113834066795298816)), (33/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((-42557022357/77371252455336267181195264), (12044365885/154742504910672534362390528)), (19/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((4404752815/77371252455336267181195264), (-13239011783/618970019642690137449562112)), (37/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-49082421975/9903520314283042199192993792), (16015480789/4951760157141521099596496896)), (17/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((29039394603/79228162514264337593543950336), (-59443353179/158456325028528675187087900672)), (13/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((-28764004291/1267650600228229401496703205376), (2899722521/79228162514264337593543950336)), (39/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((22195788839/20282409603651670423947251286016), (-3970021471/1267650600228229401496703205376)), (27/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((-9199721543/324518553658426726783156020576256), (78032708851/324518553658426726783156020576256)), (69/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-277206741/162259276829213363391578010288128), (-21782974375/1298074214633706907132624082305024)), (85/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((14757313685/41538374868278621028243970633760768), (88983292601/83076749736557242056487941267521536)), (25/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/922762947), (-406080/307587649)), 0, by norm_num⟩
  | 1 => ⟨((-57057515724800/283830485452041603), (8898674688000/94610161817347201)), 0, by norm_num⟩
  | 2 => ⟨((57789055985/9007199254740992), (-44521037361/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-54588252887/288230376151711744), (65397682471/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((5705982347/1152921504606846976), (-88383524261/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-14815147267/147573952589676412928), (56159378159/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 6 => ⟨((2652424201/4722366482869645213696), (-67771135727/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 7 => ⟨((14155152013/151115727451828646838272), (4870269407/9444732965739290427392)), (13/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-35887650993/4835703278458516698824704), (-85237476165/4835703278458516698824704)), (5/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((31257079263/77371252455336267181195264), (44032479859/77371252455336267181195264)), (15/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-46791145125/2475880078570760549798248448), (-42269351519/2475880078570760549798248448)), (21/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((64051429945/79228162514264337593543950336), (36321993301/79228162514264337593543950336)), (15/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-5138675239/158456325028528675187087900672), (-25167490459/2535301200456458802993406410752)), (43/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((88474834569/4294967296), (32756564799/4294967296)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((88699533831/68719476736), (3898465479/34359738368)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((40520896087/4398046511104), (-18703491045/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-60302429175/562949953421312), (3673096061/70368744177664)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((63085016639/36028797018963968), (-25498659117/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-18146142239/576460752303423488), (1447066217/36028797018963968)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((20131758985/36893488147419103232), (-42902793973/36893488147419103232)), (41/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-4319699809/590295810358705651712), (19980525011/590295810358705651712)), (53/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-235332273/18889465931478580854784), (-74032188695/75557863725914323419136)), (65/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((4098706725/604462909807314587353088), (8441475171/302231454903657293676544)), (177/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-14989713797/38685626227668133590597632), (-1874707765/2417851639229258349412352)), (31/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((42041734125/2475880078570760549798248448), (51091413309/2475880078570760549798248448)), (329/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-26306059417/39614081257132168796771975168), (-158626285/309485009821345068724781056)), (425/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-30820829859/36028797018963968), (47489106519/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 1 => ⟨((43670602309/576460752303423488), (-52318145977/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-18259143511/4611686018427387904), (70706819409/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((9876764845/73786976294838206464), (-74879170879/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-2652424201/2361183241434822606848), (33885567863/1180591620717411303424)), (3/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-4954303205/18889465931478580854784), (-109094034715/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((33495140927/1208925819614629174706176), (39777488877/604462909807314587353088)), (13/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-9377123779/4835703278458516698824704), (-52838975829/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((70186717687/618970019642690137449562112), (31702013639/309485009821345068724781056)), (21/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-58713810783/9903520314283042199192993792), (-16647580263/4951760157141521099596496896)), (9/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((45220342103/158456325028528675187087900672), (1730264969/19807040628566084398385987584)), (15/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-4066572907/316912650057057350374175801344), (-5100849537/5070602400912917605986812821504)), (3/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((11004644165/20282409603651670423947251286016), (-3114502693/40564819207303340847894502572032)), (19/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((88474830895/4294967296), (16378283815/2147483648)), (1/536870912), by norm_num⟩
  | 1 => ⟨((88699539037/68719476736), (7796924721/68719476736)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((81041757347/8796093022208), (-9351711807/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-60302353821/562949953421312), (29384482847/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((31542488083/18014398509481984), (-50996284129/36028797018963968)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-36292586865/1152921504606846976), (46304454301/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 6 => ⟨((40265562351/73786976294838206464), (-10725091537/9223372036854775808)), (83/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-8641688955/1180591620717411303424), (39957824987/1180591620717411303424)), (107/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-932761377/75557863725914323419136), (-37012224473/37778931862957161709568)), (131/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((8190246237/1208925819614629174706176), (67523672667/2417851639229258349412352)), (89/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-29957347349/77371252455336267181195264), (-1874496551/2417851639229258349412352)), (249/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((5251245503/309485009821345068724781056), (12772230665/618970019642690137449562112)), (165/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-52569131943/79228162514264337593543950336), (-40614411973/79228162514264337593543950336)), (213/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13911728389/18446744073709551616), (-53871862407/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-11287731251/147573952589676412928), (85576195291/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 2 => ⟨((378917743/295147905179352825856), (-77452726545/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((9436768009/18889465931478580854784), (103899080681/37778931862957161709568)), (3/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-11962550331/151115727451828646838272), (-28412492055/151115727451828646838272)), (9/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((9377123779/1208925819614629174706176), (52838975829/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-46791145125/77371252455336267181195264), (-21134675759/38685626227668133590597632)), (3/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((6290765441/154742504910672534362390528), (28538709021/1237940039285380274899124224)), (13/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-24225183269/9903520314283042199192993792), (-29661685181/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((85204384717/633825300114114700748351602688), (1669920979/158456325028528675187087900672)), (13/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-69172049037/10141204801825835211973625643008), (2447109259/2535301200456458802993406410752)), (25/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((52068881761/162259276829213363391578010288128), (-19562407021/162259276829213363391578010288128)), (23/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-36262914937/2596148429267413814265248164610048), (47330021147/5192296858534827628530496329220096)), (41/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44237415449/2147483648), (4094570953/536870912)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((11087442379/8589934592), (7796924741/68719476736)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((40520878679/4398046511104), (-18703423903/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-15075588385/140737488355328), (29384484395/562949953421312)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((31542486657/18014398509481984), (-50996290903/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-18146288961/576460752303423488), (46304466899/1152921504606846976)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((40265517727/73786976294838206464), (-85800772607/73786976294838206464)), (21/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-17283281921/2361183241434822606848), (79915704407/2361183241434822606848)), (27/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-116618275/9444732965739290427392), (-74024505521/75557863725914323419136)), (33/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((16380817503/2417851639229258349412352), (16880924537/604462909807314587353088)), (179/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-14978937545/38685626227668133590597632), (-7497976869/9671406556917033397649408)), (125/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((10502689633/618970019642690137449562112), (51088624161/2475880078570760549798248448)), (331/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-52570238599/79228162514264337593543950336), (-20306844887/39614081257132168796771975168)), (427/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4850147111/18889465931478580854784), (15490545309/2361183241434822606848)), (7/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-2831030403/9444732965739290427392), (-62339448409/37778931862957161709568)), (1/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((28710120795/302231454903657293676544), (17047495233/75557863725914323419136)), (11/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-9377123779/604462909807314587353088), (-52838975829/2417851639229258349412352)), (3/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((70186717687/38685626227668133590597632), (63404027277/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-52842429705/309485009821345068724781056), (-29965644473/309485009821345068724781056)), (15/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((67830513153/4951760157141521099596496896), (20763179627/4951760157141521099596496896)), (5/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-76683946245/79228162514264337593543950336), (-6011715525/79228162514264337593543950336)), (3/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((38909277583/633825300114114700748351602688), (-11011991665/1267650600228229401496703205376)), (29/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((-71594712421/20282409603651670423947251286016), (13449154827/10141204801825835211973625643008)), (31/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((29916904823/162259276829213363391578010288128), (-39047267447/324518553658426726783156020576256)), (17/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((-22527530359/2596148429267413814265248164610048), (46113631557/5192296858534827628530496329220096)), (17/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((3718982373/10384593717069655257060992658440192), (-2999308951/5192296858534827628530496329220096)), (33/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44237415449/2147483648), (4094570953/536870912)), (5/2147483648), by norm_num⟩
  | 1 => ⟨((11087442379/8589934592), (7796924741/68719476736)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((81041757359/8796093022208), (-18703423901/8796093022208)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-60302353549/562949953421312), (29384484383/562949953421312)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((63084973379/36028797018963968), (-12749072711/9007199254740992)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-36292578119/1152921504606846976), (46304466787/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((20132759369/36893488147419103232), (-42900386149/36893488147419103232)), (85/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-8641642103/1180591620717411303424), (19978926057/590295810358705651712)), (109/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-466470781/37778931862957161709568), (-74024506177/75557863725914323419136)), (133/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((2047601121/302231454903657293676544), (67523701355/2417851639229258349412352)), (45/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-29957860825/77371252455336267181195264), (-29991912131/38685626227668133590597632)), (251/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((5251342131/309485009821345068724781056), (25544323075/1237940039285380274899124224)), (83/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-52570210225/79228162514264337593543950336), (-10153433885/19807040628566084398385987584)), (107/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5800024403/302231454903657293676544), (-55103014895/1208925819614629174706176)), (13/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((45464842565/4835703278458516698824704), (64047243429/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 2 => ⟨((-10634351165/4835703278458516698824704), (-19213341599/9671406556917033397649408)), (13/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((26688095811/77371252455336267181195264), (15134163875/77371252455336267181195264)), (17/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((-102773504779/2475880078570760549798248448), (-31459363071/2475880078570760549798248448)), (17/1237940039285380274899124224), by norm_num⟩
  | 5 => ⟨((81331458139/19807040628566084398385987584), (199251935/618970019642690137449562112)), (29/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((-6877902603/19807040628566084398385987584), (7786256733/158456325028528675187087900672)), (11/79228162514264337593543950336), by norm_num⟩
  | 7 => ⟨((8135762775/316912650057057350374175801344), (-3056626097/316912650057057350374175801344)), (31/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((-67992965507/40564819207303340847894502572032), (22185947413/20282409603651670423947251286016)), (41/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((62576473219/649037107316853453566312041152512), (-2001459703/20282409603651670423947251286016)), (13/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((-6198303955/1298074214633706907132624082305024), (79981572027/10384593717069655257060992658440192)), (59/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((31306456985/166153499473114484112975882535043072), (-89593432205/166153499473114484112975882535043072)), (67/166153499473114484112975882535043072), by norm_num⟩
  | 12 => ⟨((-10813263155/2658455991569831745807614120560689152), (91718886437/2658455991569831745807614120560689152)), (71/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44237415449/2147483648), (4094570953/536870912)), (11/4294967296), by norm_num⟩
  | 1 => ⟨((11087442379/8589934592), (7796924741/68719476736)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((81041757359/8796093022208), (-18703423901/8796093022208)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-60302353549/562949953421312), (29384484383/562949953421312)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((31542486689/18014398509481984), (-12749072711/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-18146289057/576460752303423488), (46304466787/1152921504606846976)), (15/576460752303423488), by norm_num⟩
  | 6 => ⟨((5033189839/9223372036854775808), (-42900386147/36893488147419103232)), (43/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-17283284145/2361183241434822606848), (79915704205/2361183241434822606848)), (55/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-932941689/75557863725914323419136), (-37012253047/37778931862957161709568)), (67/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((16380809201/2417851639229258349412352), (16880925279/604462909807314587353088)), (181/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-14978930597/38685626227668133590597632), (-29991911833/38685626227668133590597632)), (63/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((42010737515/2475880078570760549798248448), (51088644815/2475880078570760549798248448)), (333/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-52570210547/79228162514264337593543950336), (-40613732807/79228162514264337593543950336)), (429/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((68907479255/154742504910672534362390528), (62248411641/154742504910672534362390528)), (31/154742504910672534362390528), by norm_num⟩
  | 1 => ⟨((-32424570031/154742504910672534362390528), (-18387177561/154742504910672534362390528)), (3/38685626227668133590597632), by norm_num⟩
  | 2 => ⟨((62432080705/1237940039285380274899124224), (19110698797/1237940039285380274899124224)), (23/1237940039285380274899124224), by norm_num⟩
  | 3 => ⟨((-82344377399/9903520314283042199192993792), (-3227735375/4951760157141521099596496896)), (33/9903520314283042199192993792), by norm_num⟩
  | 4 => ⟨((83562737561/79228162514264337593543950336), (-2956210661/19807040628566084398385987584)), (19/39614081257132168796771975168), by norm_num⟩
  | 5 => ⟨((-69191533263/633825300114114700748351602688), (12997714665/316912650057057350374175801344)), (37/633825300114114700748351602688), by norm_num⟩
  | 6 => ⟨((48187835041/5070602400912917605986812821504), (-15723579141/2535301200456458802993406410752)), (17/2535301200456458802993406410752), by norm_num⟩
  | 7 => ⟨((-7127529065/10141204801825835211973625643008), (14589981413/20282409603651670423947251286016)), (13/20282409603651670423947251286016), by norm_num⟩
  | 8 => ⟨((3529968159/81129638414606681695789005144064), (-45549944729/649037107316853453566312041152512)), (39/649037107316853453566312041152512), by norm_num⟩
  | 9 => ⟨((-5447810887/2596148429267413814265248164610048), (62362607893/10384593717069655257060992658440192)), (27/5192296858534827628530496329220096), by norm_num⟩
  | 10 => ⟨((9032045411/166153499473114484112975882535043072), (-76610467671/166153499473114484112975882535043072)), (69/166153499473114484112975882535043072), by norm_num⟩
  | 11 => ⟨((4354468967/1329227995784915872903807060280344576), (42771906261/1329227995784915872903807060280344576)), (21/664613997892457936451903530140172288), by norm_num⟩
  | 12 => ⟨((-28976687331/42535295865117307932921825928971026432), (-21840365923/10633823966279326983230456482242756608)), (99/42535295865117307932921825928971026432), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44237415449/2147483648), (4094570953/536870912)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((11087442379/8589934592), (7796924741/68719476736)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((81041757359/8796093022208), (-18703423901/8796093022208)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-60302353549/562949953421312), (29384484383/562949953421312)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((31542486689/18014398509481984), (-12749072711/9007199254740992)), (23/36028797018963968), by norm_num⟩
  | 5 => ⟨((-18146289057/576460752303423488), (46304466787/1152921504606846976)), (31/1152921504606846976), by norm_num⟩
  | 6 => ⟨((40265518713/73786976294838206464), (-42900386147/36893488147419103232)), (87/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-17283284147/2361183241434822606848), (79915704207/2361183241434822606848)), (111/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-466470843/37778931862957161709568), (-74024506099/75557863725914323419136)), (135/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((4095202299/604462909807314587353088), (67523701131/2417851639229258349412352)), (91/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-14978930595/38685626227668133590597632), (-29991911851/38685626227668133590597632)), (253/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((42010737523/2475880078570760549798248448), (51088644895/2475880078570760549798248448)), (167/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-52570210601/79228162514264337593543950336), (-20306866485/39614081257132168796771975168)), (215/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((208772074183527/1048576), (451412138589051/524288)), (12527283/2097152), by norm_num⟩
  | 1 => ⟨((5097581823/32), (72571173393/64)), (273/32), by norm_num⟩
  | 2 => ⟨((2697295365/64), (95789053999/128)), (393/64), by norm_num⟩
  | 3 => ⟨((-1958442443/256), (42269327575/128)), (381/128), by norm_num⟩
  | 4 => ⟨((-5581528347/512), (14036818425/128)), (559/512), by norm_num⟩
  | 5 => ⟨((-5196461479/1024), (29941887779/1024)), (83/256), by norm_num⟩
  | 6 => ⟨((-26343277673/16384), (106852327537/16384)), (83/1024), by norm_num⟩
  | 7 => ⟨((-13090684479/32768), (20506190017/16384)), (575/32768), by norm_num⟩
  | 8 => ⟨((-21692801105/262144), (55304890097/262144)), (881/262144), by norm_num⟩
  | 9 => ⟨((-15516559427/1048576), (2079321849/65536)), (303/524288), by norm_num⟩
  | 10 => ⟨((-19607559281/8388608), (18076637059/4194304)), (379/4194304), by norm_num⟩
  | 11 => ⟨((-22248323121/67108864), (71675824373/134217728)), (871/67108864), by norm_num⟩
  | 12 => ⟨((-45902638813/1073741824), (65339018483/1073741824)), (927/536870912), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((805404556785357/5070602400912917605986812821504), (437530129495/2535301200456458802993406410752)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((453593710749959/158456325028528675187087900672), (268585241273/79228162514264337593543950336)), (4479/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((964921358460467/19807040628566084398385987584), (1211894889021/19807040628566084398385987584)), (5053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((483041301393155/618970019642690137449562112), (645206157789/618970019642690137449562112)), (5381/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1813877593551389/154742504910672534362390528), (2587030917217/154742504910672534362390528)), (5395/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((794810761592353/4835703278458516698824704), (2431955557631/9671406556917033397649408)), (5073/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((323474377624365/151115727451828646838272), (2134598953711/604462909807314587353088)), (2227/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1944936467759753/75557863725914323419136), (3481220025033/75557863725914323419136)), (227/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1340479029339139/4722366482869645213696), (1310950335531/2361183241434822606848)), (5473/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((840311276236723/295147905179352825856), (3623061284823/590295810358705651712)), (7565/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1897642282100911/73786976294838206464), (1138979438319/18446744073709551616)), (2379/18446744073709551616), by norm_num⟩
  | 7 => ⟨((238296417472725/1152921504606846976), (5162934971141/9223372036854775808)), (10789/9223372036854775808), by norm_num⟩
  | 6 => ⟨((838983341177611/576460752303423488), (5210263577071/1152921504606846976)), (10895/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1268457027965235/144115188075855872), (576600931845/18014398509481984)), (9653/144115188075855872), by norm_num⟩
  | 4 => ⟨((200405636624995/4503599627370496), (7028337462911/36028797018963968)), (7361/18014398509481984), by norm_num⟩
  | 3 => ⟨((1630171937514915/9007199254740992), (2244938581577/2251799813685248)), (18837/9007199254740992), by norm_num⟩
  | 2 => ⟨((628514229988125/1125899906842624), (9278098077625/2251799813685248)), (19505/2251799813685248), by norm_num⟩
  | 1 => ⟨((332025529533137/281474976710656), (14687522890643/1125899906842624)), (30985/1125899906842624), by norm_num⟩
  | 0 => ⟨((388266804204159/281474976710656), (32608219180149/1125899906842624)), (69245/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((388266804204159/281474976710656), (32608219180149/1125899906842624)), (264148716453170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((535339435890341/281474976710656), (89959606355203/1125899906842624)), (195045/1125899906842624), by norm_num⟩
  | 2 => ⟨((1016369267666713/281474976710656), (85547435658227/281474976710656)), (386543/562949953421312), by norm_num⟩
  | 3 => ⟨((455497028766093/35184372088832), (154450291721839/70368744177664)), (189155/35184372088832), by norm_num⟩
  | 4 => ⟨((715920904999829/4398046511104), (499878531253401/8796093022208)), (1431987/8796093022208), by norm_num⟩
  | 5 => ⟨((799490439564749/34359738368), (39731938903933/2147483648)), (2456879/34359738368), by norm_num⟩
  | 6 => ⟨((208772074183527/1048576), (451412138589051/524288)), (12527283/2097152), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((44237415449/2147483648), (4094570953/536870912)), (3/1073741824), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/17590849), (-4872960/17590849)), 0, by norm_num⟩
  | 1 => ⟨((9335315660800/309437968540801), (10977804288000/309437968540801)), 0, by norm_num⟩
  | 2 => ⟨((-7526818011/1099511627776), (8386737539/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1532468723/8796093022208), (-75314238537/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((38586484087/281474976710656), (52165574699/562949953421312)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-24334017169/1125899906842624), (29395076987/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 6 => ⟨((-3820359847/9007199254740992), (-34492776789/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 7 => ⟨((80354701809/144115188075855872), (13436274015/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 8 => ⟨((-17734898633/288230376151711744), (37636247293/576460752303423488)), (1/36028797018963968), by norm_num⟩
  | 9 => ⟨((-23533501613/4611686018427387904), (-58582696307/4611686018427387904)), (27/4611686018427387904), by norm_num⟩
  | 10 => ⟨((38484487955/18446744073709551616), (1966623239/18446744073709551616)), (45/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-43786917093/295147905179352825856), (41635957785/147573952589676412928)), (37/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-34920150457/1180591620717411303424), (-45588119927/1180591620717411303424)), (61/1180591620717411303424), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (3807/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (3807/1280)))⁻¹=value ((2252800/17590849), (-4872960/17590849)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/17590849), (-4872960/17590849))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/23734849), (-4872960/23734849)), 0, by norm_num⟩
  | 1 => ⟨((4302150860800/563343057052801), (18961661952000/563343057052801)), 0, by norm_num⟩
  | 2 => ⟨((-17949574255/4398046511104), (-17373765035/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((75619584939/140737488355328), (-36176449311/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-4970098545/281474976710656), (85825026683/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-28722603813/4503599627370496), (-9076078585/1125899906842624)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((97299921331/72057594037927936), (439269189/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 7 => ⟨((-32083961863/288230376151711744), (39808918977/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((-11652428447/2305843009213693952), (-26227116787/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 9 => ⟨((50718555085/18446744073709551616), (6207248083/4611686018427387904)), (11/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-13412629169/36893488147419103232), (1585589561/9223372036854775808)), (33/147573952589676412928), by norm_num⟩
  | 11 => ⟨((14348632827/1180591620717411303424), (-60696296713/1180591620717411303424)), (25/590295810358705651712), by norm_num⟩
  | 12 => ⟨((20218137977/4722366482869645213696), (12896721761/2361183241434822606848)), (75/9444732965739290427392), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (3807/1280)))⁻¹=value ((3891200/23734849), (-4872960/23734849)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/23734849), (-4872960/23734849))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-14979643801600/417516144796801), (-29939466240000/417516144796801)), 0, by norm_num⟩
  | 1 => ⟨((99095882215/4398046511104), (3996542625/2199023255552)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-48630791155/17592186044416), (34147240113/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-12775021343/35184372088832), (-28613006941/35184372088832)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((5444572829/35184372088832), (9253061357/562949953421312)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-2144170777/140737488355328), (47547234157/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 6 => ⟨((-31965700027/18014398509481984), (-17273842719/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 7 => ⟨((96396682741/144115188075855872), (3484044271/72057594037927936)), (21/144115188075855872), by norm_num⟩
  | 8 => ⟨((-32556690155/576460752303423488), (25374902843/288230376151711744)), (19/576460752303423488), by norm_num⟩
  | 9 => ⟨((-1131660637/144115188075855872), (-32394972195/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 10 => ⟨((90381605079/36893488147419103232), (-2409111765/36893488147419103232)), (27/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-11843518825/73786976294838206464), (24611497437/73786976294838206464)), (45/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-39974684951/1180591620717411303424), (-52036480807/1180591620717411303424)), (37/590295810358705651712), by norm_num⟩
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
  | 0 => ⟨((27/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((204800/1227987), (-60160/409329)), 0, by norm_num⟩
  | 1 => ⟨((-4685004800/1507952072169), (12320768000/502650690723)), 0, by norm_num⟩
  | 2 => ⟨((-2855733821440000/1851745541246593803), (-467523862528000/205749504582954867)), 0, by norm_num⟩
  | 3 => ⟨((41599571275/140737488355328), (21435508471/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-17026128911/562949953421312), (34612057335/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((12542511763/9007199254740992), (-15781968641/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((20377759645/144115188075855872), (56860321019/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((-47021722259/1152921504606846976), (-6488029339/288230376151711744)), (9/1152921504606846976), by norm_num⟩
  | 8 => ⟨((93251064443/18446744073709551616), (-1291335657/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-50061943157/147573952589676412928), (17151159411/36893488147419103232)), (31/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-6935184309/1180591620717411303424), (-75197568999/1180591620717411303424)), (5/147573952589676412928), by norm_num⟩
  | 11 => ⟨((48834337821/9444732965739290427392), (46087784535/9444732965739290427392)), (51/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-59672279067/75557863725914323419136), (-2036363521/75557863725914323419136)), (129/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (3807/1280)))⁻¹=value ((204800/1227987), (-60160/409329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((204800/1227987), (-60160/409329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-36333994377/2199023255552), (-14703248369/2199023255552)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((25922320853/4398046511104), (-16119205661/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-3962895997/35184372088832), (63067348941/35184372088832)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-42560049519/140737488355328), (-33778912109/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((20006808361/281474976710656), (-12503218825/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((-16809802585/4503599627370496), (57808407007/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-13435865101/9007199254740992), (-31048824023/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 7 => ⟨((53280474195/144115188075855872), (-1011274101/18014398509481984)), (13/144115188075855872), by norm_num⟩
  | 8 => ⟨((-1670592955/72057594037927936), (63217696251/1152921504606846976)), (3/144115188075855872), by norm_num⟩
  | 9 => ⟨((-25228607439/4611686018427387904), (-68853297547/9223372036854775808)), (41/9223372036854775808), by norm_num⟩
  | 10 => ⟨((51788754869/36893488147419103232), (-11101394039/73786976294838206464)), (35/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-24717580225/295147905179352825856), (14382538399/73786976294838206464)), (59/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-45961598805/2361183241434822606848), (-14629164967/590295810358705651712)), (97/2361183241434822606848), by norm_num⟩
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
  | 0 => ⟨((35/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/45853249), (-4872960/45853249)), 0, by norm_num⟩
  | 1 => ⟨((-13817242419200/2102520443856001), (34929377280000/2102520443856001)), 0, by norm_num⟩
  | 2 => ⟨((-811654087/2199023255552), (-57973969003/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((32764685087/281474976710656), (61461273275/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-33551072973/2251799813685248), (-2643921855/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((23227278133/18014398509481984), (-43823205755/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((-39467108637/576460752303423488), (66897517151/576460752303423488)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-7517668459/9223372036854775808), (-58608108197/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 8 => ⟨((54528444111/73786976294838206464), (35049753679/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-31947659053/295147905179352825856), (-10326785861/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 10 => ⟨((97466710643/9444732965739290427392), (-28493427319/9444732965739290427392)), (15/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-12208383539/18889465931478580854784), (59249216501/75557863725914323419136)), (1/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((1337303509/151115727451828646838272), (-115614445115/1208925819614629174706176)), (17/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (3807/1280)))⁻¹=value ((7168000/45853249), (-4872960/45853249)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/45853249), (-4872960/45853249))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-57939695897/17592186044416), (12502706961/17592186044416)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((26442840745/35184372088832), (-12577322571/8796093022208)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((6689276665/35184372088832), (31235027201/70368744177664)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-62615255981/562949953421312), (-16874123169/562949953421312)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((5358578413/281474976710656), (-8215160233/562949953421312)), (7/2251799813685248), by norm_num⟩
  | 5 => ⟨((1225793915/18014398509481984), (5129005893/1125899906842624)), (13/18014398509481984), by norm_num⟩
  | 6 => ⟨((-23913551227/36028797018963968), (-33388621667/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | 7 => ⟨((73976641551/576460752303423488), (-27160914041/576460752303423488)), (3/72057594037927936), by norm_num⟩
  | 8 => ⟨((-24552256147/4611686018427387904), (24830755529/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-43844361949/18446744073709551616), (-47074266499/18446744073709551616)), (39/18446744073709551616), by norm_num⟩
  | 10 => ⟨((77450640367/147573952589676412928), (-3672049649/36893488147419103232)), (33/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-33186277701/1180591620717411303424), (44294475217/590295810358705651712)), (111/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-2203805821/295147905179352825856), (-43277168251/4722366482869645213696)), (93/4722366482869645213696), by norm_num⟩
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
  | 0 => ⟨((43/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/61827649), (-4872960/61827649)), 0, by norm_num⟩
  | 1 => ⟨((-26903470899200/3822658180867201), (42913234944000/3822658180867201)), 0, by norm_num⟩
  | 2 => ⟨((4139760789/70368744177664), (-75775441531/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((2691306491/70368744177664), (22238650447/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1643042743/281474976710656), (-4638181723/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((83306512095/144115188075855872), (9129644651/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-25170578985/576460752303423488), (21061774387/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 7 => ⟨((44082696973/18446744073709551616), (-13935152511/4611686018427387904)), (15/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-15085561413/295147905179352825856), (91310258597/295147905179352825856)), (7/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-20191726825/2361183241434822606848), (-56778869185/2361183241434822606848)), (13/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1837760245/1180591620717411303424), (51966906449/37778931862957161709568)), (47/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-12472127393/75557863725914323419136), (-22135175895/604462909807314587353088)), (21/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((31912588755/2417851639229258349412352), (-18844527645/4835703278458516698824704)), (19/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (3807/1280)))⁻¹=value ((8806400/61827649), (-4872960/61827649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/61827649), (-4872960/61827649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-58137736667/140737488355328), (12694697775/35184372088832)), (5/140737488355328), by norm_num⟩
  | 1 => ⟨((672149667/70368744177664), (-85813877943/281474976710656)), (9/281474976710656), by norm_num⟩
  | 2 => ⟨((5164926619/70368744177664), (39590906569/562949953421312)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((-118010892979/4503599627370496), (5361265021/2251799813685248)), (15/4503599627370496), by norm_num⟩
  | 4 => ⟨((30027980371/9007199254740992), (-10766273303/2251799813685248)), (9/9007199254740992), by norm_num⟩
  | 5 => ⟨((23038621489/72057594037927936), (40185567441/36028797018963968)), (9/36028797018963968), by norm_num⟩
  | 6 => ⟨((-57007008871/288230376151711744), (-23208454283/288230376151711744)), (19/288230376151711744), by norm_num⟩
  | 7 => ⟨((73380389461/2305843009213693952), (-21772945977/1152921504606846976)), (33/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-10755029471/18446744073709551616), (56136136427/9223372036854775808)), (61/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-13613563219/18446744073709551616), (-46675860797/73786976294838206464)), (55/73786976294838206464), by norm_num⟩
  | 10 => ⟨((42617886061/295147905179352825856), (-23359847965/590295810358705651712)), (47/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-16088268953/2361183241434822606848), (101115396455/4722366482869645213696)), (159/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-20252924337/9444732965739290427392), (-47416969545/18889465931478580854784)), (67/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((51/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/27026283), (-541440/9008761)), 0, by norm_num⟩
  | 1 => ⟨((-4741561548800/730419972796089), (628359168000/81157774755121)), 0, by norm_num⟩
  | 2 => ⟨((13050860831/70368744177664), (-48820233767/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((5011685113/562949953421312), (28294131331/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-37538217915/18014398509481984), (-53499487017/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((64409403615/288230376151711744), (37086782781/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-42105469351/2305843009213693952), (-3626079169/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((176314843/144115188075855872), (-2063480159/4611686018427387904)), (13/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-19289899267/295147905179352825856), (19357450223/295147905179352825856)), (11/590295810358705651712), by norm_num⟩
  | 9 => ⟨((21145057789/9444732965739290427392), (-29224253405/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((3155512785/75557863725914323419136), (70402773945/151115727451828646838272)), (7/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-20177262319/1208925819614629174706176), (-34760706489/1208925819614629174706176)), (43/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((75015372113/38685626227668133590597632), (26122288435/19342813113834066795298816)), (33/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (3807/1280)))⁻¹=value ((3481600/27026283), (-541440/9008761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/27026283), (-541440/9008761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35500653351/1125899906842624), (80285025511/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 1 => ⟨((-19370737787/1125899906842624), (-51103562823/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 2 => ⟨((72752407559/4503599627370496), (31772988789/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 3 => ⟨((-40397863565/9007199254740992), (4306829591/2251799813685248)), (15/18014398509481984), by norm_num⟩
  | 4 => ⟨((26915188083/72057594037927936), (-77408890385/72057594037927936)), (19/72057594037927936), by norm_num⟩
  | 5 => ⟨((33563498375/288230376151711744), (14763809181/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-25350374491/576460752303423488), (-18870328571/2305843009213693952)), (41/2305843009213693952), by norm_num⟩
  | 7 => ⟨((55737469253/9223372036854775808), (-23703398965/4611686018427387904)), (19/4611686018427387904), by norm_num⟩
  | 8 => ⟨((4124818007/73786976294838206464), (49133189967/36893488147419103232)), (17/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-52155594957/295147905179352825856), (-35782596803/295147905179352825856)), (31/147573952589676412928), by norm_num⟩
  | 10 => ⟨((73783036019/2361183241434822606848), (-6657093875/590295810358705651712)), (27/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-11944823409/9444732965739290427392), (91298529147/18889465931478580854784)), (183/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-37090917899/75557863725914323419136), (-41089950275/75557863725914323419136)), (77/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((59/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/103606849), (-4872960/103606849)), 0, by norm_num⟩
  | 1 => ⟨((-61128991539200/10734379159708801), (58880950272000/10734379159708801)), 0, by norm_num⟩
  | 2 => ⟨((7145184687/35184372088832), (-63863974835/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-1318066825/1125899906842624), (70339286347/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-24006721693/36028797018963968), (-66618718507/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((23732344957/288230376151711744), (53122627437/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((-64272953983/9223372036854775808), (-31704297579/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((35948076425/73786976294838206464), (168641927/4611686018427387904)), (11/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-17277481835/590295810358705651712), (11008522603/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((28097790849/18889465931478580854784), (-46545669749/37778931862957161709568)), (11/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-17458585809/302231454903657293676544), (64571751121/604462909807314587353088)), (15/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((8281738807/9671406556917033397649408), (-36691912665/4835703278458516698824704)), (5/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((9942452323/77371252455336267181195264), (71583531715/154742504910672534362390528)), (53/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (3807/1280)))⁻¹=value ((12083200/103606849), (-4872960/103606849)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/103606849), (-4872960/103606849))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1456883479/4503599627370496), (44131958265/4503599627370496)), (13/9007199254740992), by norm_num⟩
  | 1 => ⟨((-9801809491/2251799813685248), (-45606719805/9007199254740992)), (7/4503599627370496), by norm_num⟩
  | 2 => ⟨((5829284265/2251799813685248), (9219835249/36028797018963968)), (5/9007199254740992), by norm_num⟩
  | 3 => ⟨((-21260225105/36028797018963968), (8646231591/18014398509481984)), (13/72057594037927936), by norm_num⟩
  | 4 => ⟨((9315001541/576460752303423488), (-106483482139/576460752303423488)), (33/576460752303423488), by norm_num⟩
  | 5 => ⟨((61379104429/2305843009213693952), (34091794903/1152921504606846976)), (35/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-35792322701/4611686018427387904), (143715345/9223372036854775808)), (37/9223372036854775808), by norm_num⟩
  | 7 => ⟨((33766539605/36893488147419103232), (-19684318483/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 8 => ⟨((12065730579/295147905179352825856), (17445896457/73786976294838206464)), (63/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-80882396257/2361183241434822606848), (-44045176711/2361183241434822606848)), (115/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((52419331835/9444732965739290427392), (-23637926533/9444732965739290427392)), (51/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-3493744895/18889465931478580854784), (16993575221/18889465931478580854784)), (173/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-56335538299/604462909807314587353088), (-58720351381/604462909807314587353088)), (293/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((67/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/129411649), (-4872960/129411649)), 0, by norm_num⟩
  | 1 => ⟨((-82268283699200/16747374896899201), (66864807936000/16747374896899201)), 0, by norm_num⟩
  | 2 => ⟨((26072798179/140737488355328), (-10701410607/35184372088832)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-4610723233/1125899906842624), (88327579321/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-685219463/4503599627370496), (-80479134731/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((33543102291/1152921504606846976), (32481704721/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-48022207217/18446744073709551616), (-45000444945/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 7 => ⟨((54290437903/295147905179352825856), (2963163003/36893488147419103232)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-53192532677/4722366482869645213696), (-1876788307/2361183241434822606848)), (3/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((46251025521/75557863725914323419136), (-25679296573/151115727451828646838272)), (7/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-70728838857/2417851639229258349412352), (49647452093/2417851639229258349412352)), (33/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((45039703473/38685626227668133590597632), (-31709704317/19342813113834066795298816)), (39/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-9550192925/309485009821345068724781056), (67362865051/618970019642690137449562112)), (23/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (3807/1280)))⁻¹=value ((13721600/129411649), (-4872960/129411649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/129411649), (-4872960/129411649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12058419563/36028797018963968), (75747173387/72057594037927936)), (1/4503599627370496), by norm_num⟩
  | 1 => ⟨((-49700497559/72057594037927936), (-15218339905/36028797018963968)), (9/36028797018963968), by norm_num⟩
  | 2 => ⟨((94723674685/288230376151711744), (-17563807487/288230376151711744)), (7/72057594037927936), by norm_num⟩
  | 3 => ⟨((-35031729005/576460752303423488), (47574357451/576460752303423488)), (19/576460752303423488), by norm_num⟩
  | 4 => ⟨((-1030205975/288230376151711744), (-14822990449/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((42514979511/9223372036854775808), (31626201027/9223372036854775808)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-41736549665/36893488147419103232), (14676080693/73786976294838206464)), (7/9223372036854775808), by norm_num⟩
  | 7 => ⟨((33379145833/295147905179352825856), (-13241138463/73786976294838206464)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((25076764677/2361183241434822606848), (41524962289/1180591620717411303424)), (25/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-26255169967/4722366482869645213696), (-22221291749/9444732965739290427392)), (91/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((7870196495/9444732965739290427392), (-34325938283/75557863725914323419136)), (161/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-12911067773/604462909807314587353088), (10738783583/75557863725914323419136)), (277/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-18234742429/1208925819614629174706176), (-17804998041/1208925819614629174706176)), (59/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((75/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/52831083), (-541440/17610361)), 0, by norm_num⟩
  | 1 => ⟨((-11787992268800/2791123330952889), (924057600000/310124814550321)), 0, by norm_num⟩
  | 2 => ⟨((22355388839/140737488355328), (-58914715383/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-10086700757/2251799813685248), (28336951045/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((850352669/36028797018963968), (-6112659819/9007199254740992)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((5354704801/576460752303423488), (76663061669/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-35462411195/36893488147419103232), (-27084348003/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((20408806809/295147905179352825856), (33274566005/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-79660596707/18889465931478580854784), (-31516268343/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((69512829807/302231454903657293676544), (4840937063/302231454903657293676544)), (11/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-110168150671/9671406556917033397649408), (26688979879/9671406556917033397649408)), (23/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((39424479535/77371252455336267181195264), (-11947357107/38685626227668133590597632)), (3/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-49377196535/2475880078570760549798248448), (56445227859/2475880078570760549798248448)), (25/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (3807/1280)))⁻¹=value ((5120000/52831083), (-541440/17610361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/52831083), (-541440/17610361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2333057085/36028797018963968), (26397495097/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 1 => ⟨((-6079952117/72057594037927936), (-13357447775/576460752303423488)), (5/144115188075855872), by norm_num⟩
  | 2 => ⟨((79368257157/2305843009213693952), (-37317773113/2305843009213693952)), (17/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-687593117/144115188075855872), (25778896407/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 4 => ⟨((-19879074681/18446744073709551616), (-55288166757/18446744073709551616)), (15/9223372036854775808), by norm_num⟩
  | 5 => ⟨((47993625313/73786976294838206464), (23556522821/73786976294838206464)), (35/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-41304393745/295147905179352825856), (28680443619/590295810358705651712)), (73/590295810358705651712), by norm_num⟩
  | 7 => ⟨((27099582417/2361183241434822606848), (-936129007/36893488147419103232)), (37/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((9183082461/4722366482869645213696), (84778500081/18889465931478580854784)), (17/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-58509747315/75557863725914323419136), (-18486031641/75557863725914323419136)), (123/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((32663007037/302231454903657293676544), (-5266096475/75557863725914323419136)), (55/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-9021687801/4835703278458516698824704), (11768396127/604462909807314587353088)), (95/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-320892193/151115727451828646838272), (-37441135873/19342813113834066795298816)), (325/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((83/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/190851649), (-4872960/190851649)), 0, by norm_num⟩
  | 1 => ⟨((-132599931699200/36424351926019201), (82832523264000/36424351926019201)), 0, by norm_num⟩
  | 2 => ⟨((37460645051/281474976710656), (-41587171697/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-9098551821/2251799813685248), (37283811125/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((10700594055/144115188075855872), (-60565482937/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((9493463501/4611686018427387904), (45340341679/2305843009213693952)), (9/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-25286950819/73786976294838206464), (-62673401793/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((15409721397/590295810358705651712), (39491416841/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-60052616973/37778931862957161709568), (-43687040971/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((12928194375/151115727451828646838272), (9430901943/302231454903657293676544)), (9/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-10174890267/2417851639229258349412352), (-5753259459/19342813113834066795298816)), (17/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((29587174087/154742504910672534362390528), (-6263680973/154742504910672534362390528)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-39604537295/4951760157141521099596496896), (10506576047/2475880078570760549798248448)), (15/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (3807/1280)))⁻¹=value ((16998400/190851649), (-4872960/190851649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/190851649), (-4872960/190851649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((74763801597/9223372036854775808), (59986114947/9223372036854775808)), (17/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-9858287263/1152921504606846976), (-881599933/9223372036854775808)), (5/1152921504606846976), by norm_num⟩
  | 2 => ⟨((55976355841/18446744073709551616), (-44737013211/18446744073709551616)), (9/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-4494899391/18446744073709551616), (46644528561/36893488147419103232)), (13/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-26238208493/147573952589676412928), (-22050902145/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 5 => ⟨((91868909707/1180591620717411303424), (26995021543/1180591620717411303424)), (79/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-70746094207/4722366482869645213696), (37192083445/4722366482869645213696)), (21/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((17774359635/18889465931478580854784), (-29231183237/9444732965739290427392)), (43/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((43128267637/151115727451828646838272), (75547427883/151115727451828646838272)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-28503113771/302231454903657293676544), (-12475577645/604462909807314587353088)), (73/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((59524755685/4835703278458516698824704), (-44739036941/4835703278458516698824704)), (261/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-3834848877/38685626227668133590597632), (90943535357/38685626227668133590597632)), (455/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-40875280231/154742504910672534362390528), (-17341885919/77371252455336267181195264)), (391/154742504910672534362390528), by norm_num⟩
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
  | 0 => ⟨((91/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/226486849), (-4872960/226486849)), 0, by norm_num⟩
  | 1 => ⟨((-161792287539200/51296292769948801), (90816380928000/51296292769948801)), 0, by norm_num⟩
  | 2 => ⟨((62331520303/562949953421312), (-60107137595/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-30686475765/9007199254740992), (50296737789/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((2885851621/36028797018963968), (-19195890915/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-990805105/2305843009213693952), (109039516751/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-16159294343/147573952589676412928), (-4528872845/9223372036854775808)), (7/147573952589676412928), by norm_num⟩
  | 7 => ⟨((46219852443/4722366482869645213696), (89839428269/4722366482869645213696)), (13/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-22944803941/37778931862957161709568), (-6398128505/9444732965739290427392)), (3/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((78037769931/2417851639229258349412352), (51592004405/2417851639229258349412352)), (21/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-15062950383/9671406556917033397649408), (-10265230655/19342813113834066795298816)), (9/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((43197029653/618970019642690137449562112), (3144287907/618970019642690137449562112)), (31/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-7244362267/2475880078570760549798248448), (335334995/618970019642690137449562112)), (53/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (3807/1280)))⁻¹=value ((18636800/226486849), (-4872960/226486849)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/226486849), (-4872960/226486849))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((59541398143/73786976294838206464), (26619760599/73786976294838206464)), (15/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-109609723825/147573952589676412928), (6269844753/36893488147419103232)), (35/73786976294838206464), by norm_num⟩
  | 2 => ⟨((4173547857/18446744073709551616), (-5161979665/18446744073709551616)), (17/73786976294838206464), by norm_num⟩
  | 3 => ⟨((503579521/590295810358705651712), (72739022063/590295810358705651712)), (25/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-52939586209/2361183241434822606848), (-60980483767/2361183241434822606848)), (67/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((76459473061/9444732965739290427392), (9715511339/9444732965739290427392)), (79/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-53171160503/37778931862957161709568), (1198484361/1180591620717411303424)), (43/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((8738208107/151115727451828646838272), (-25072143881/75557863725914323419136)), (11/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((21416906697/604462909807314587353088), (29782832667/604462909807314587353088)), (167/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-12321626955/1208925819614629174706176), (-6360184277/4835703278458516698824704)), (153/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((24126915829/19342813113834066795298816), (-41845187631/38685626227668133590597632)), (275/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((847779249/309485009821345068724781056), (19613352801/77371252455336267181195264)), (481/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-72786362067/2475880078570760549798248448), (-28671271711/1237940039285380274899124224)), (415/1237940039285380274899124224), by norm_num⟩
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
  | 0 => ⟨((99/8), (3807/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/29488761), (-60160/3276529)), 0, by norm_num⟩
  | 1 => ⟨((-2390975283200/869587025315121), (135528448000/96620780590569)), 0, by norm_num⟩
  | 2 => ⟨((25937652429/281474976710656), (-44372446337/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-50372910243/18014398509481984), (69477106709/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((20580697179/288230376151711744), (-6232609587/36028797018963968)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-5254210993/4611686018427387904), (66992191745/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-427243425/18446744073709551616), (-42486610967/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((16659311007/4722366482869645213696), (12732067481/1180591620717411303424)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-17662240419/75557863725914323419136), (-57356734185/151115727451828646838272)), (13/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((60027870599/4835703278458516698824704), (3733190549/302231454903657293676544)), (21/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-45460456189/77371252455336267181195264), (-27688003967/77371252455336267181195264)), (17/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((31850699613/1237940039285380274899124224), (20488579191/2475880078570760549798248448)), (27/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-20970680795/19807040628566084398385987584), (-1582458565/19807040628566084398385987584)), (21/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (3807/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (3807/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (3807/1280)))⁻¹=value ((2252800/29488761), (-60160/3276529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/29488761), (-60160/3276529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((40299520191/590295810358705651712), (3761555403/295147905179352825856)), (23/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-33261121535/590295810358705651712), (31593020115/1180591620717411303424)), (7/147573952589676412928), by norm_num⟩
  | 2 => ⟨((33181647619/2361183241434822606848), (-63920476423/2361183241434822606848)), (29/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((2407728553/1180591620717411303424), (49873794529/4722366482869645213696)), (87/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-22307430367/9444732965739290427392), (-36759361929/18889465931478580854784)), (59/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((56322774407/75557863725914323419136), (-657512611/37778931862957161709568)), (141/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-35420122045/302231454903657293676544), (8379580565/75557863725914323419136)), (79/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((2155908739/1208925819614629174706176), (-19175882457/604462909807314587353088)), (161/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((37085701321/9671406556917033397649408), (41990415685/9671406556917033397649408)), (155/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-38264555813/38685626227668133590597632), (-3402851915/77371252455336267181195264)), (287/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((35162244835/309485009821345068724781056), (-8738101113/77371252455336267181195264)), (259/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((7728099207/4951760157141521099596496896), (61086414437/2475880078570760549798248448)), (909/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-29287150147/9903520314283042199192993792), (-42737230135/19807040628566084398385987584)), (787/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2880126969/1099511627776), (67419848609/1099511627776)), (579/1099511627776), by norm_num⟩
  | 1 => ⟨((-20800212409/549755813888), (19932446603/549755813888)), (709/549755813888), by norm_num⟩
  | 2 => ⟨((-87406649187/4398046511104), (-5686562585/4398046511104)), (6907/4398046511104), by norm_num⟩
  | 3 => ⟨((-50725658939/17592186044416), (-13681082167/4398046511104)), (22339/17592186044416), by norm_num⟩
  | 4 => ⟨((-9998337925/70368744177664), (-9054771257/17592186044416)), (109347/140737488355328), by norm_num⟩
  | 5 => ⟨((-8709271573/281474976710656), (-9856157403/140737488355328)), (217165/562949953421312), by norm_num⟩
  | 6 => ⟨((-3086578209/4503599627370496), (-70379137131/4503599627370496)), (182635/1125899906842624), by norm_num⟩
  | 7 => ⟨((9842551857/9007199254740992), (-11881199347/9007199254740992)), (1071975/18014398509481984), by norm_num⟩
  | 8 => ⟨((3385748989/144115188075855872), (-54182457837/1152921504606846976)), (5610615/288230376151711744), by norm_num⟩
  | 9 => ⟨((4933031347/2305843009213693952), (-117895862371/4611686018427387904)), (26635997/4611686018427387904), by norm_num⟩
  | 10 => ⟨((65719306243/18446744073709551616), (-9331931559/9223372036854775808)), (7263329/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-1812809903/36893488147419103232), (80464420351/295147905179352825856)), (58877443/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-7286151833/295147905179352825856), (-56531099115/1180591620717411303424)), (55907783/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2880126969/1099511627776), (67419848609/1099511627776)), (145/274877906944), by norm_num⟩
  | 1 => ⟨((-20800212409/549755813888), (19932446603/549755813888)), (1419/1099511627776), by norm_num⟩
  | 2 => ⟨((-87406649187/4398046511104), (-5686562585/4398046511104)), (1727/1099511627776), by norm_num⟩
  | 3 => ⟨((-50725658939/17592186044416), (-13681082167/4398046511104)), (5585/4398046511104), by norm_num⟩
  | 4 => ⟨((-9998337925/70368744177664), (-9054771257/17592186044416)), (109353/140737488355328), by norm_num⟩
  | 5 => ⟨((-8709271573/281474976710656), (-9856157403/140737488355328)), (54297/140737488355328), by norm_num⟩
  | 6 => ⟨((-3086578209/4503599627370496), (-70379137131/4503599627370496)), (730721/4503599627370496), by norm_num⟩
  | 7 => ⟨((9842551857/9007199254740992), (-11881199347/9007199254740992)), (134087/2251799813685248), by norm_num⟩
  | 8 => ⟨((3385748989/144115188075855872), (-54182457837/1152921504606846976)), (22488577/1152921504606846976), by norm_num⟩
  | 9 => ⟨((4933031347/2305843009213693952), (-117895862371/4611686018427387904)), (26820465/4611686018427387904), by norm_num⟩
  | 10 => ⟨((65719306243/18446744073709551616), (-9331931559/9223372036854775808)), (14895593/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-1812809903/36893488147419103232), (80464420351/295147905179352825856)), (129560803/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-7286151833/295147905179352825856), (-56531099115/1180591620717411303424)), (159039231/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile013Gamma
