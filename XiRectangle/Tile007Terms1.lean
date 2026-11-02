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
namespace Reinmann.XiRectangle.Tile007Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/128))
  have he : value ((3/4), (423/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/33554432), (-31186361389/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((484252340492321/4503599627370496), (-44926155839307/281474976710656)), (425715/4503599627370496), by norm_num⟩
  | 1 => ⟨((-16235521609/68719476736), (3012477227/8589934592)), (31/137438953472), by norm_num⟩
  | 2 => ⟨((35673087105/137438953472), (-52952712015/137438953472)), (9/34359738368), by norm_num⟩
  | 3 => ⟨((-52254522491/274877906944), (9695750023/34359738368)), (55/274877906944), by norm_num⟩
  | 4 => ⟨((14351865137/137438953472), (-10651870123/68719476736)), (33/274877906944), by norm_num⟩
  | 5 => ⟨((-50454833295/1099511627776), (18723640663/274877906944)), (61/1099511627776), by norm_num⟩
  | 6 => ⟨((18476766627/1099511627776), (-6856673907/274877906944)), (47/2199023255552), by norm_num⟩
  | 7 => ⟨((-23198631853/4398046511104), (68871553953/8796093022208)), (61/8796093022208), by norm_num⟩
  | 8 => ⟨((12743151017/8796093022208), (-9457891939/4398046511104)), (35/17592186044416), by norm_num⟩
  | 9 => ⟨((-24888501873/70368744177664), (18472100105/35184372088832)), (71/140737488355328), by norm_num⟩
  | 10 => ⟨((43748502407/562949953421312), (-64939763753/562949953421312)), (65/562949953421312), by norm_num⟩
  | 11 => ⟨((-17477324493/1125899906842624), (3242891931/140737488355328)), (27/1125899906842624), by norm_num⟩
  | 12 => ⟨((51202142563/18014398509481984), (-76003859759/18014398509481984)), (41/9007199254740992), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-318473988053/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444856472765175/158456325028528675187087900672), (-1508651293601/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472620242875373/9903520314283042199192993792), (-1696985181567/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945151035606091/1237940039285380274899124224), (-1802743525627/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771968130980337/154742504910672534362390528), (-1802402473275/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((775141038595983/4835703278458516698824704), (-1689390031281/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39357064139601/18889465931478580854784), (-369463520187/151115727451828646838272)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472206847916121/18889465931478580854784), (-300104244429/9444732965739290427392)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1298315632603433/4722366482869645213696), (-112501974959/295147905179352825856)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622514823472267/590295810358705651712), (-2474078776291/590295810358705651712)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456201799382857/18446744073709551616), (-3091152093453/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456038730631797/2305843009213693952), (-3475558363939/9223372036854775808)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595402020903899/1152921504606846976), (-3473075227281/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298954580182203/36028797018963968), (-1518074705597/72057594037927936)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((186686322231797/4503599627370496), (-2274323288975/18014398509481984)), (1099/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491568629596181/9007199254740992), (-1419014853529/2251799813685248)), (1375/9007199254740992), by norm_num⟩
  | 2 => ⟨((139534590713217/281474976710656), (-1415364986481/562949953421312)), (2753/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222970600446843/2251799813685248), (-16911548481949/2251799813685248)), (4139/2251799813685248), by norm_num⟩
  | 0 => ⟨((2194302736081267/2251799813685248), (-16766382826903/1125899906842624)), (65/17592186044416), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2194302736081267/2251799813685248), (-16766382826903/1125899906842624)), (247955389374489/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((2137774424682589/2251799813685248), (-65353091314185/2251799813685248)), (1029/140737488355328), by norm_num⟩
  | 2 => ⟨((506906568307503/562949953421312), (-62043777753389/1125899906842624)), (32217/2251799813685248), by norm_num⟩
  | 3 => ⟨((454732982653303/562949953421312), (-223468521666375/2251799813685248)), (61571/2251799813685248), by norm_num⟩
  | 4 => ⟨((1447098080488619/2251799813685248), (-361021461211219/2251799813685248)), (27923/562949953421312), by norm_num⟩
  | 5 => ⟨((872083009850205/2251799813685248), (-29000883002503/140737488355328)), (89685/1125899906842624), by norm_num⟩
  | 6 => ⟨((484252340492321/4503599627370496), (-44926155839307/281474976710656)), (425715/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-31186361389/4294967296)), (1/4294967296), by norm_num⟩, -1, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7417145753/4294967296), (-16340899237/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((387977857534031/9007199254740992), (-1554032693807861/9007199254740992)), (921073/9007199254740992), by norm_num⟩
  | 1 => ⟨((-6815735101/68719476736), (54600410687/137438953472)), (17/68719476736), by norm_num⟩
  | 2 => ⟨((15693810041/137438953472), (-62861045859/137438953472)), (41/137438953472), by norm_num⟩
  | 3 => ⟨((-12045444351/137438953472), (12061908927/34359738368)), (65/274877906944), by norm_num⟩
  | 4 => ⟨((3466957575/68719476736), (-3471696461/17179869184)), (5/34359738368), by norm_num⟩
  | 5 => ⟨((-25545487457/1099511627776), (25580404859/274877906944)), (19/274877906944), by norm_num⟩
  | 6 => ⟨((4901721551/549755813888), (-78534745201/2199023255552)), (15/549755813888), by norm_num⟩
  | 7 => ⟨((-25798013653/8796093022208), (12916638113/1099511627776)), (41/4398046511104), by norm_num⟩
  | 8 => ⟨((14850530417/17592186044416), (-59483316741/17592186044416)), (49/17592186044416), by norm_num⟩
  | 9 => ⟨((-15197604427/70368744177664), (15218377601/17592186044416)), (13/17592186044416), by norm_num⟩
  | 10 => ⟨((13997510961/281474976710656), (-28033287523/140737488355328)), (25/140737488355328), by norm_num⟩
  | 11 => ⟨((-11720167301/1125899906842624), (11736187265/281474976710656)), (43/1125899906842624), by norm_num⟩
  | 12 => ⟨((4497780419/2251799813685248), (-9007856615/1125899906842624)), (17/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (-3373913943/19807040628566084398385987584)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889651488493587/316912650057057350374175801344), (-1022756567191/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890342655194793/39614081257132168796771975168), (-287606244925/4951760157141521099596496896)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890155060133351/2475880078570760549798248448), (-1222111054899/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885910531849025/77371252455336267181195264), (-2443737371483/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775072070970505/4835703278458516698824704), (-2290488860857/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314826324874125/151115727451828646838272), (-2003662951559/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944315528194629/37778931862957161709568), (-3254987304905/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324542070878157/1180591620717411303424), (-2440396372959/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622312060006125/590295810358705651712), (-3354173831669/590295810358705651712)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228069188228857/9223372036854775808), (-2095330688131/36893488147419103232)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823869193521479/9223372036854775808), (-1177917140487/2305843009213693952)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595115885401619/1152921504606846976), (-4708138794985/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195567495963497/144115188075855872), (-1028913332913/36028797018963968)), (367/72057594037927936), by norm_num⟩
  | 4 => ⟨((373278357767607/9007199254740992), (-3082775475305/18014398509481984)), (1101/36028797018963968), by norm_num⟩
  | 3 => ⟨((745547805232675/4503599627370496), (-3846539501817/4503599627370496)), (689/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115801340495981/2251799813685248), (-15344643493013/4503599627370496)), (345/562949953421312), by norm_num⟩
  | 1 => ⟨((1110766350482491/1125899906842624), (-5728351154461/562949953421312)), (2077/1125899906842624), by norm_num⟩
  | 0 => ⟨((273922559880429/281474976710656), (-45413918933963/2251799813685248)), (2091/562949953421312), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((273922559880429/281474976710656), (-45413918933963/2251799813685248)), (7976534129905523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2131666390026013/2251799813685248), (-22097695990541/562949953421312)), (8309/1125899906842624), by norm_num⟩
  | 2 => ⟨((1007236220579763/1125899906842624), (-20918784855461/281474976710656)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((1789720860562021/2251799813685248), (-149712475639317/1125899906842624)), (63501/2251799813685248), by norm_num⟩
  | 4 => ⟨((691323766517959/1125899906842624), (-475963341163189/2251799813685248)), (58915/1125899906842624), by norm_num⟩
  | 5 => ⟨((374183594882079/1125899906842624), (-584500927191925/2251799813685248)), (12157/140737488355328), by norm_num⟩
  | 6 => ⟨((387977857534031/9007199254740992), (-1554032693807861/9007199254740992)), (921073/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-16340899237/2147483648)), (1/4294967296), by norm_num⟩, -1, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1931040333/1073741824), (-68069171737/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-52383240639175/4503599627370496), (-743773703840215/4503599627370496)), (951975/9007199254740992), by norm_num⟩
  | 1 => ⟨((7666596991/274877906944), (27213919807/68719476736)), (9/34359738368), by norm_num⟩
  | 2 => ⟨((-4595924171/137438953472), (-65256129659/137438953472)), (45/137438953472), by norm_num⟩
  | 3 => ⟨((918378737/34359738368), (26079560805/68719476736)), (37/137438953472), by norm_num⟩
  | 4 => ⟨((-68818001/4294967296), (-62536055571/274877906944)), (23/137438953472), by norm_num⟩
  | 5 => ⟨((8448939995/1099511627776), (59981964813/549755813888)), (91/1099511627776), by norm_num⟩
  | 6 => ⟨((-6753224425/2199023255552), (-95886979919/2199023255552)), (75/2199023255552), by norm_num⟩
  | 7 => ⟨((4626721407/4398046511104), (65693410249/4398046511104)), (53/4398046511104), by norm_num⟩
  | 8 => ⟨((-5547196695/17592186044416), (-78762958945/17592186044416)), (65/17592186044416), by norm_num⟩
  | 9 => ⟨((2955910385/35184372088832), (20985036325/17592186044416)), (71/70368744177664), by norm_num⟩
  | 10 => ⟨((-5670370831/281474976710656), (-80511871045/281474976710656)), (35/140737488355328), by norm_num⟩
  | 11 => ⟨((2472173711/562949953421312), (8775410681/140737488355328)), (63/1125899906842624), by norm_num⟩
  | 12 => ⟨((-7904018207/9007199254740992), (-112226750873/9007199254740992)), (103/9007199254740992), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (-267215999883/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444797883915933/158456325028528675187087900672), (-2531043139713/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890217235340945/39614081257132168796771975168), (-5560485389/77371252455336267181195264)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945010868906621/1237940039285380274899124224), (-3024348532061/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885843834875083/77371252455336267181195264), (-3023723691419/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96876188066543/604462909807314587353088), (-2834077199965/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259195732240655/604462909807314587353088), (-2479153938163/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888452867248835/75557863725914323419136), (-4027381193835/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298034517231089/4722366482869645213696), (-1509723875291/2361183241434822606848)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811063964709759/295147905179352825856), (-4149973014991/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912161520049261/36893488147419103232), (-1296203960919/18446744073709551616)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911804752163345/4611686018427387904), (-2914637588107/4611686018427387904)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594855678183921/1152921504606846976), (-5824724395689/1152921504606846976)), (419/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195339233293045/144115188075855872), (-1272879423829/36028797018963968)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492769877902009/36028797018963968), (-7627052931967/36028797018963968)), (1103/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490664148437957/9007199254740992), (-9515944394133/9007199254740992)), (345/2251799813685248), by norm_num⟩
  | 2 => ⟨((2230733727042067/4503599627370496), (-1186146977497/281474976710656)), (2767/4503599627370496), by norm_num⟩
  | 1 => ⟨((277526788290501/281474976710656), (-14166979014985/1125899906842624)), (521/281474976710656), by norm_num⟩
  | 0 => ⟨((1094342249324649/1125899906842624), (-56135277909055/2251799813685248)), (8405/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1094342249324649/1125899906842624), (-56135277909055/2251799813685248)), (32062539107512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((531484707933161/562949953421312), (-109123743451995/2251799813685248)), (16759/2251799813685248), by norm_num⟩
  | 2 => ⟨((250228056324563/281474976710656), (-206048870115995/2251799813685248)), (16635/1125899906842624), by norm_num⟩
  | 3 => ⟨((1760744880621131/2251799813685248), (-91587552256907/562949953421312)), (65243/2251799813685248), by norm_num⟩
  | 4 => ⟨((329293265874823/562949953421312), (-572918827987825/2251799813685248)), (123261/2251799813685248), by norm_num⟩
  | 5 => ⟨((624704242000525/2251799813685248), (-670248965481643/2251799813685248)), (51731/562949953421312), by norm_num⟩
  | 6 => ⟨((-52383240639175/4503599627370496), (-743773703840215/4503599627370496)), (951975/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-68069171737/8589934592)), (1/4294967296), by norm_num⟩, -1, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2001111149/1073741824), (-70539168001/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-30583387545775/562949953421312), (-327130307936303/2251799813685248)), (475669/4503599627370496), by norm_num⟩
  | 1 => ⟨((4638480413/34359738368), (99229526067/274877906944)), (75/274877906944), by norm_num⟩
  | 2 => ⟨((-11526190823/68719476736), (-61644027295/137438953472)), (49/137438953472), by norm_num⟩
  | 3 => ⟨((19094338815/137438953472), (51059884449/137438953472)), (43/137438953472), by norm_num⟩
  | 4 => ⟨((-23723824747/274877906944), (-63439523203/274877906944)), (7/34359738368), by norm_num⟩
  | 5 => ⟨((23580595949/549755813888), (63056517227/549755813888)), (57/549755813888), by norm_num⟩
  | 6 => ⟨((-19531859893/1099511627776), (-26114926495/549755813888)), (49/1099511627776), by norm_num⟩
  | 7 => ⟨((27734199161/4398046511104), (37081802575/2199023255552)), (9/549755813888), by norm_num⟩
  | 8 => ⟨((-34458447961/17592186044416), (-92144817805/17592186044416)), (23/4398046511104), by norm_num⟩
  | 9 => ⟨((4757001471/8796093022208), (50882504557/35184372088832)), (53/35184372088832), by norm_num⟩
  | 10 => ⟨((-18913127341/140737488355328), (-50575309573/140737488355328)), (55/140737488355328), by norm_num⟩
  | 11 => ⟨((34179895199/1125899906842624), (45699972027/562949953421312)), (51/562949953421312), by norm_num⟩
  | 12 => ⟨((-7077820739/1125899906842624), (-75706776257/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-2512288000181/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779089588668877/633825300114114700748351602688), (-743549317989/158456325028528675187087900672)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890102489331515/39614081257132168796771975168), (-836354109619/9903520314283042199192993792)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889899746680273/2475880078570760549798248448), (-888457066627/618970019642690137449562112)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221445699500735/19342813113834066795298816), (-3553067100973/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774952238609523/4835703278458516698824704), (-3330191817915/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259095429237505/604462909807314587353088), (-2913109419087/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472072427675083/18889465931478580854784), (-1183071842957/18889465931478580854784)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297912006325563/4722366482869645213696), (-3547889880261/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202744905504185/73786976294838206464), (-609524384309/73786976294838206464)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824111834531563/73786976294838206464), (-6092014746005/73786976294838206464)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911685709615825/4611686018427387904), (-6849078480903/9223372036854775808)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594616995770151/1152921504606846976), (-6843533695877/1152921504606846976)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195129715875205/144115188075855872), (-186933063137/4503599627370496)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492454265352637/36028797018963968), (-4480164451821/18014398509481984)), (1105/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490267303421787/9007199254740992), (-5589315730109/4503599627370496)), (1383/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114966543293275/2251799813685248), (-11146006068227/2251799813685248)), (1387/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109498050361215/1125899906842624), (-16637600042515/1125899906842624)), (1045/562949953421312), by norm_num⟩
  | 0 => ⟨((34159060811017/35184372088832), (-4118811323051/140737488355328)), (4221/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((34159060811017/35184372088832), (-4118811323051/140737488355328)), (16101841453170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2120543554285317/2251799813685248), (-127961108276581/2251799813685248)), (16887/2251799813685248), by norm_num⟩
  | 2 => ⟨((497416654575659/562949953421312), (-60251160362037/562949953421312)), (16863/1125899906842624), by norm_num⟩
  | 3 => ⟨((433063586634341/562949953421312), (-212949164944021/1125899906842624)), (16705/562949953421312), by norm_num⟩
  | 4 => ⟨((313006924123745/562949953421312), (-163816567673517/562949953421312)), (128083/2251799813685248), by norm_num⟩
  | 5 => ⟨((505462102076677/2251799813685248), (-364335903441293/1125899906842624)), (13561/140737488355328), by norm_num⟩
  | 6 => ⟨((-30583387545775/562949953421312), (-327130307936303/2251799813685248)), (475669/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-70539168001/8589934592)), (1/4294967296), by norm_num⟩, -1, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-16524560409/8589934592), (-4550709019/536870912)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-95870616146875/1125899906842624), (-1068941084296261/9007199254740992)), (926527/9007199254740992), by norm_num⟩
  | 1 => ⟨((30017489659/137438953472), (41836238821/137438953472)), (19/68719476736), by norm_num⟩
  | 2 => ⟨((-38496670407/137438953472), (-26826958471/68719476736)), (51/137438953472), by norm_num⟩
  | 3 => ⟨((16457001671/68719476736), (22936596631/68719476736)), (45/137438953472), by norm_num⟩
  | 4 => ⟨((-21105687931/137438953472), (-58831208791/274877906944)), (15/68719476736), by norm_num⟩
  | 5 => ⟨((21654008279/274877906944), (60359628475/549755813888)), (1/8589934592), by norm_num⟩
  | 6 => ⟨((-37027623081/1099511627776), (-51606463425/1099511627776)), (57/1099511627776), by norm_num⟩
  | 7 => ⟨((54270844589/4398046511104), (75638837259/4398046511104)), (43/2199023255552), by norm_num⟩
  | 8 => ⟨((-17400245995/4398046511104), (-48502446757/8796093022208)), (57/8796093022208), by norm_num⟩
  | 9 => ⟨((19835888793/17592186044416), (13822924405/8796093022208)), (67/35184372088832), by norm_num⟩
  | 10 => ⟨((-10175610043/35184372088832), (-28364080857/70368744177664)), (71/140737488355328), by norm_num⟩
  | 11 => ⟨((37963526461/562949953421312), (52910858887/562949953421312)), (17/140737488355328), by norm_num⟩
  | 12 => ⟨((-8114543567/562949953421312), (-45237891169/2251799813685248)), (15/562949953421312), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418293/10141204801825835211973625643008), (-1428424900065/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((55593613447863/19807040628566084398385987584), (-1690887619321/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944998362720813/19807040628566084398385987584), (-950960854345/9903520314283042199192993792)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472446823008777/618970019642690137449562112), (-4040789139935/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771453050866715/154742504910672534362390528), (-4039895449935/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549798870073473/9671406556917033397649408), (-1893226299221/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259002926988797/604462909807314587353088), (-414024602163/75557863725914323419136)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236017401840711/9444732965739290427392), (-168141888995/2361183241434822606848)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648899488587095/2361183241434822606848), (-1008462189955/1180591620717411303424)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101362723366987/36893488147419103232), (-5544013324491/590295810358705651712)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911958432388545/36893488147419103232), (-1731556207075/18446744073709551616)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823151553854051/9223372036854775808), (-7786791206211/9223372036854775808)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797198238131919/576460752303423488), (-3890139802879/576460752303423488)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194936027302485/144115188075855872), (-6800423309243/144115188075855872)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((746081134601761/18014398509481984), (-10186002789787/36028797018963968)), (553/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489899758080109/9007199254740992), (-12706920862673/9007199254740992)), (1385/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114595193882573/2251799813685248), (-12668594324931/2251799813685248)), (695/1125899906842624), by norm_num⟩
  | 1 => ⟨((554465794981663/562949953421312), (-18907241213857/1125899906842624)), (131/70368744177664), by norm_num⟩
  | 0 => ⟨((272979930477677/281474976710656), (-37432879137401/1125899906842624)), (4239/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((272979930477677/281474976710656), (-37432879137401/1125899906842624)), (16170506003951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((528860270535355/562949953421312), (-72606274731207/1125899906842624)), (8505/1125899906842624), by norm_num⟩
  | 2 => ⟨((1977975244700353/2251799813685248), (-272838278881057/2251799813685248)), (34155/2251799813685248), by norm_num⟩
  | 3 => ⟨((852195057238135/1125899906842624), (-479320904241637/2251799813685248)), (68281/2251799813685248), by norm_num⟩
  | 4 => ⟨((1188026181023277/2251799813685248), (-90699648997025/281474976710656)), (66217/1125899906842624), by norm_num⟩
  | 5 => ⟨((196490584201793/1125899906842624), (-765635076178393/2251799813685248)), (225091/2251799813685248), by norm_num⟩
  | 6 => ⟨((-95870616146875/1125899906842624), (-1068941084296261/9007199254740992)), (926527/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-16524560409/8589934592), (-4550709019/536870912)), (1/4294967296), by norm_num⟩, -1, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2125249673/1073741824), (-74915050975/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-949017051629251/9007199254740992), (-805070574586157/9007199254740992)), (883271/9007199254740992), by norm_num⟩
  | 1 => ⟨((38215795991/137438953472), (253275323/1073741824)), (37/137438953472), by norm_num⟩
  | 2 => ⟨((-50426838259/137438953472), (-42778118245/137438953472)), (51/137438953472), by norm_num⟩
  | 3 => ⟨((11089943093/34359738368), (37631302167/137438953472)), (47/137438953472), by norm_num⟩
  | 4 => ⟨((-58533991209/274877906944), (-3103473869/17179869184)), (65/274877906944), by norm_num⟩
  | 5 => ⟨((61789823413/549755813888), (6552196369/68719476736)), (71/549755813888), by norm_num⟩
  | 6 => ⟨((-54355628791/1099511627776), (-46110991607/1099511627776)), (65/1099511627776), by norm_num⟩
  | 7 => ⟨((2561564653/137438953472), (34768442965/2199023255552)), (51/2199023255552), by norm_num⟩
  | 8 => ⟨((-27040463891/4398046511104), (-45877957123/8796093022208)), (35/4398046511104), by norm_num⟩
  | 9 => ⟨((63432297269/35184372088832), (53810915117/35184372088832)), (21/8796093022208), by norm_num⟩
  | 10 => ⟨((-66960587617/140737488355328), (-56804035981/140737488355328)), (91/140737488355328), by norm_num⟩
  | 11 => ⟨((8032401343/70368744177664), (27256201365/281474976710656)), (89/562949953421312), by norm_num⟩
  | 12 => ⟨((-56527913703/2251799813685248), (-47953785327/2251799813685248)), (81/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (-3175864198865/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889454243984817/316912650057057350374175801344), (-3759061459261/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118118664120631/2475880078570760549798248448), (-1057048601147/9903520314283042199192993792)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889682975750533/2475880078570760549798248448), (-2245773798639/1237940039285380274899124224)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771348638423029/154742504910672534362390528), (-4490525112585/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549700881317473/9671406556917033397649408), (-4208781067673/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258917084826093/604462909807314587353088), (-3681597393757/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887999530147743/75557863725914323419136), (-1495139958029/18889465931478580854784)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324423511687185/1180591620717411303424), (-4483638826237/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101353688970517/36893488147419103232), (-3081054960567/295147905179352825856)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911867885476535/36893488147419103232), (-3849149247975/36893488147419103232)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822947266200727/9223372036854775808), (-1081827739221/1152921504606846976)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594191493738327/1152921504606846976), (-8647170199815/1152921504606846976)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194755887927997/144115188075855872), (-3778947543565/72057594037927936)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((745945252986319/18014398509481984), (-11320095818637/36028797018963968)), (1107/36028797018963968), by norm_num⟩
  | 3 => ⟨((372389336459729/2251799813685248), (-7060418663999/4503599627370496)), (1387/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114248742481867/2251799813685248), (-7038481347215/1125899906842624)), (1393/2251799813685248), by norm_num⟩
  | 1 => ⟨((554200947888765/562949953421312), (-10502964724245/562949953421312)), (2101/1125899906842624), by norm_num⟩
  | 0 => ⟨((545410374276905/562949953421312), (-41574835412519/1125899906842624)), (4255/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((545410374276905/562949953421312), (-41574835412519/1125899906842624)), (16231541160201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527649674413729/562949953421312), (-80559013834299/1125899906842624)), (535/70368744177664), by norm_num⟩
  | 2 => ⟨((245840450424795/281474976710656), (-151014978018647/1125899906842624)), (17273/1125899906842624), by norm_num⟩
  | 3 => ⟨((52413346410545/70368744177664), (-131896592197459/562949953421312)), (34807/1125899906842624), by norm_num⟩
  | 4 => ⟨((35176629922609/70368744177664), (-785933227372857/2251799813685248)), (34081/562949953421312), by norm_num⟩
  | 5 => ⟨((288392306412785/2251799813685248), (-1571520572450521/4503599627370496)), (462911/4503599627370496), by norm_num⟩
  | 6 => ⟨((-949017051629251/9007199254740992), (-805070574586157/9007199254740992)), (883271/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-74915050975/8589934592)), (1/4294967296), by norm_num⟩, -1, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8723240287/4294967296), (-76873555031/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1050631039645853/9007199254740992), (-67624875574603/1125899906842624)), (206685/2251799813685248), by norm_num⟩
  | 1 => ⟨((86827441351/274877906944), (44709853003/274877906944)), (71/274877906944), by norm_num⟩
  | 2 => ⟨((-58783267503/137438953472), (-7567282901/34359738368)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((26531339897/68719476736), (13661721321/68719476736)), (47/137438953472), by norm_num⟩
  | 4 => ⟨((-71848200343/274877906944), (-36996627171/274877906944)), (33/137438953472), by norm_num⟩
  | 5 => ⟨((77827413355/549755813888), (10018872365/137438953472)), (37/274877906944), by norm_num⟩
  | 6 => ⟨((-70253514129/1099511627776), (-36175479097/1099511627776)), (69/1099511627776), by norm_num⟩
  | 7 => ⟨((54357155161/2199023255552), (27990003841/2199023255552)), (55/2199023255552), by norm_num⟩
  | 8 => ⟨((-36800476241/4398046511104), (-37899167765/8796093022208)), (77/8796093022208), by norm_num⟩
  | 9 => ⟨((88584477409/35184372088832), (45614599505/35184372088832)), (95/35184372088832), by norm_num⟩
  | 10 => ⟨((-11994560593/17592186044416), (-1544082817/4398046511104)), (53/70368744177664), by norm_num⟩
  | 11 => ⟨((47246359601/281474976710656), (12164229187/140737488355328)), (27/140737488355328), by norm_num⟩
  | 12 => ⟨((-85297009079/2251799813685248), (-43921791061/2251799813685248)), (25/562949953421312), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798723/10141204801825835211973625643008), (-434107437357/1267650600228229401496703205376)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111176701892357/39614081257132168796771975168), (-2055122135651/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889807144180947/39614081257132168796771975168), (-4623181226713/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944792843617977/1237940039285380274899124224), (-4911109846475/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771251249701507/154742504910672534362390528), (-4909962176019/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549609473005815/9671406556917033397649408), (-2300935152125/4835703278458516698824704)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258836996263313/604462909807314587353088), (-2012708732343/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471967296785361/18889465931478580854784), (-1634754512565/18889465931478580854784)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297596115490731/4722366482869645213696), (-4902264266143/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621524085671773/590295810358705651712), (-3368682642721/295147905179352825856)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911783337864749/36893488147419103232), (-2104208943727/18446744073709551616)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455689113414481/2305843009213693952), (-9462244949699/9223372036854775808)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593999957286779/1152921504606846976), (-4726939488843/576460752303423488)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((74661717584339/9007199254740992), (-4131368362011/72057594037927936)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((186454534658277/4503599627370496), (-3093825296483/9007199254740992)), (1109/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489236739409913/9007199254740992), (-15436244153797/9007199254740992)), (1389/9007199254740992), by norm_num⟩
  | 2 => ⟨((556961965016777/1125899906842624), (-15386969791589/2251799813685248)), (1395/2251799813685248), by norm_num⟩
  | 1 => ⟨((276976062165051/281474976710656), (-22957441355695/1125899906842624)), (1053/562949953421312), by norm_num⟩
  | 0 => ⟨((1089784258595331/1125899906842624), (-22711934864791/562949953421312)), (4269/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1089784258595331/1125899906842624), (-22711934864791/562949953421312)), (16284946921920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052994493680761/1125899906842624), (-87933603857563/1125899906842624)), (4305/562949953421312), by norm_num⟩
  | 2 => ⟨((244485561803259/281474976710656), (-164479275837549/1125899906842624)), (17451/1125899906842624), by norm_num⟩
  | 3 => ⟨((825399843321895/1125899906842624), (-285729187212783/1125899906842624)), (70829/2251799813685248), by norm_num⟩
  | 4 => ⟨((532590623097323/1125899906842624), (-837874929821409/2251799813685248)), (139801/2251799813685248), by norm_num⟩
  | 5 => ⟨((384205280231907/4503599627370496), (-792689169328771/2251799813685248)), (59075/562949953421312), by norm_num⟩
  | 6 => ⟨((-1050631039645853/9007199254740992), (-67624875574603/1125899906842624)), (206685/2251799813685248), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8723240287/4294967296), (-76873555031/8589934592)), (1/4294967296), by norm_num⟩, -1, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile007Terms1
