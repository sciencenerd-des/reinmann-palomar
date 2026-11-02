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
namespace Reinmann.XiRectangle.Tile010Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2961/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2961/640))
  have he : value ((3/4), (2961/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-55294967/33554432), (-87321811889/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-159891331666077/1125899906842624), (73117686460821/562949953421312)), (612161/4503599627370496), by norm_num⟩
  | 1 => ⟨((2680337247/8589934592), (-39222650813/137438953472)), (43/137438953472), by norm_num⟩
  | 2 => ⟨((-47114422997/137438953472), (43090486177/137438953472)), (49/137438953472), by norm_num⟩
  | 3 => ⟨((69013978771/274877906944), (-63119650185/274877906944)), (37/137438953472), by norm_num⟩
  | 4 => ⟨((-4738725323/34359738368), (34672011675/274877906944)), (21/137438953472), by norm_num⟩
  | 5 => ⟨((2082408749/34359738368), (-30472878479/549755813888)), (77/1099511627776), by norm_num⟩
  | 6 => ⟨((-48805543289/2199023255552), (44637171691/2199023255552)), (59/2199023255552), by norm_num⟩
  | 7 => ⟨((15319534175/2199023255552), (-56044508973/8796093022208)), (77/8796093022208), by norm_num⟩
  | 8 => ⟨((-67320914005/35184372088832), (30785593135/17592186044416)), (87/35184372088832), by norm_num⟩
  | 9 => ⟨((4108865745/8796093022208), (-15031747081/35184372088832)), (11/17592186044416), by norm_num⟩
  | 10 => ⟨((-57779845119/562949953421312), (52844998603/562949953421312)), (5/35184372088832), by norm_num⟩
  | 11 => ⟨((23082781049/1125899906842624), (-42222665353/2251799813685248)), (33/1125899906842624), by norm_num⟩
  | 12 => ⟨((-67624071779/18014398509481984), (61848452023/18014398509481984)), (99/18014398509481984), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (195454743579/633825300114114700748351602688)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889709887879619/316912650057057350374175801344), (925893676729/158456325028528675187087900672)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890473739104985/39614081257132168796771975168), (4165899564097/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890293936555527/2475880078570760549798248448), (2212761095427/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885979745045917/77371252455336267181195264), (4424682833277/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550273438760301/9671406556917033397649408), (4147248406283/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259417956547417/604462909807314587353088), (3627950681383/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888813229023381/75557863725914323419136), (2946874064779/37778931862957161709568)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298304130348707/4722366482869645213696), (4418848496941/4722366482869645213696)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622497578647241/590295810358705651712), (6073540261215/590295810358705651712)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824783499797585/73786976294838206464), (7588361225121/73786976294838206464)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824125321202579/9223372036854775808), (8532006604675/9223372036854775808)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595368748059165/1152921504606846976), (2131470797395/288230376151711744)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195785083670999/144115188075855872), (7453260744077/144115188075855872)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((373358123367263/9007199254740992), (5583060762835/18014398509481984)), (1107/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491481663813027/9007199254740992), (6966782648855/4503599627370496)), (1387/9007199254740992), by norm_num⟩
  | 2 => ⟨((558084149779817/1125899906842624), (3474363958907/562949953421312)), (87/140737488355328), by norm_num⟩
  | 1 => ⟨((555634644973227/562949953421312), (5188995536893/281474976710656)), (2101/1125899906842624), by norm_num⟩
  | 0 => ⟨((34265860582675/35184372088832), (20575796946295/562949953421312)), (1063/281474976710656), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((34265860582675/35184372088832), (20575796946295/562949953421312)), (4055024267101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1066378388815831/1125899906842624), (80154608160589/1125899906842624)), (4297/562949953421312), by norm_num⟩
  | 2 => ⟨((251074296225633/281474976710656), (151834352924235/1125899906842624)), (547/35184372088832), by norm_num⟩
  | 3 => ⟨((54709523848741/70368744177664), (135435496784903/562949953421312)), (35949/1125899906842624), by norm_num⟩
  | 4 => ⟨((1230785601045227/2251799813685248), (421187652439115/1125899906842624)), (18299/281474976710656), by norm_num⟩
  | 5 => ⟨((44699635186139/281474976710656), (230212159539935/562949953421312)), (134779/1125899906842624), by norm_num⟩
  | 6 => ⟨((-159891331666077/1125899906842624), (73117686460821/562949953421312)), (612161/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-87321811889/8589934592)), (1/4294967296), by norm_num⟩, -2, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-7417145753/4294967296), (-91509035727/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-537961115898079/9007199254740992), (1508688923914421/9007199254740992)), (542909/4503599627370496), by norm_num⟩
  | 1 => ⟨((18901081025/137438953472), (-26503636369/68719476736)), (5/17179869184), by norm_num⟩
  | 2 => ⟨((-21760673705/137438953472), (61026878013/137438953472)), (3/8589934592), by norm_num⟩
  | 3 => ⟨((33403868591/274877906944), (-93679719723/274877906944)), (19/68719476736), by norm_num⟩
  | 4 => ⟨((-9614406233/137438953472), (53926381537/274877906944)), (23/137438953472), by norm_num⟩
  | 5 => ⟨((2213798847/68719476736), (-99336065797/1099511627776)), (87/1099511627776), by norm_num⟩
  | 6 => ⟨((-3318659/268435456), (19060812025/549755813888)), (69/2199023255552), by norm_num⟩
  | 7 => ⟨((17885464265/4398046511104), (-100318038009/8796093022208)), (93/8796093022208), by norm_num⟩
  | 8 => ⟨((-20591401699/17592186044416), (57747704719/17592186044416)), (55/17592186044416), by norm_num⟩
  | 9 => ⟨((21072646487/70368744177664), (-59097335129/70368744177664)), (29/35184372088832), by norm_num⟩
  | 10 => ⟨((-4852156167/70368744177664), (54430657161/281474976710656)), (55/281474976710656), by norm_num⟩
  | 11 => ⟨((32501825335/2251799813685248), (-45574989011/1125899906842624)), (47/1125899906842624), by norm_num⟩
  | 12 => ⟨((-24946072837/9007199254740992), (17490048385/2251799813685248)), (37/4503599627370496), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (2492308716019/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444825139328455/158456325028528675187087900672), (2951210223959/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890339794074759/39614081257132168796771975168), (3319598667877/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890151842109657/2475880078570760549798248448), (3526451255311/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885908822726439/77371252455336267181195264), (881437805671/38685626227668133590597632)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550140724713733/9671406556917033397649408), (1652324051757/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629651048463587/302231454903657293676544), (2890823554255/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888625454054829/75557863725914323419136), (4696194424397/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298163733642041/4722366482869645213696), (1760463238905/2361183241434822606848)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811152619372353/295147905179352825856), (1209823250651/147573952589676412928)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912272066176883/36893488147419103232), (1511536453423/18446744073709551616)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455964371326743/2305843009213693952), (1699457794119/2305843009213693952)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797551362761151/576460752303423488), (6792729832837/1152921504606846976)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195554350901487/144115188075855872), (2968951333963/72057594037927936)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((23329538445669/562949953421312), (8895389822477/36028797018963968)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((745530610597831/4503599627370496), (2774798069761/2251799813685248)), (1383/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115758470216755/2251799813685248), (5534579714427/1125899906842624)), (1387/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110680958217283/1125899906842624), (4132194592497/281474976710656)), (1045/562949953421312), by norm_num⟩
  | 0 => ⟨((273858949945255/281474976710656), (32758442415763/1125899906842624)), (4221/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((273858949945255/281474976710656), (32758442415763/1125899906842624)), (16101841453170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064842859126337/1125899906842624), (31872078813759/562949953421312)), (2115/281474976710656), by norm_num⟩
  | 2 => ⟨((1003487956730629/1125899906842624), (30143670253529/281474976710656)), (16961/1125899906842624), by norm_num⟩
  | 3 => ⟨((1762945035469267/2251799813685248), (429861445227795/2251799813685248)), (33867/1125899906842624), by norm_num⟩
  | 4 => ⟨((649079531454523/1125899906842624), (673081235905913/2251799813685248)), (8245/140737488355328), by norm_num⟩
  | 5 => ⟨((273598610985695/1125899906842624), (388030277449617/1125899906842624)), (28871/281474976710656), by norm_num⟩
  | 6 => ⟨((-537961115898079/9007199254740992), (1508688923914421/9007199254740992)), (542909/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-91509035727/8589934592)), (1/4294967296), by norm_num⟩, -2, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-1931040333/1073741824), (-5956052527/536870912)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((146557041094735/9007199254740992), (1484012917531979/9007199254740992)), (226159/2251799813685248), by norm_num⟩
  | 1 => ⟨((-670296547/17179869184), (-54298516231/137438953472)), (17/68719476736), by norm_num⟩
  | 2 => ⟨((3214601843/68719476736), (65101077695/137438953472)), (21/68719476736), by norm_num⟩
  | 3 => ⟨((-10277704751/274877906944), (-104070377639/274877906944)), (69/274877906944), by norm_num⟩
  | 4 => ⟨((12322429819/549755813888), (124774933289/549755813888)), (85/549755813888), by norm_num⟩
  | 5 => ⟨((-11819158485/1099511627776), (-119678889079/1099511627776)), (21/274877906944), by norm_num⟩
  | 6 => ⟨((9447034753/2199023255552), (95659147459/2199023255552)), (35/1099511627776), by norm_num⟩
  | 7 => ⟨((-6472285707/4398046511104), (-65537319283/4398046511104)), (25/2199023255552), by norm_num⟩
  | 8 => ⟨((3879965825/8796093022208), (39287907025/8796093022208)), (31/8796093022208), by norm_num⟩
  | 9 => ⟨((-516875095/4398046511104), (-83740699141/70368744177664)), (17/17592186044416), by norm_num⟩
  | 10 => ⟨((1983059755/70368744177664), (20080142661/70368744177664)), (67/281474976710656), by norm_num⟩
  | 11 => ⟨((-6916610345/1125899906842624), (-1094319981/17592186044416)), (15/281474976710656), by norm_num⟩
  | 12 => ⟨((2764217875/2251799813685248), (55980047133/4503599627370496)), (49/4503599627370496), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (479477757903/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889596102008127/316912650057057350374175801344), (2270782607173/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890218025488141/39614081257132168796771975168), (2554223168847/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890022626518019/2475880078570760549798248448), (2713363833337/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885844306869393/77371252455336267181195264), (2712803384827/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550019952760657/9671406556917033397649408), (2542657824293/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629598308322385/302231454903657293676544), (2224230390737/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944227207167259/37778931862957161709568), (3613258679409/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298035773655739/4722366482869645213696), (1354484035983/2361183241434822606848)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622129813037583/590295810358705651712), (3723245771671/590295810358705651712)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912162814209201/36893488147419103232), (4651680223217/73786976294838206464)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823612737245445/9223372036854775808), (5229873511823/9223372036854775808)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594859311808201/1152921504606846976), (1306448130677/288230376151711744)), (419/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195342862658951/144115188075855872), (1141995172881/36028797018963968)), (367/72057594037927936), by norm_num⟩
  | 4 => ⟨((746388109860005/18014398509481984), (6842803869187/36028797018963968)), (551/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490673642042795/9007199254740992), (8537481100269/9007199254740992)), (1379/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230757394227809/4503599627370496), (17026966173079/4503599627370496)), (2763/4503599627370496), by norm_num⟩
  | 1 => ⟨((138766340038815/140737488355328), (6355180524223/562949953421312)), (65/35184372088832), by norm_num⟩
  | 0 => ⟨((136801556499873/140737488355328), (50364111150117/2251799813685248)), (8383/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((136801556499873/140737488355328), (50364111150117/2251799813685248)), (31978615767668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1063242364522881/1125899906842624), (3059725271845/70368744177664)), (16673/2251799813685248), by norm_num⟩
  | 2 => ⟨((1001943128037457/1125899906842624), (92462344492415/1125899906842624)), (32941/2251799813685248), by norm_num⟩
  | 3 => ⟨((1768080342885359/2251799813685248), (329130538526127/2251799813685248)), (8005/281474976710656), by norm_num⟩
  | 4 => ⟨((20940063485319/35184372088832), (258428494342463/1125899906842624)), (14911/281474976710656), by norm_num⟩
  | 5 => ⟨((21217729922559/70368744177664), (615217354373565/2251799813685248)), (196751/2251799813685248), by norm_num⟩
  | 6 => ⟨((146557041094735/9007199254740992), (1484012917531979/9007199254740992)), (226159/2251799813685248), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-5956052527/536870912)), (1/4294967296), by norm_num⟩, -2, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-2001111149/1073741824), (-49377417601/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((41937287912783/562949953421312), (306333083409581/2251799813685248)), (180163/2251799813685248), by norm_num⟩
  | 1 => ⟨((-12720977247/68719476736), (-46460517335/137438953472)), (29/137438953472), by norm_num⟩
  | 2 => ⟨((31610440953/137438953472), (57725024239/137438953472)), (19/68719476736), by norm_num⟩
  | 3 => ⟨((-26182998309/137438953472), (-23906882765/68719476736)), (33/137438953472), by norm_num⟩
  | 4 => ⟨((32531153305/274877906944), (59406371959/274877906944)), (43/274877906944), by norm_num⟩
  | 5 => ⟨((-32334751669/549755813888), (-59047715489/549755813888)), (45/549755813888), by norm_num⟩
  | 6 => ⟨((26782946481/1099511627776), (48909353625/1099511627776)), (39/1099511627776), by norm_num⟩
  | 7 => ⟨((-38030355321/4398046511104), (-69448673177/4398046511104)), (57/4398046511104), by norm_num⟩
  | 8 => ⟨((5906367677/2199023255552), (86286734899/17592186044416)), (37/8796093022208), by norm_num⟩
  | 9 => ⟨((-13046019837/17592186044416), (-5955957815/4398046511104)), (21/17592186044416), by norm_num⟩
  | 10 => ⟨((25934513157/140737488355328), (47359997377/140737488355328)), (11/35184372088832), by norm_num⟩
  | 11 => ⟨((-23434488801/562949953421312), (-85589216303/1125899906842624)), (41/562949953421312), by norm_num⟩
  | 12 => ⟨((38821678037/4503599627370496), (70893737581/4503599627370496)), (35/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (1393527029987/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779092864594737/633825300114114700748351602688), (1649740909755/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890106361606919/39614081257132168796771975168), (1855653822879/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889904101922103/2475880078570760549798248448), (1971257235093/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885785111064493/77371252455336267181195264), (492708882967/38685626227668133590597632)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387477275464023/2417851639229258349412352), (923605182629/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259099763256259/604462909807314587353088), (807930625881/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472074323019309/18889465931478580854784), (2624935147649/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297918163236729/4722366482869645213696), (1967967169477/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405492118556673/147573952589676412928), (2704762306853/590295810358705651712)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912062258822183/36893488147419103232), (3379164948259/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911693630262797/4611686018427387904), (949775900917/2305843009213693952)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199329349989579/144115188075855872), (474504321303/144115188075855872)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597573749201401/72057594037927936), (829520142349/36028797018963968)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((746242668090941/18014398509481984), (4970228945375/36028797018963968)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490313812598589/9007199254740992), (6200742089231/9007199254740992)), (43/281474976710656), by norm_num⟩
  | 2 => ⟨((69689031885567/140737488355328), (193209668911/70368744177664)), (1377/2251799813685248), by norm_num⟩
  | 1 => ⟨((2219226952829865/2251799813685248), (18458198609931/2251799813685248)), (4143/2251799813685248), by norm_num⟩
  | 0 => ⟨((2186867386461137/2251799813685248), (36558078748601/2251799813685248)), (8331/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2186867386461137/2251799813685248), (36558078748601/2251799813685248)), (31780251509856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2123213814917679/2251799813685248), (17751948828025/562949953421312)), (16453/2251799813685248), by norm_num⟩
  | 2 => ⟨((1999731401297477/2251799813685248), (66952990695367/1125899906842624)), (32065/2251799813685248), by norm_num⟩
  | 3 => ⟨((883958432114741/1125899906842624), (237832860790915/2251799813685248)), (30383/1125899906842624), by norm_num⟩
  | 4 => ⟨((681447247331549/1125899906842624), (373451248112567/2251799813685248)), (54127/1125899906842624), by norm_num⟩
  | 5 => ⟨((762952176487873/2251799813685248), (226030150186709/1125899906842624)), (166949/2251799813685248), by norm_num⟩
  | 6 => ⟨((41937287912783/562949953421312), (306333083409581/2251799813685248)), (180163/2251799813685248), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-49377417601/4294967296)), (1/4294967296), by norm_num⟩, -2, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-16524560409/8589934592), (-101935882025/8589934592)), (3/8589934592), by norm_num⟩
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
  | 0 => ⟨((1006693102134407/9007199254740992), (423508926232965/4503599627370496)), (829977/9007199254740992), by norm_num⟩
  | 1 => ⟨((-39399975975/137438953472), (-8287650667/34359738368)), (17/68719476736), by norm_num⟩
  | 2 => ⟨((50529471531/137438953472), (42514808507/137438953472)), (23/68719476736), by norm_num⟩
  | 3 => ⟨((-43201845179/137438953472), (-9087360897/34359738368)), (41/137438953472), by norm_num⟩
  | 4 => ⟨((55405272517/274877906944), (11654310247/68719476736)), (55/274877906944), by norm_num⟩
  | 5 => ⟨((-56844687257/549755813888), (-1494635779/17179869184)), (59/549755813888), by norm_num⟩
  | 6 => ⟨((48601248019/1099511627776), (40892427531/1099511627776)), (53/1099511627776), by norm_num⟩
  | 7 => ⟨((-35617068537/2199023255552), (-59935431841/4398046511104)), (5/274877906944), by norm_num⟩
  | 8 => ⟨((22838994265/4398046511104), (2402052303/549755813888)), (27/4398046511104), by norm_num⟩
  | 9 => ⟨((-26035939407/17592186044416), (-43812568969/35184372088832)), (1/549755813888), by norm_num⟩
  | 10 => ⟨((53424692843/140737488355328), (44950808251/140737488355328)), (17/35184372088832), by norm_num⟩
  | 11 => ⟨((-49829684211/562949953421312), (-41926016997/562949953421312)), (65/562949953421312), by norm_num⟩
  | 12 => ⟨((42603538833/2251799813685248), (17923018393/1125899906842624)), (57/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418293/10141204801825835211973625643008), (911140510241/10141204801825835211973625643008)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((889500563330903/316912650057057350374175801344), (1078555973197/633825300114114700748351602688)), (271/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890003221357097/39614081257132168796771975168), (1213170730171/39614081257132168796771975168)), (609/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889794598092583/2475880078570760549798248448), (644370476685/1237940039285380274899124224)), (81/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442865202816177/38685626227668133590597632), (1288456479249/154742504910672534362390528)), (81/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387451656974543/2417851639229258349412352), (603812890285/4835703278458516698824704)), (607/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259010197216147/604462909807314587353088), (528185242469/302231454903657293676544)), (133/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888151932158783/75557863725914323419136), (858017927127/37778931862957161709568)), (863/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162226163120915/590295810358705651712), (1286531683027/4722366482869645213696)), (81/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621819056603199/590295810358705651712), (6906940361/2305843009213693952)), (891/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823938138982897/73786976294838206464), (2209015083791/73786976294838206464)), (1113/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911589062399669/4611686018427387904), (1241742516031/4611686018427387904)), (313/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594426338606693/1152921504606846976), (310176935195/144115188075855872)), (1253/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194965852213387/144115188075855872), (1084456264543/72057594037927936)), (1097/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492214378661711/36028797018963968), (3248722321139/36028797018963968)), (1645/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489977754210517/9007199254740992), (4052784074057/9007199254740992)), (1029/4503599627370496), by norm_num⟩
  | 2 => ⟨((2229384790858541/4503599627370496), (4040630794115/2251799813685248)), (515/562949953421312), by norm_num⟩
  | 1 => ⟨((2218250228278251/2251799813685248), (12061300370039/2251799813685248)), (3095/1125899906842624), by norm_num⟩
  | 0 => ⟨((2184991826711191/2251799813685248), (11940638148651/1125899906842624)), (12425/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2184991826711191/2251799813685248), (11940638148651/1125899906842624)), (47397622115325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1059956337687211/1125899906842624), (46345499456845/2251799813685248)), (24377/2251799813685248), by norm_num⟩
  | 2 => ⟨((249349532460321/281474976710656), (10907764885229/281474976710656)), (46903/2251799813685248), by norm_num⟩
  | 3 => ⟨((1763743569068459/2251799813685248), (154605349639437/2251799813685248)), (5421/140737488355328), by norm_num⟩
  | 4 => ⟨((685426951484039/1125899906842624), (60548053497675/562949953421312)), (147785/2251799813685248), by norm_num⟩
  | 5 => ⟨((1617002846967615/4503599627370496), (147442121541999/1125899906842624)), (13233/140737488355328), by norm_num⟩
  | 6 => ⟨((1006693102134407/9007199254740992), (423508926232965/4503599627370496)), (829977/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-16524560409/8589934592), (-101935882025/8589934592)), (3/8589934592), by norm_num⟩, -2, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2125249673/1073741824), (-52440535683/4294967296)), (3/8589934592), by norm_num⟩
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
  | 0 => ⟨((1166201317802289/9007199254740992), (434449629650721/9007199254740992)), (77039/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1467548435/4294967296), (-34989547103/274877906944)), (13/68719476736), by norm_num⟩
  | 2 => ⟨((61967111263/137438953472), (11542427593/68719476736)), (37/137438953472), by norm_num⟩
  | 3 => ⟨((-54511586391/137438953472), (-20307418761/137438953472)), (35/137438953472), by norm_num⟩
  | 4 => ⟨((71929600807/274877906944), (26796221163/274877906944)), (49/274877906944), by norm_num⟩
  | 5 => ⟨((-75930536091/549755813888), (-28286705547/549755813888)), (27/274877906944), by norm_num⟩
  | 6 => ⟨((16698753151/274877906944), (24883412535/1099511627776)), (25/549755813888), by norm_num⟩
  | 7 => ⟨((-50364533599/2199023255552), (-18762500639/2199023255552)), (39/2199023255552), by norm_num⟩
  | 8 => ⟨((33228722887/4398046511104), (24757657417/8796093022208)), (27/4398046511104), by norm_num⟩
  | 9 => ⟨((-77948893057/35184372088832), (-3629826515/4398046511104)), (65/35184372088832), by norm_num⟩
  | 10 => ⟨((82284639023/140737488355328), (30653824863/140737488355328)), (71/140737488355328), by norm_num⟩
  | 11 => ⟨((-39482523587/281474976710656), (-7354291017/140737488355328)), (71/562949953421312), by norm_num⟩
  | 12 => ⟨((69464428843/2251799813685248), (25877860817/2251799813685248)), (1/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (58065043971/1267650600228229401496703205376)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1778915887717893/633825300114114700748351602688), (549822171867/633825300114114700748351602688)), (271/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118119210638885/2475880078570760549798248448), (618442859403/39614081257132168796771975168)), (609/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889692810520325/2475880078570760549798248448), (656962890891/2475880078570760549798248448)), (647/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771359084696539/154742504910672534362390528), (656813715201/154742504910672534362390528)), (647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774855662013245/4835703278458516698824704), (615604406281/9671406556917033397649408)), (607/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258926871079661/604462909807314587353088), (33655966073/37778931862957161709568)), (531/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888016648521777/75557863725914323419136), (54672389653/4722366482869645213696)), (863/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20276686692715/73786976294838206464), (655809016181/4722366482869645213696)), (81/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810839931748475/295147905179352825856), (112664457845/73786976294838206464)), (445/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823764405755817/73786976294838206464), (563006174145/36893488147419103232)), (139/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822983029490731/9223372036854775808), (1265895178763/9223372036854775808)), (1251/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594231685925107/1152921504606846976), (1264810191841/1152921504606846976)), (1251/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149349503533145/18014398509481984), (1105489549997/144115188075855872)), (1095/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491960635020549/36028797018963968), (827899345957/18014398509481984)), (821/18014398509481984), by norm_num⟩
  | 3 => ⟨((372415576656297/2251799813685248), (516373244645/2251799813685248)), (1027/4503599627370496), by norm_num⟩
  | 2 => ⟨((557189768380763/1125899906842624), (2059123818879/2251799813685248)), (4109/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217324533823859/2251799813685248), (6145622886271/2251799813685248)), (6169/2251799813685248), by norm_num⟩
  | 0 => ⟨((545797896804185/562949953421312), (12164833181629/2251799813685248)), (1545/281474976710656), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((545797896804185/562949953421312), (12164833181629/2251799813685248)), (5893708349132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2116608010339687/2251799813685248), (5897096469371/562949953421312)), (12051/1125899906842624), by norm_num⟩
  | 2 => ⟨((1989285650643523/2251799813685248), (44344409477107/2251799813685248)), (5727/281474976710656), by norm_num⟩
  | 3 => ⟨((878251021508703/1125899906842624), (78349502405101/2251799813685248)), (82755/2251799813685248), by norm_num⟩
  | 4 => ⟨((170927759868111/281474976710656), (30558014128869/562949953421312)), (134865/2251799813685248), by norm_num⟩
  | 5 => ⟨((1647484341257017/4503599627370496), (74226319683613/1125899906842624)), (356875/4503599627370496), by norm_num⟩
  | 6 => ⟨((1166201317802289/9007199254740992), (434449629650721/9007199254740992)), (77039/1125899906842624), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-52440535683/4294967296)), (3/8589934592), by norm_num⟩, -2, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-8723240287/4294967296), (-26905744261/2147483648)), (3/8589934592), by norm_num⟩
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
  | 0 => ⟨((590455819126135/4503599627370496), (44195102471241/9007199254740992)), (442211/9007199254740992), by norm_num⟩
  | 1 => ⟨((-12199279783/34359738368), (-3652421757/274877906944)), (19/137438953472), by norm_num⟩
  | 2 => ⟨((66072524139/137438953472), (4945470737/274877906944)), (27/137438953472), by norm_num⟩
  | 3 => ⟨((-119285141521/274877906944), (-4464194341/274877906944)), (51/274877906944), by norm_num⟩
  | 4 => ⟨((80757537871/274877906944), (755578899/68719476736)), (9/68719476736), by norm_num⟩
  | 5 => ⟨((-87478186669/549755813888), (-3273832943/549755813888)), (41/549755813888), by norm_num⟩
  | 6 => ⟨((9870638375/137438953472), (2955234653/1099511627776)), (39/1099511627776), by norm_num⟩
  | 7 => ⟨((-61097563969/2199023255552), (-285818707/274877906944)), (63/4398046511104), by norm_num⟩
  | 8 => ⟨((20681908799/2199023255552), (774011407/2199023255552)), (45/8796093022208), by norm_num⟩
  | 9 => ⟨((-24892287681/8796093022208), (-1863165997/17592186044416)), (7/4398046511104), by norm_num⟩
  | 10 => ⟨((3370478233/4398046511104), (2018218821/70368744177664)), (63/140737488355328), by norm_num⟩
  | 11 => ⟨((-53105013857/281474976710656), (-993715979/140737488355328)), (1/8796093022208), by norm_num⟩
  | 12 => ⟨((47937014485/1125899906842624), (897010919/562949953421312)), (15/562949953421312), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798723/10141204801825835211973625643008), (48726931841/10141204801825835211973625643008)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((889418135196897/316912650057057350374175801344), (28834969069/316912650057057350374175801344)), (271/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889817825527341/39614081257132168796771975168), (32433587289/19807040628566084398385987584)), (609/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944798850270387/1237940039285380274899124224), (68907097349/2475880078570760549798248448)), (647/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885632004932229/77371252455336267181195264), (68891043175/154742504910672534362390528)), (647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774811114349973/4835703278458516698824704), (64568300713/9671406556917033397649408)), (607/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629424474989925/302231454903657293676544), (14120054205/151115727451828646838272)), (531/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943945048327565/37778931862957161709568), (91748403169/75557863725914323419136)), (431/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162201636947107/590295810358705651712), (8597919939/590295810358705651712)), (647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621549540243639/590295810358705651712), (23632933971/147573952589676412928)), (889/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911800825248895/36893488147419103232), (29524159039/18446744073709551616)), (1111/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455700033559585/2305843009213693952), (66382618339/4611686018427387904)), (625/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594049045890703/1152921504606846976), (132648488859/1152921504606846976)), (1249/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18666195389779/2251799813685248), (14492028137/18014398509481984)), (1093/144115188075855872), by norm_num⟩
  | 4 => ⟨((745860961220537/18014398509481984), (86821139269/18014398509481984)), (205/4503599627370496), by norm_num⟩
  | 3 => ⟨((186170614413023/1125899906842624), (108297511299/4503599627370496)), (1025/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228167279928131/4503599627370496), (431819674447/4503599627370496)), (2049/2251799813685248), by norm_num⟩
  | 1 => ⟨((2216444284069067/2251799813685248), (644314431121/2251799813685248)), (1537/562949953421312), by norm_num⟩
  | 0 => ⟨((2181460659095945/2251799813685248), (637516710825/1125899906842624)), (6149/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2181460659095945/2251799813685248), (637516710825/1125899906842624)), (23456577781295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2113317956841371/2251799813685248), (617602690847/562949953421312)), (23843/2251799813685248), by norm_num⟩
  | 2 => ⟨((247918723538179/281474976710656), (2318484705129/1125899906842624)), (44807/2251799813685248), by norm_num⟩
  | 3 => ⟨((1746893688053093/2251799813685248), (8168339159033/2251799813685248)), (19779/562949953421312), by norm_num⟩
  | 4 => ⟨((338792420295233/562949953421312), (6336806687731/1125899906842624)), (1927/35184372088832), by norm_num⟩
  | 5 => ⟨((1630983565373645/4503599627370496), (15254372518423/2251799813685248)), (299661/4503599627370496), by norm_num⟩
  | 6 => ⟨((590455819126135/4503599627370496), (44195102471241/9007199254740992)), (442211/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8723240287/4294967296), (-26905744261/2147483648)), (3/8589934592), by norm_num⟩, -2, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile010Terms1
