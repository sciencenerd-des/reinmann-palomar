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
namespace Reinmann.XiRectangle.Tile020Terms1
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
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-55294967/33554432), (-5327670071/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((470066713625779/4503599627370496), (-728174182808451/4503599627370496)), (3439057/1125899906842624), by norm_num⟩
  | 1 => ⟨((-492497509/2147483648), (381460717/1073741824)), (15/2147483648), by norm_num⟩
  | 2 => ⟨((1082127631/4294967296), (-3352619451/8589934592)), (17/2147483648), by norm_num⟩
  | 3 => ⟨((-3170236569/17179869184), (4795871/16777216)), (51/8589934592), by norm_num⟩
  | 4 => ⟨((870715213/8589934592), (-1348813521/8589934592)), (29/8589934592), by norm_num⟩
  | 5 => ⟨((-1530525493/34359738368), (2370916975/34359738368)), (105/68719476736), by norm_num⟩
  | 6 => ⟨((560484705/34359738368), (-217059877/8589934592)), (79/137438953472), by norm_num⟩
  | 7 => ⟨((-1407440879/274877906944), (4360496425/549755813888)), (51/274877906944), by norm_num⟩
  | 8 => ⟨((3092463691/2199023255552), (-4790494957/2199023255552)), (115/2199023255552), by norm_num⟩
  | 9 => ⟨((-377490957/1099511627776), (4678130337/8796093022208)), (115/8796093022208), by norm_num⟩
  | 10 => ⟨((2654183707/35184372088832), (-4111561181/35184372088832)), (103/35184372088832), by norm_num⟩
  | 11 => ⟨((-2120668245/140737488355328), (1642549687/70368744177664)), (21/35184372088832), by norm_num⟩
  | 12 => ⟨((388298699/140737488355328), (-4812067389/1125899906842624)), (63/562949953421312), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-162429437773/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444856460447349/158456325028528675187087900672), (-1538897307835/633825300114114700748351602688)), (1443/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890480913229695/39614081257132168796771975168), (-1731006937131/39614081257132168796771975168)), (12989/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472575501417651/618970019642690137449562112), (-1838885555957/2475880078570760549798248448)), (6901/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885984030679991/77371252455336267181195264), (-919268829495/77371252455336267181195264)), (3451/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550282007591373/9671406556917033397649408), (-861629748333/4835703278458516698824704)), (12943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259425987237667/604462909807314587353088), (-1507482593065/604462909807314587353088)), (11327/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888827277554713/75557863725914323419136), (-2448966659715/75557863725914323419136)), (2301/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649157769964287/2361183241434822606848), (-459029801419/1180591620717411303424)), (6905/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202814335566097/73786976294838206464), (-2523679867233/590295810358705651712)), (1187/36893488147419103232), by norm_num⟩
  | 8 => ⟨((456201751648967/18446744073709551616), (-394140551843/9223372036854775808)), (23747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912077342012625/4611686018427387904), (-886309326789/2305843009213693952)), (6681/2305843009213693952), by norm_num⟩
  | 6 => ⟨((24928152387803/18014398509481984), (-221419018455/72057594037927936)), (1671/72057594037927936), by norm_num⟩
  | 5 => ⟨((1195818052931783/144115188075855872), (-1548509383557/72057594037927936)), (23407/144115188075855872), by norm_num⟩
  | 4 => ⟨((373372527463937/9007199254740992), (-2319919266143/18014398509481984)), (549/562949953421312), by norm_num⟩
  | 3 => ⟨((1491567928888957/9007199254740992), (-180932918515/281474976710656)), (43965/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116275852076803/2251799813685248), (-11549920653605/4503599627370496)), (88067/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222967119432451/2251799813685248), (-17250584083035/2251799813685248)), (132445/2251799813685248), by norm_num⟩
  | 0 => ⟨((1097146180170221/1125899906842624), (-34204989368503/2251799813685248)), (8321/70368744177664), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1097146180170221/1125899906842624), (-34204989368503/2251799813685248)), (31742096215701081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2137733981544589/2251799813685248), (-33331447316357/1125899906842624)), (263517/1125899906842624), by norm_num⟩
  | 2 => ⟨((253434086734931/281474976710656), (-126572117377747/2251799813685248)), (1031879/2251799813685248), by norm_num⟩
  | 3 => ⟨((1818378791331421/2251799813685248), (-113962844401299/1125899906842624)), (1974167/2251799813685248), by norm_num⟩
  | 4 => ⟨((1445311119295925/2251799813685248), (-184055099391789/1125899906842624)), (3588017/2251799813685248), by norm_num⟩
  | 5 => ⟨((433746175223949/1125899906842624), (-236270453614357/1125899906842624)), (5779011/2251799813685248), by norm_num⟩
  | 6 => ⟨((470066713625779/4503599627370496), (-728174182808451/4503599627370496)), (3439057/1125899906842624), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-5327670071/268435456)), (1/134217728), by norm_num⟩, -3, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-231785805/134217728), (-1395785143/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-295917159217601/4503599627370496), (-744190258354661/4503599627370496)), (17470797/4503599627370496), by norm_num⟩
  | 1 => ⟨((649809303/4294967296), (408544873/1073741824)), (79/8589934592), by norm_num⟩
  | 2 => ⟨((-748120607/4294967296), (-3762837337/8589934592)), (93/8589934592), by norm_num⟩
  | 3 => ⟨((2296815143/17179869184), (5776168773/17179869184)), (145/17179869184), by norm_num⟩
  | 4 => ⟨((-1322153077/17179869184), (-831257507/4294967296)), (43/8589934592), by norm_num⟩
  | 5 => ⟨((608873993/17179869184), (6124931661/68719476736)), (81/34359738368), by norm_num⟩
  | 6 => ⟨((-116832015/8589934592), (-4701058779/137438953472)), (127/137438953472), by norm_num⟩
  | 7 => ⟨((4803851/1073741824), (1546369695/137438953472)), (85/274877906944), by norm_num⟩
  | 8 => ⟨((-707921645/549755813888), (-27817561/8589934592)), (25/274877906944), by norm_num⟩
  | 9 => ⟨((1448933179/4398046511104), (1821932125/2199023255552)), (105/4398046511104), by norm_num⟩
  | 10 => ⟨((-1334516775/17592186044416), (-3356123001/17592186044416)), (99/17592186044416), by norm_num⟩
  | 11 => ⟨((2234791587/140737488355328), (1405047053/35184372088832)), (21/17592186044416), by norm_num⟩
  | 12 => ⟨((-1715265931/562949953421312), (-4313653865/562949953421312)), (131/562949953421312), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581726236476819/10141204801825835211973625643008), (-2539133327281/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779300380686483/633825300114114700748351602688), (-3006656513811/633825300114114700748351602688)), (11563/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118146224076473/2475880078570760549798248448), (-845491443199/9903520314283042199192993792)), (13011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890151607206337/2475880078570760549798248448), (-1796352286213/1237940039285380274899124224)), (6913/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771817395934391/154742504910672534362390528), (-448998917293/19342813113834066795298816)), (6915/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775070237634893/4835703278458516698824704), (-3366734184537/9671406556917033397649408)), (1621/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259301863152633/604462909807314587353088), (-736283711691/151115727451828646838272)), (11351/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472156261276905/18889465931478580854784), (-598052996179/9444732965739290427392)), (9225/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298163401520703/4722366482869645213696), (-1793537808699/2361183241434822606848)), (3461/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622304740822031/590295810358705651712), (-2465105329759/295147905179352825856)), (4761/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456135862032815/18446744073709551616), (-6159736763127/73786976294838206464)), (23817/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823856630660213/9223372036854775808), (-1731385954117/2305843009213693952)), (6703/2305843009213693952), by norm_num⟩
  | 6 => ⟨((12461732538377/9007199254740992), (-6920345984147/1152921504606846976)), (26835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149444173921885/18014398509481984), (-3024729114365/72057594037927936)), (11753/72057594037927936), by norm_num⟩
  | 4 => ⟨((746544391893853/18014398509481984), (-2265626491645/9007199254740992)), (17655/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491058710960251/9007199254740992), (-11307707244695/9007199254740992)), (22113/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115755340929527/2251799813685248), (-11277103838109/2251799813685248)), (44361/2251799813685248), by norm_num⟩
  | 1 => ⟨((138834340640337/140737488355328), (-16839267791307/1125899906842624)), (66877/1125899906842624), by norm_num⟩
  | 0 => ⟨((136927153451859/140737488355328), (-33373707836649/1125899906842624)), (67551/562949953421312), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((136927153451859/140737488355328), (-33373707836649/1125899906842624)), (257686617137718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1064770581198969/1125899906842624), (-32470146139519/562949953421312)), (270899/1125899906842624), by norm_num⟩
  | 2 => ⟨((501607266401251/562949953421312), (-959600631639/8796093022208)), (543633/1125899906842624), by norm_num⟩
  | 3 => ⟨((880497865601031/1125899906842624), (-437778589615257/2251799813685248)), (1087405/1125899906842624), by norm_num⟩
  | 4 => ⟨((646028979597615/1125899906842624), (-342360019233879/1125899906842624)), (1061799/562949953421312), by norm_num⟩
  | 5 => ⟨((266580588457289/1125899906842624), (-785769649811679/2251799813685248)), (7456937/2251799813685248), by norm_num⟩
  | 6 => ⟨((-295917159217601/4503599627370496), (-744190258354661/4503599627370496)), (17470797/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-231785805/134217728), (-1395785143/67108864)), (1/134217728), by norm_num⟩, -3, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-482760083/268435456), (-5814241753/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1410085918720955/9007199254740992), (-485212336676815/9007199254740992)), (32559137/9007199254740992), by norm_num⟩
  | 1 => ⟨((806150045/2147483648), (554794487/4294967296)), (77/8589934592), by norm_num⟩
  | 2 => ⟨((-966531691/2147483648), (-665169539/4294967296)), (47/4294967296), by norm_num⟩
  | 3 => ⟨((6180378061/17179869184), (1063337929/8589934592)), (153/17179869184), by norm_num⟩
  | 4 => ⟨((-1852487417/8589934592), (-1274886497/17179869184)), (47/8589934592), by norm_num⟩
  | 5 => ⟨((222103541/2147483648), (611408861/17179869184)), (23/8589934592), by norm_num⟩
  | 6 => ⟨((-5680864331/137438953472), (-1954792557/137438953472)), (149/137438953472), by norm_num⟩
  | 7 => ⟨((973008409/68719476736), (669626833/137438953472)), (13/34359738368), by norm_num⟩
  | 8 => ⟨((-4666344529/1099511627776), (-1605695017/1099511627776)), (127/1099511627776), by norm_num⟩
  | 9 => ⟨((2486534553/2199023255552), (1711239329/4398046511104)), (69/2199023255552), by norm_num⟩
  | 10 => ⟨((-596244945/2199023255552), (-1641349079/17592186044416)), (67/8796093022208), by norm_num⟩
  | 11 => ⟨((1039805771/17592186044416), (715596945/35184372088832)), (119/70368744177664), by norm_num⟩
  | 12 => ⟨((-3324460457/281474976710656), (-1143951021/281474976710656)), (97/281474976710656), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122367159/10141204801825835211973625643008), (-915144107665/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779184915897019/633825300114114700748351602688), (-4334076583311/633825300114114700748351602688)), (11579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890209409246203/39614081257132168796771975168), (-609379854985/4951760157141521099596496896)), (6515/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472503233895199/618970019642690137449562112), (-5178775370395/2475880078570760549798248448)), (1731/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771678319959525/154742504910672534362390528), (-1294425685093/38685626227668133590597632)), (13853/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550009662177841/9671406556917033397649408), (-2426478355623/4835703278458516698824704)), (203/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1259186972619007/604462909807314587353088), (-4245197583445/604462909807314587353088)), (11373/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888437544079343/75557863725914323419136), (-6896309584595/75557863725914323419136)), (18489/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81126379558595/295147905179352825856), (-2585181454187/2361183241434822606848)), (13875/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622109273094575/590295810358705651712), (-7106211696149/590295810358705651712)), (9545/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912148702042317/36893488147419103232), (-2219552288237/18446744073709551616)), (23881/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227947185493819/1152921504606846976), (-623857645287/576460752303423488)), (6723/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797409844564591/576460752303423488), (-2493473701897/288230376151711744)), (26925/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597651643276933/72057594037927936), (-2179588414503/36028797018963968)), (5899/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492707066263413/36028797018963968), (-13059926064527/36028797018963968)), (35467/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490570121151999/9007199254740992), (-1018381832263/562949953421312)), (44463/9007199254740992), by norm_num⟩
  | 2 => ⟨((557624830951531/1125899906842624), (-16247931073065/2251799813685248)), (44657/2251799813685248), by norm_num⟩
  | 1 => ⟨((138734218268103/140737488355328), (-24256518953115/1125899906842624)), (67471/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093647000586591/1125899906842624), (-24025971136695/562949953421312)), (68445/562949953421312), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1093647000586591/1125899906842624), (-24025971136695/562949953421312)), (261096956493186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1060267227557967/1125899906842624), (-46675430222767/562949953421312)), (277623/1125899906842624), by norm_num⟩
  | 2 => ⟨((990720581739467/1125899906842624), (-87909109320649/562949953421312)), (142229/281474976710656), by norm_num⟩
  | 3 => ⟨((422157964175435/562949953421312), (-77354446338475/281474976710656)), (1178903/1125899906842624), by norm_num⟩
  | 4 => ⟨((1096243133555815/2251799813685248), (-58008345835547/140737488355328)), (4832189/2251799813685248), by norm_num⟩
  | 5 => ⟨((302262350353207/4503599627370496), (-1807372052870433/4503599627370496)), (8688313/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1410085918720955/9007199254740992), (-485212336676815/9007199254740992)), (32559137/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-482760083/268435456), (-5814241753/268435456)), (1/134217728), by norm_num⟩, -3, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-500277787/268435456), (-753152575/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-627584971883859/4503599627370496), (153342792020009/2251799813685248)), (31104717/9007199254740992), by norm_num⟩
  | 1 => ⟨((2974491253/8589934592), (-1453561873/8589934592)), (19/2147483648), by norm_num⟩
  | 2 => ⟨((-3695666547/8589934592), (902991391/4294967296)), (3/268435456), by norm_num⟩
  | 3 => ⟨((3061128793/8589934592), (-1495899541/8589934592)), (41/4294967296), by norm_num⟩
  | 4 => ⟨((-3803309647/17179869184), (929292679/8589934592)), (13/2147483648), by norm_num⟩
  | 5 => ⟨((3780347773/34359738368), (-923682223/17179869184)), (105/34359738368), by norm_num⟩
  | 6 => ⟨((-391408805/8589934592), (1530176065/68719476736)), (89/68719476736), by norm_num⟩
  | 7 => ⟨((4446236993/274877906944), (-543192097/68719476736)), (1/2147483648), by norm_num⟩
  | 8 => ⟨((-5524241935/1099511627776), (674890827/274877906944)), (161/1099511627776), by norm_num⟩
  | 9 => ⟨((95327955/68719476736), (-2911529/4294967296)), (91/2199023255552), by norm_num⟩
  | 10 => ⟨((-3032077687/8796093022208), (185212871/1099511627776)), (23/2199023255552), by norm_num⟩
  | 11 => ⟨((5479585459/70368744177664), (-2677740769/70368744177664)), (169/70368744177664), by norm_num⟩
  | 12 => ⟨((-2269376391/140737488355328), (1108989307/140737488355328)), (143/281474976710656), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115842083/10141204801825835211973625643008), (875044154877/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779085135743049/633825300114114700748351602688), (32372805413/4951760157141521099596496896)), (11577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890097225794987/39614081257132168796771975168), (2330449184987/19807040628566084398385987584)), (13027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889893826679097/2475880078570760549798248448), (4951260349653/2475880078570760549798248448)), (13845/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771559307803593/154742504910672534362390528), (154693692431/4835703278458516698824704)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549898191040423/9671406556917033397649408), (4639682295659/9671406556917033397649408)), (3247/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259089538094807/604462909807314587353088), (2029296822709/302231454903657293676544)), (11369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888279405499271/75557863725914323419136), (6593099235183/75557863725914323419136)), (18483/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162237954672347/590295810358705651712), (4942973660481/4722366482869645213696)), (6935/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621946697662331/590295810358705651712), (6793581744717/590295810358705651712)), (4771/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824094594722427/73786976294838206464), (8487467422989/73786976294838206464)), (373/1152921504606846976), by norm_num⟩
  | 7 => ⟨((455837471660225/2305843009213693952), (4771100618063/4611686018427387904)), (26881/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594592795205245/1152921504606846976), (9534453676147/1152921504606846976)), (841/36028797018963968), by norm_num⟩
  | 5 => ⟨((1195105544794883/144115188075855872), (1041741707799/18014398509481984)), (737/4503599627370496), by norm_num⟩
  | 4 => ⟨((1492412032260935/36028797018963968), (6241740330285/18014398509481984)), (35445/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490204086278013/9007199254740992), (15573881427469/9007199254740992)), (44429/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114887753493097/2251799813685248), (15528208110613/2251799813685248)), (44615/2251799813685248), by norm_num⟩
  | 1 => ⟨((277335291177051/281474976710656), (11589118664737/562949953421312)), (33693/562949953421312), by norm_num⟩
  | 0 => ⟨((546311376059009/562949953421312), (45900831813195/1125899906842624)), (136635/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((546311376059009/562949953421312), (45900831813195/1125899906842624)), (521221165183639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((264614461916681/281474976710656), (89088369002325/1125899906842624)), (276335/1125899906842624), by norm_num⟩
  | 2 => ⟨((988006368092957/1125899906842624), (20937980972655/140737488355328)), (17603/35184372088832), by norm_num⟩
  | 3 => ⟨((210520277737095/281474976710656), (293977941168923/1125899906842624)), (1156221/1125899906842624), by norm_num⟩
  | 4 => ⟨((1106097555809063/2251799813685248), (219871473289363/562949953421312)), (583327/281474976710656), by norm_num⟩
  | 5 => ⟨((399641534713011/4503599627370496), (1728034953867323/4503599627370496)), (4114911/1125899906842624), by norm_num⟩
  | 6 => ⟨((-627584971883859/4503599627370496), (153342792020009/2251799813685248)), (31104717/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-500277787/268435456), (-753152575/33554432)), (1/134217728), by norm_num⟩, -4, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-516392513/268435456), (-3109651163/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-126030841619833/2251799813685248), (151900968604421/1125899906842624)), (14428763/4503599627370496), by norm_num⟩
  | 1 => ⟨((616574719/4294967296), (-2972551665/8589934592)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((-1581482929/8589934592), (1906111121/4294967296)), (95/8589934592), by norm_num⟩
  | 3 => ⟨((169017651/1073741824), (-3259385663/8589934592)), (83/8589934592), by norm_num⟩
  | 4 => ⟨((-1734086861/17179869184), (4180079581/17179869184)), (27/4294967296), by norm_num⟩
  | 5 => ⟨((222392249/4294967296), (-2144338487/17179869184)), (113/34359738368), by norm_num⟩
  | 6 => ⟨((-760566475/34359738368), (229171651/4294967296)), (49/34359738368), by norm_num⟩
  | 7 => ⟨((557375569/68719476736), (-5374296493/274877906944)), (73/137438953472), by norm_num⟩
  | 8 => ⟨((-357410027/137438953472), (107693737/17179869184)), (3/17179869184), by norm_num⟩
  | 9 => ⟨((1629757545/2199023255552), (-3928589959/2199023255552)), (111/2199023255552), by norm_num⟩
  | 10 => ⟨((-1672098227/8796093022208), (1007663429/2199023255552)), (29/2199023255552), by norm_num⟩
  | 11 => ⟨((1559580827/35184372088832), (-3759426421/35184372088832)), (111/35184372088832), by norm_num⟩
  | 12 => ⟨((-83338455/8796093022208), (200890383/8796093022208)), (97/140737488355328), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917417231/10141204801825835211973625643008), (2558374365739/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778996842072237/633825300114114700748351602688), (3028457107135/633825300114114700748351602688)), (11563/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944999078777233/19807040628566084398385987584), (1703215571489/19807040628566084398385987584)), (13011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944894451375479/1237940039285380274899124224), (3618621877567/2475880078570760549798248448)), (13827/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771454761747513/154742504910672534362390528), (3617821899497/154742504910672534362390528)), (6915/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387450145096619/2417851639229258349412352), (847714554561/2417851639229258349412352)), (12969/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157375566225511/75557863725914323419136), (370768914123/75557863725914323419136)), (11351/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236017752305807/9444732965739290427392), (1204600805831/18889465931478580854784)), (18451/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648900627033513/2361183241434822606848), (1806204615975/2361183241434822606848)), (3461/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202725873404213/73786976294838206464), (2482399751407/295147905179352825856)), (4761/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823921554937797/73786976294838206464), (6202605878813/73786976294838206464)), (11909/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911578705869635/4611686018427387904), (3486633821485/4611686018427387904)), (13407/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594403059766801/1152921504606846976), (6967440816823/1152921504606846976)), (6709/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194942602538541/144115188075855872), (6089959849179/144115188075855872)), (5877/36028797018963968), by norm_num⟩
  | 4 => ⟨((373043439320303/9007199254740992), (4560924413971/18014398509481984)), (2207/2251799813685248), by norm_num⟩
  | 3 => ⟨((1489916953063819/9007199254740992), (5689713074041/4503599627370496)), (44231/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114616622715515/2251799813685248), (11345147358175/2251799813685248)), (22183/1125899906842624), by norm_num⟩
  | 1 => ⟨((554487126641505/562949953421312), (16932193969441/1125899906842624)), (8361/140737488355328), by norm_num⟩
  | 0 => ⟨((1092046742551169/1125899906842624), (33523299226903/1125899906842624)), (270273/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1092046742551169/1125899906842624), (33523299226903/1125899906842624)), (1031009682662200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((529106659075379/562949953421312), (130061329600677/2251799813685248)), (540389/2251799813685248), by norm_num⟩
  | 2 => ⟨((495419900369171/562949953421312), (244484665685419/2251799813685248)), (1078229/2251799813685248), by norm_num⟩
  | 3 => ⟨((858708946428139/1125899906842624), (107578451671895/562949953421312)), (2131909/2251799813685248), by norm_num⟩
  | 4 => ⟨((613809946531805/1125899906842624), (328194640863243/1125899906842624)), (1016691/562949953421312), by norm_num⟩
  | 5 => ⟨((29870653525113/140737488355328), (357845548677979/1125899906842624)), (850633/281474976710656), by norm_num⟩
  | 6 => ⟨((-126030841619833/2251799813685248), (151900968604421/1125899906842624)), (14428763/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516392513/268435456), (-3109651163/134217728)), (1/134217728), by norm_num⟩, -4, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-265656209/134217728), (-6398993937/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((339334551714437/9007199254740992), (149667551345321/1125899906842624)), (5676497/2251799813685248), by norm_num⟩
  | 1 => ⟨((-854037605/8589934592), (-23542717/67108864)), (117/17179869184), by norm_num⟩
  | 2 => ⟨((1126927101/8589934592), (3976357111/8589934592)), (5/536870912), by norm_num⟩
  | 3 => ⟨((-495670871/4294967296), (-3497944793/8589934592)), (9/1073741824), by norm_num⟩
  | 4 => ⟨((1308103845/17179869184), (2307819211/8589934592)), (97/17179869184), by norm_num⟩
  | 5 => ⟨((-43152013/1073741824), (-4872373763/34359738368)), (13/4294967296), by norm_num⟩
  | 6 => ⟨((607363393/34359738368), (4286157897/68719476736)), (93/68719476736), by norm_num⟩
  | 7 => ⟨((-1831847787/274877906944), (-3231833261/137438953472)), (143/274877906944), by norm_num⟩
  | 8 => ⟨((151073479/68719476736), (4264496627/549755813888)), (3/17179869184), by norm_num⟩
  | 9 => ⟨((-708785017/1099511627776), (-5001889369/2199023255552)), (115/2199023255552), by norm_num⟩
  | 10 => ⟨((1496419435/8796093022208), (82501705/137438953472)), (123/8796093022208), by norm_num⟩
  | 11 => ⟨((-1436049701/35184372088832), (-2533547395/17592186044416)), (15/4398046511104), by norm_num⟩
  | 12 => ⟨((78954531/8796093022208), (4457451215/140737488355328)), (27/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197674689623573/1267650600228229401496703205376), (1686401678197/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444728479347547/158456325028528675187087900672), (124755168129/39614081257132168796771975168)), (11551/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889905041883287/39614081257132168796771975168), (2245201776085/39614081257132168796771975168)), (3249/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944845095906149/1237940039285380274899124224), (1192522515243/1237940039285380274899124224)), (6905/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771356303162141/154742504910672534362390528), (1192251547285/77371252455336267181195264)), (3453/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549708543439925/9671406556917033397649408), (279361999241/1208925819614629174706176)), (12951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629462132643233/302231454903657293676544), (977479252913/302231454903657293676544)), (11335/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888012090396287/75557863725914323419136), (3175728888039/75557863725914323419136)), (9211/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648852123371369/2361183241434822606848), (595213293793/1180591620717411303424)), (3455/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621674314409049/590295810358705651712), (3272140613449/590295810358705651712)), (297/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1823756781116923/73786976294838206464), (2043939092817/36893488147419103232)), (23769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56967922085055/288230376151711744), (2297852844535/4611686018427387904)), (209/72057594037927936), by norm_num⟩
  | 6 => ⟨((1594220983841321/1152921504606846976), (1147940489217/288230376151711744)), (13383/576460752303423488), by norm_num⟩
  | 5 => ⟨((597392669978149/72057594037927936), (1003339734177/36028797018963968)), (11719/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491941961434507/36028797018963968), (3005591327255/18014398509481984)), (17595/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489634358057233/9007199254740992), (1874625696403/2251799813685248)), (44047/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228689418001911/4503599627370496), (3737666748983/1125899906842624)), (5517/281474976710656), by norm_num⟩
  | 1 => ⟨((1108592934359415/1125899906842624), (22310461677317/2251799813685248)), (16607/281474976710656), by norm_num⟩
  | 0 => ⟨((545694702323815/562949953421312), (11040152542467/562949953421312)), (267509/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((545694702323815/562949953421312), (11040152542467/562949953421312)), (1020465859420012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1057503678140805/1125899906842624), (85614043929227/2251799813685248)), (66139/281474976710656), by norm_num⟩
  | 2 => ⟨((1983269705177997/2251799813685248), (80413157337903/1125899906842624)), (517087/1125899906842624), by norm_num⟩
  | 3 => ⟨((867637877096565/1125899906842624), (141647563763647/1125899906842624)), (492355/562949953421312), by norm_num⟩
  | 4 => ⟨((1301592528783959/2251799813685248), (436624217740413/2251799813685248)), (1765439/1125899906842624), by norm_num⟩
  | 5 => ⟨((667689194364127/2251799813685248), (504757853023341/2251799813685248)), (5451135/2251799813685248), by norm_num⟩
  | 6 => ⟨((339334551714437/9007199254740992), (149667551345321/1125899906842624)), (5676497/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-265656209/134217728), (-6398993937/268435456)), (1/134217728), by norm_num⟩, -4, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-272601259/134217728), (-3283141413/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((462610327261087/4503599627370496), (367584087059479/4503599627370496)), (244493/140737488355328), by norm_num⟩
  | 1 => ⟨((-1194736471/4294967296), (-3797287601/17179869184)), (83/17179869184), by norm_num⟩
  | 2 => ⟨((3235406341/8589934592), (2570811363/8589934592)), (29/4294967296), by norm_num⟩
  | 3 => ⟨((-1460273799/4294967296), (-2320628743/8589934592)), (27/4294967296), by norm_num⟩
  | 4 => ⟨((3954494755/17179869184), (3142189567/17179869184)), (75/17179869184), by norm_num⟩
  | 5 => ⟨((-4283588127/34359738368), (-850920709/8589934592)), (21/8589934592), by norm_num⟩
  | 6 => ⟨((483340487/8589934592), (768111999/17179869184)), (39/34359738368), by norm_num⟩
  | 7 => ⟨((-1495897489/68719476736), (-2377240975/137438953472)), (63/137438953472), by norm_num⟩
  | 8 => ⟨((506370687/68719476736), (1609421975/274877906944)), (87/549755813888), by norm_num⟩
  | 9 => ⟨((-1218913103/549755813888), (-484266167/274877906944)), (27/549755813888), by norm_num⟩
  | 10 => ⟨((2640702299/4398046511104), (1049133673/2199023255552)), (15/1099511627776), by norm_num⟩
  | 11 => ⟨((-2600419779/17592186044416), (-2066259385/17592186044416)), (61/17592186044416), by norm_num⟩
  | 12 => ⟨((4694711537/140737488355328), (3730356095/140737488355328)), (113/140737488355328), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (874614520601/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778835698693217/633825300114114700748351602688), (517567630375/316912650057057350374175801344)), (11539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889817150034719/39614081257132168796771975168), (1164320271903/39614081257132168796771975168)), (6491/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472399235202741/618970019642690137449562112), (1236834007207/2475880078570760549798248448)), (6897/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221407900362803/19342813113834066795298816), (1236545790859/154742504910672534362390528)), (13795/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549621422020017/9671406556917033397649408), (579477770361/4835703278458516698824704)), (6467/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258848194017027/604462909807314587353088), (1013780063057/604462909807314587353088)), (5659/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887888774319131/75557863725914323419136), (1646819005781/75557863725914323419136)), (9197/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324403005435017/1180591620717411303424), (1234612576217/4722366482869645213696)), (6899/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50673372827187/18446744073709551616), (424194368937/147573952589676412928)), (9487/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455899859663223/18446744073709551616), (1059875168821/36893488147419103232)), (23723/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822797371821109/9223372036854775808), (2383040723311/9223372036854775808)), (13347/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594045941452923/1152921504606846976), (1190472231149/576460752303423488)), (13351/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194633404605417/144115188075855872), (260121313885/18014398509481984)), (23373/144115188075855872), by norm_num⟩
  | 4 => ⟨((372929126512881/9007199254740992), (779187493471/9007199254740992)), (35077/36028797018963968), by norm_num⟩
  | 3 => ⟨((372339202275095/2251799813685248), (1943857899641/4503599627370496)), (10969/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114073539303607/2251799813685248), (30276642123/17592186044416)), (43923/2251799813685248), by norm_num⟩
  | 1 => ⟨((554101018355425/562949953421312), (1445611300673/281474976710656)), (66001/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090670491569977/1125899906842624), (5721386047849/562949953421312)), (16559/140737488355328), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1090670491569977/1125899906842624), (5721386047849/562949953421312)), (63167572558355287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2112854218957703/2251799813685248), (11084727683775/562949953421312)), (259347/1125899906842624), by norm_num⟩
  | 2 => ⟨((1981609104167865/2251799813685248), (2600188248343/70368744177664)), (248451/562949953421312), by norm_num⟩
  | 3 => ⟨((1740763710644757/2251799813685248), (146444469506457/2251799813685248)), (1822563/2251799813685248), by norm_num⟩
  | 4 => ⟨((1336181082955379/2251799813685248), (113209538695297/1125899906842624)), (763735/562949953421312), by norm_num⟩
  | 5 => ⟨((96262680484649/281474976710656), (537413470222109/4503599627370496)), (4239853/2251799813685248), by norm_num⟩
  | 6 => ⟨((462610327261087/4503599627370496), (367584087059479/4503599627370496)), (244493/140737488355328), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-3283141413/134217728)), (1/134217728), by norm_num⟩, -4, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile020Terms1
