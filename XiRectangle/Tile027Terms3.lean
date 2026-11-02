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
namespace Reinmann.XiRectangle.Tile027Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨27,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7473/640))
  have he : value ((5/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-259295435/134217728), (-1211071739/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23199480929977/4503599627370496), (652034949617729/4503599627370496)), (52899305/9007199254740992), by norm_num⟩
  | 1 => ⟨((273554155/17179869184), (-1922099791/4294967296)), (157/8589934592), by norm_num⟩
  | 2 => ⟨((-211391877/8589934592), (2970646027/4294967296)), (245/8589934592), by norm_num⟩
  | 3 => ⟨((217807089/8589934592), (-3060797661/4294967296)), (255/8589934592), by norm_num⟩
  | 4 => ⟨((-42078185/2147483648), (1182631939/2147483648)), (199/8589934592), by norm_num⟩
  | 5 => ⟨((104052365/8589934592), (-365556553/1073741824)), (31/2147483648), by norm_num⟩
  | 6 => ⟨((-214420185/34359738368), (6026404397/34359738368)), (257/34359738368), by norm_num⟩
  | 7 => ⟨((11835391/4294967296), (-5322249095/68719476736)), (229/68719476736), by norm_num⟩
  | 8 => ⟨((-2286481/2147483648), (4112824475/137438953472)), (89/68719476736), by norm_num⟩
  | 9 => ⟨((201034235/549755813888), (-5650184469/549755813888)), (247/549755813888), by norm_num⟩
  | 10 => ⟨((-124281071/1099511627776), (6985984025/2199023255552)), (307/2199023255552), by norm_num⟩
  | 11 => ⟨((279387685/8796093022208), (-7852353891/8796093022208)), (347/8796093022208), by norm_num⟩
  | 12 => ⟨((-143933199/17592186044416), (8090653079/35184372088832)), (45/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790729624827833/5070602400912917605986812821504), (1046232565199/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778985838764813/633825300114114700748351602688), (2476906958361/633825300114114700748351602688)), (2889/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944992936842359/19807040628566084398385987584), (2786044060811/39614081257132168796771975168)), (26005/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944887986781823/1237940039285380274899124224), (2959587961005/2475880078570760549798248448)), (13817/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885720985096557/77371252455336267181195264), (2958931276251/154742504910672534362390528)), (3455/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((96861795903407/604462909807314587353088), (1386650251537/4835703278458516698824704)), (25917/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629497155334329/302231454903657293676544), (2425940550749/604462909807314587353088)), (22683/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236015710750283/9444732965739290427392), (3940846170019/75557863725914323419136)), (18435/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297789243976183/4722366482869645213696), (2954491185869/4722366482869645213696)), (13831/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621790861748569/590295810358705651712), (4060568000597/590295810358705651712)), (38049/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455975495000813/18446744073709551616), (5072925177721/73786976294838206464)), (23791/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455784047251051/2305843009213693952), (2851606859499/4611686018427387904)), (6695/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594382834251501/1152921504606846976), (5698432874201/1152921504606846976)), (53597/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194926024869003/144115188075855872), (4980754489713/144115188075855872)), (11735/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492151124556287/36028797018963968), (7460393617429/36028797018963968)), (70493/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489892558839207/9007199254740992), (2326680944709/2251799813685248)), (11033/1125899906842624), by norm_num⟩
  | 2 => ⟨((2229196097384879/4503599627370496), (18557236612669/4503599627370496)), (88485/2251799813685248), by norm_num⟩
  | 1 => ⟨((34655026752415/35184372088832), (865489234689/70368744177664)), (133283/1125899906842624), by norm_num⟩
  | 0 => ⟨((273019321246713/281474976710656), (13708119695503/562949953421312)), (537587/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((273019321246713/281474976710656), (13708119695503/562949953421312)), (2050731667525481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2117206225807971/2251799813685248), (53185282451337/1125899906842624)), (1069057/2251799813685248), by norm_num⟩
  | 2 => ⟨((992816385885735/1125899906842624), (12501578786331/140737488355328)), (2111317/2251799813685248), by norm_num⟩
  | 3 => ⟨((866579563543687/1125899906842624), (88190946232991/562949953421312)), (1024651/562949953421312), by norm_num⟩
  | 4 => ⟨((159838712923507/281474976710656), (543028531972497/2251799813685248)), (7593369/2251799813685248), by norm_num⟩
  | 5 => ⟨((297588291565135/1125899906842624), (616729647839701/2251799813685248)), (12286289/2251799813685248), by norm_num⟩
  | 6 => ⟨((-23199480929977/4503599627370496), (652034949617729/4503599627370496)), (52899305/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-259295435/134217728), (-1211071739/33554432)), (1/67108864), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-263024319/134217728), (-4913951833/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((589975335134467/9007199254740992), (1123676092414981/9007199254740992)), (42308235/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1764168025/8589934592), (-3360061539/8589934592)), (1/67108864), by norm_num⟩
  | 2 => ⟨((2765769319/8589934592), (658465845/1073741824)), (203/8589934592), by norm_num⟩
  | 3 => ⟨((-2890684567/8589934592), (-2752821131/4294967296)), (215/8589934592), by norm_num⟩
  | 4 => ⟨((2265931185/8589934592), (4315727367/8589934592)), (85/4294967296), by norm_num⟩
  | 5 => ⟨((-1420962825/8589934592), (-5412775279/17179869184)), (27/2147483648), by norm_num⟩
  | 6 => ⟨((92821265/1073741824), (1414310465/8589934592)), (115/17179869184), by norm_num⟩
  | 7 => ⟨((-665235519/17179869184), (-1267017795/17179869184)), (13/4294967296), by norm_num⟩
  | 8 => ⟨((1042921061/68719476736), (496590871/17179869184)), (165/137438953472), by norm_num⟩
  | 9 => ⟨((-2906731515/549755813888), (-1384051381/137438953472)), (29/68719476736), by norm_num⟩
  | 10 => ⟨((911403985/549755813888), (216984255/68719476736)), (37/274877906944), by norm_num⟩
  | 11 => ⟨((-2078328671/4398046511104), (-123700523/137438953472)), (171/4398046511104), by norm_num⟩
  | 12 => ⟨((1086097921/8796093022208), (4137197593/17592186044416)), (181/17592186044416), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581423060041861/10141204801825835211973625643008), (1416352654285/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222368097459693/79228162514264337593543950336), (209562209553/79228162514264337593543950336)), (5773/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889939791630549/39614081257132168796771975168), (1885735032247/39614081257132168796771975168)), (25981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59053973510305/77371252455336267181195264), (500798210651/618970019642690137449562112)), (3451/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771393307415989/154742504910672534362390528), (2002742269707/154742504910672534362390528)), (6903/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549743281366165/9671406556917033397649408), (234636534129/1208925819614629174706176)), (12945/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314738676843641/151115727451828646838272), (820988639537/302231454903657293676544)), (22657/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888061645718743/75557863725914323419136), (1333658137163/37778931862957161709568)), (4603/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648870744611057/2361183241434822606848), (999851404999/2361183241434822606848)), (3453/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621725646156283/590295810358705651712), (687079324437/147573952589676412928)), (37993/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823821130560417/73786976294838206464), (1716743266319/36893488147419103232)), (47505/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823046153487827/9223372036854775808), (3860047615597/9223372036854775808)), (6683/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594293947057557/1152921504606846976), (3856769156339/1152921504606846976)), (53489/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74678096121849/9007199254740992), (1685494061071/72057594037927936)), (2927/9007199254740992), by norm_num⟩
  | 4 => ⟨((93252435419839/2251799813685248), (2524560419587/18014398509481984)), (2197/1125899906842624), by norm_num⟩
  | 3 => ⟨((93109803095991/562949953421312), (6298537656303/9007199254740992)), (21995/2251799813685248), by norm_num⟩
  | 2 => ⟨((2228938087077395/4503599627370496), (6279280436289/2251799813685248)), (176259/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217568023053347/2251799813685248), (9370909921827/1125899906842624)), (265141/2251799813685248), by norm_num⟩
  | 0 => ⟨((2183579334993043/2251799813685248), (37101138055913/2251799813685248)), (266653/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2183579334993043/2251799813685248), (37101138055913/2251799813685248)), (1017200474265670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058407188062297/1125899906842624), (35977122775861/1125899906842624)), (1051873/2251799813685248), by norm_num⟩
  | 2 => ⟨((993810742481135/1125899906842624), (67640906834347/1125899906842624)), (511215/562949953421312), by norm_num⟩
  | 3 => ⟨((1746308874561343/2251799813685248), (59705360516151/562949953421312)), (3855619/2251799813685248), by norm_num⟩
  | 4 => ⟨((1328963163596825/2251799813685248), (185210071152111/1125899906842624)), (1699509/562949953421312), by norm_num⟩
  | 5 => ⟨((1412873297847/4398046511104), (109306946644373/562949953421312)), (5130327/1125899906842624), by norm_num⟩
  | 6 => ⟨((589975335134467/9007199254740992), (1123676092414981/9007199254740992)), (42308235/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-263024319/134217728), (-4913951833/134217728)), (1/67108864), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-133297239/67108864), (-1245162833/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((256661553181231/2251799813685248), (171985897005079/2251799813685248)), (15499363/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1555794205/4294967296), (-2085038905/8589934592)), (95/8589934592), by norm_num⟩
  | 2 => ⟨((1236099433/2147483648), (3313182939/8589934592)), (153/8589934592), by norm_num⟩
  | 3 => ⟨((-2618927025/4294967296), (-54841009/134217728)), (83/4294967296), by norm_num⟩
  | 4 => ⟨((1040386383/2147483648), (2788602859/8589934592)), (67/4294967296), by norm_num⟩
  | 5 => ⟨((-330640393/1073741824), (-1772465999/8589934592)), (87/8589934592), by norm_num⟩
  | 6 => ⟨((700528645/4294967296), (1877664119/17179869184)), (47/8589934592), by norm_num⟩
  | 7 => ⟨((-5088726271/68719476736), (-3409895797/68719476736)), (173/68719476736), by norm_num⟩
  | 8 => ⟨((15793209/536870912), (677302025/34359738368)), (35/34359738368), by norm_num⟩
  | 9 => ⟨((-713837061/68719476736), (-1913335373/274877906944)), (25/68719476736), by norm_num⟩
  | 10 => ⟨((3629780169/1099511627776), (608068281/274877906944)), (129/1099511627776), by norm_num⟩
  | 11 => ⟨((-4194777007/4398046511104), (-2810870879/4398046511104)), (151/4398046511104), by norm_num⟩
  | 12 => ⟨((2221871189/8796093022208), (1488849827/8796093022208)), (81/8796093022208), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395347102722001/2535301200456458802993406410752), (769019803551/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889452413947255/316912650057057350374175801344), (455113817481/316912650057057350374175801344)), (23073/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472473728516187/9903520314283042199192993792), (1023828052793/39614081257132168796771975168)), (25959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944839778878597/1237940039285380274899124224), (1087596915863/2475880078570760549798248448)), (27583/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771345811593205/154742504910672534362390528), (1087349061907/154742504910672534362390528)), (431/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1549698858894775/9671406556917033397649408), (1019126478353/9671406556917033397649408)), (25863/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629457971253987/302231454903657293676544), (891472488737/604462909807314587353088)), (2829/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887998849161363/75557863725914323419136), (1448149517605/75557863725914323419136)), (9195/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297694563469705/4722366482869645213696), (1085680706681/4722366482869645213696)), (6897/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621661401938517/590295810358705651712), (1492110243095/590295810358705651712)), (37939/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823741242862795/73786976294838206464), (1864087319005/73786976294838206464)), (5929/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911478426620599/4611686018427387904), (2095654804597/9223372036854775808)), (13343/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398551340612711/288230376151711744), (261731499749/144115188075855872)), (26693/576460752303423488), by norm_num⟩
  | 5 => ⟨((597386414983269/72057594037927936), (14297612297/1125899906842624)), (5841/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491925507976717/36028797018963968), (2741094390201/36028797018963968)), (70123/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489617823096383/9007199254740992), (1709648424343/4503599627370496)), (21927/2251799813685248), by norm_num⟩
  | 2 => ⟨((2228668390547147/4503599627370496), (6817425845853/4503599627370496)), (175579/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217184248355937/2251799813685248), (2543344572023/562949953421312)), (263781/2251799813685248), by norm_num⟩
  | 0 => ⟨((1091447072122623/1125899906842624), (20136666893317/2251799813685248)), (264609/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1091447072122623/1125899906842624), (20136666893317/2251799813685248)), (1009403233054732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2115916934831313/2251799813685248), (19520479564345/1125899906842624)), (1035513/2251799813685248), by norm_num⟩
  | 2 => ⟨((993778454775607/1125899906842624), (73370133588615/2251799813685248)), (1981959/2251799813685248), by norm_num⟩
  | 3 => ⟨((1751931618533025/2251799813685248), (129520675046233/2251799813685248)), (3627919/2251799813685248), by norm_num⟩
  | 4 => ⟨((338894333790231/562949953421312), (201537778347959/2251799813685248)), (6062491/2251799813685248), by norm_num⟩
  | 5 => ⟨((798016069003787/2251799813685248), (485300767584781/4503599627370496)), (16768803/4503599627370496), by norm_num⟩
  | 6 => ⟨((256661553181231/2251799813685248), (171985897005079/2251799813685248)), (15499363/4503599627370496), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-133297239/67108864), (-1245162833/33554432)), (1/67108864), by norm_num⟩, -6, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-270018875/134217728), (-5044627631/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1196915885674079/9007199254740992), (17085928753347/1125899906842624)), (10336201/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1837121777/4294967296), (-52449687/1073741824)), (129/17179869184), by norm_num⟩
  | 2 => ⟨((5913466875/8589934592), (337658059/4294967296)), (53/4294967296), by norm_num⟩
  | 3 => ⟨((-6344905189/8589934592), (-362293121/4294967296)), (29/2147483648), by norm_num⟩
  | 4 => ⟨((5105865481/8589934592), (145772071/2147483648)), (95/8589934592), by norm_num⟩
  | 5 => ⟨((-6574058785/17179869184), (-93844439/2147483648)), (31/4294967296), by norm_num⟩
  | 6 => ⟨((7053692965/34359738368), (805529589/34359738368)), (135/34359738368), by norm_num⟩
  | 7 => ⟨((-1621782983/17179869184), (-185207123/17179869184)), (63/34359738368), by norm_num⟩
  | 8 => ⟨((5220318037/137438953472), (596158731/137438953472)), (103/137438953472), by norm_num⟩
  | 9 => ⟨((-7468246901/549755813888), (-852871523/549755813888)), (149/549755813888), by norm_num⟩
  | 10 => ⟨((4807871881/1099511627776), (549057505/1099511627776)), (49/549755813888), by norm_num⟩
  | 11 => ⟨((-5627615479/4398046511104), (-321335987/2199023255552)), (29/1099511627776), by norm_num⟩
  | 12 => ⟨((754774809/2199023255552), (689560427/17592186044416)), (127/17592186044416), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581355176385417/10141204801825835211973625643008), (148116189101/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444716479649813/158456325028528675187087900672), (87652991417/316912650057057350374175801344)), (23055/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889851173036809/39614081257132168796771975168), (98592284745/19807040628566084398385987584)), (12969/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472408280970859/618970019642690137449562112), (52366405017/618970019642690137449562112)), (27559/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771299423776711/154742504910672534362390528), (209417279519/154742504910672534362390528)), (27559/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774827709613183/4835703278458516698824704), (196277353497/9671406556917033397649408)), (25837/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258877981678077/604462909807314587353088), (171691356015/604462909807314587353088)), (1413/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943968627199931/37778931862957161709568), (69725562673/18889465931478580854784)), (18369/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297648447474469/4722366482869645213696), (104546274121/2361183241434822606848)), (13777/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621598122450713/590295810358705651712), (71841399337/147573952589676412928)), (37/576460752303423488), by norm_num⟩
  | 8 => ⟨((455915584576437/18446744073709551616), (179501067765/36893488147419103232)), (23681/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911434176567103/4611686018427387904), (403595919045/9223372036854775808)), (13321/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594117196242967/1152921504606846976), (201622182759/576460752303423488)), (26643/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194696059483887/144115188075855872), (176221867627/72057594037927936)), (46629/144115188075855872), by norm_num⟩
  | 4 => ⟨((745905550217903/18014398509481984), (527876465417/36028797018963968)), (69949/36028797018963968), by norm_num⟩
  | 3 => ⟨((744738059569223/4503599627370496), (329233454635/4503599627370496)), (10931/1125899906842624), by norm_num⟩
  | 2 => ⟨((2228388883664789/4503599627370496), (1312807057143/4503599627370496)), (174927/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216774686986045/2251799813685248), (979463003073/1125899906842624)), (262477/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182113496884741/2251799813685248), (3876907059131/2251799813685248)), (525307/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2182113496884741/2251799813685248), (3876907059131/2251799813685248)), (2003887185103606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2114577083602057/2251799813685248), (7513857287387/2251799813685248)), (1019911/2251799813685248), by norm_num⟩
  | 2 => ⟨((992845757706561/1125899906842624), (14111938665953/2251799813685248)), (1922325/2251799813685248), by norm_num⟩
  | 3 => ⟨((437735586397231/562949953421312), (12444248687077/1125899906842624)), (3414401/2251799813685248), by norm_num⟩
  | 4 => ⟨((340303303344991/562949953421312), (38705326917285/2251799813685248)), (5385381/2251799813685248), by norm_num⟩
  | 5 => ⟨((1644376466057581/4503599627370496), (93589496025003/4503599627370496)), (13392123/4503599627370496), by norm_num⟩
  | 6 => ⟨((1196915885674079/9007199254740992), (17085928753347/1125899906842624)), (10336201/4503599627370496), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-270018875/134217728), (-5044627631/134217728)), (1/67108864), by norm_num⟩, -6, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-273308947/134217728), (-5106094399/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((276638016602667/2251799813685248), (-396735092504655/9007199254740992)), (24612267/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1719118813/4294967296), (308180149/2147483648)), (39/4294967296), by norm_num⟩
  | 2 => ⟨((5601055053/8589934592), (-2008161353/8589934592)), (129/8589934592), by norm_num⟩
  | 3 => ⟨((-3041463013/4294967296), (2180927851/8589934592)), (71/4294967296), by norm_num⟩
  | 4 => ⟨((4954690057/8589934592), (-888209185/4294967296)), (59/4294967296), by norm_num⟩
  | 5 => ⟨((-403571463/1073741824), (289387127/2147483648)), (79/8589934592), by norm_num⟩
  | 6 => ⟨((876583191/4294967296), (-1257134929/17179869184)), (87/17179869184), by norm_num⟩
  | 7 => ⟨((-3263991611/34359738368), (1170247703/34359738368)), (83/34359738368), by norm_num⟩
  | 8 => ⟨((1329299971/34359738368), (-1906389995/137438953472)), (137/137438953472), by norm_num⟩
  | 9 => ⟨((-3849766785/274877906944), (690133627/137438953472)), (101/274877906944), by norm_num⟩
  | 10 => ⟨((2508582367/549755813888), (-1798817585/1099511627776)), (67/549755813888), by norm_num⟩
  | 11 => ⟨((-2972074009/2199023255552), (2131171399/4398046511104)), (161/4398046511104), by norm_num⟩
  | 12 => ⟨((3227768013/8796093022208), (-144657545/1099511627776)), (89/8796093022208), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581323245535579/10141204801825835211973625643008), (-448431892239/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778827992634997/633825300114114700748351602688), (-132682345695/158456325028528675187087900672)), (2883/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944904253125097/19807040628566084398385987584), (-596964356795/39614081257132168796771975168)), (6487/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889587789874293/2475880078570760549798248448), (-634142905705/2475880078570760549798248448)), (13785/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442813522289017/38685626227668133590597632), (-633994770937/154742504910672534362390528)), (27571/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387403229343427/2417851639229258349412352), (-297106376549/4835703278458516698824704)), (25849/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258840791915605/604462909807314587353088), (-519778868921/604462909807314587353088)), (5655/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943938409921293/37778931862957161709568), (-52771616199/4722366482869645213696)), (36759/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648801560260881/2361183241434822606848), (-633001557883/4722366482869645213696)), (27571/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621535796226789/590295810358705651712), (-869958375075/590295810358705651712)), (37913/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455896107015133/18446744073709551616), (-1086820198385/73786976294838206464)), (11849/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455695175192055/2305843009213693952), (-610905077989/4611686018427387904)), (26663/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594029539776243/1152921504606846976), (-305183217999/288230376151711744)), (26667/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194619355564297/144115188075855872), (-1066930589225/144115188075855872)), (46677/144115188075855872), by norm_num⟩
  | 4 => ⟨((186462004473593/4503599627370496), (-798988854733/18014398509481984)), (70033/36028797018963968), by norm_num⟩
  | 3 => ⟨((744666136778883/4503599627370496), (-249155932679/1125899906842624)), (87573/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114050575233185/2251799813685248), (-1986924683145/2251799813685248)), (175243/4503599627370496), by norm_num⟩
  | 1 => ⟨((554085747508831/562949953421312), (-2964629789977/1125899906842624)), (65777/562949953421312), by norm_num⟩
  | 0 => ⟨((2181249761727795/2251799813685248), (-5866528021731/1125899906842624)), (527201/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2181249761727795/2251799813685248), (-5866528021731/1125899906842624)), (2011112221724700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2112848943995191/2251799813685248), (-22730906667281/2251799813685248)), (513431/1125899906842624), by norm_num⟩
  | 2 => ⟨((1982242799247159/2251799813685248), (-333254064261/17592186044416)), (121733/140737488355328), by norm_num⟩
  | 3 => ⟨((436036422130023/562949953421312), (-75100441472525/2251799813685248)), (3502935/2251799813685248), by norm_num⟩
  | 4 => ⟨((1348434300429461/2251799813685248), (-113612341063/2199023255552)), (88439/35184372088832), by norm_num⟩
  | 5 => ⟨((801465689808891/2251799813685248), (-278666953165957/4503599627370496)), (14727345/4503599627370496), by norm_num⟩
  | 6 => ⟨((276638016602667/2251799813685248), (-396735092504655/9007199254740992)), (24612267/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-273308947/134217728), (-5106094399/134217728)), (1/67108864), by norm_num⟩, -6, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-276474835/134217728), (-5165241105/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((50763811828409/562949953421312), (-202866554092547/2251799813685248)), (16314959/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2552936439/8589934592), (2550564071/8589934592)), (53/8589934592), by norm_num⟩
  | 2 => ⟨((525878877/1073741824), (-4203121547/8589934592)), (89/8589934592), by norm_num⟩
  | 3 => ⟨((-1155473993/2147483648), (2308800491/4294967296)), (51/4294967296), by norm_num⟩
  | 4 => ⟨((476031723/1073741824), (-3804714887/8589934592)), (43/4294967296), by norm_num⟩
  | 5 => ⟨((-2510276643/8589934592), (1253971959/4294967296)), (29/4294967296), by norm_num⟩
  | 6 => ⟨((86181899/536870912), (-344407251/2147483648)), (33/8589934592), by norm_num⟩
  | 7 => ⟨((-2596950673/34359738368), (2594537405/34359738368)), (1/536870912), by norm_num⟩
  | 8 => ⟨((1069890721/34359738368), (-4275586015/137438953472)), (27/34359738368), by norm_num⟩
  | 9 => ⟨((-783596729/68719476736), (3131474225/274877906944)), (81/274877906944), by norm_num⟩
  | 10 => ⟨((1033042795/274877906944), (-2064165639/549755813888)), (109/1099511627776), by norm_num⟩
  | 11 => ⟨((-2476174929/2199023255552), (2473873895/2199023255552)), (67/2199023255552), by norm_num⟩
  | 12 => ⟨((1360178103/4398046511104), (-1358914131/4398046511104)), (75/8796093022208), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790646259958961/5070602400912917605986812821504), (-511231638745/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778790995874597/633825300114114700748351602688), (-605030764269/316912650057057350374175801344)), (11541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889766856475877/39614081257132168796771975168), (-1361073930521/39614081257132168796771975168)), (1623/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889543499549571/2475880078570760549798248448), (-361459297985/618970019642690137449562112)), (13797/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771209756752135/154742504910672534362390528), (-722747734657/77371252455336267181195264)), (6899/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774785655533805/4835703278458516698824704), (-1354789031059/9671406556917033397649408)), (12937/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314701085439025/151115727451828646838272), (-296269388311/151115727451828646838272)), (11321/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887817504706165/75557863725914323419136), (-962535471233/37778931862957161709568)), (18399/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81097410066967/295147905179352825856), (-1443208395571/4722366482869645213696)), (6901/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621474408340533/590295810358705651712), (-1983445463003/590295810358705651712)), (4745/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911753757743999/36893488147419103232), (-1238929279955/36893488147419103232)), (11865/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822693930169681/9223372036854775808), (-1392800447349/4611686018427387904)), (1669/576460752303423488), by norm_num⟩
  | 6 => ⟨((796971232419423/576460752303423488), (-695778872087/288230376151711744)), (13357/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194542823442391/144115188075855872), (-1216216410497/72057594037927936)), (23385/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491580556572681/36028797018963968), (-1821534944235/18014398509481984)), (35097/36028797018963968), by norm_num⟩
  | 3 => ⟨((744593368688689/4503599627370496), (-4544089508825/9007199254740992)), (10977/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113903267582791/2251799813685248), (-9058999353737/4503599627370496)), (21981/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107946137200813/1125899906842624), (-6757886514523/1125899906842624)), (66079/1125899906842624), by norm_num⟩
  | 0 => ⟨((2180313545934987/2251799813685248), (-26741977315459/2251799813685248)), (265413/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2180313545934987/2251799813685248), (-26741977315459/2251799813685248)), (1012470253951262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2110779118263675/2251799813685248), (-25893019011561/1125899906842624)), (520279/2251799813685248), by norm_num⟩
  | 2 => ⟨((988699498352973/1125899906842624), (-24271448778993/562949953421312)), (249831/562949953421312), by norm_num⟩
  | 3 => ⟨((1732250405588501/2251799813685248), (-170510142766675/2251799813685248)), (460317/562949953421312), by norm_num⟩
  | 4 => ⟨((329915845628827/562949953421312), (-262337941560743/2251799813685248)), (3111727/2251799813685248), by norm_num⟩
  | 5 => ⟨((1485647380734015/4503599627370496), (-307485392989329/2251799813685248)), (8744573/4503599627370496), by norm_num⟩
  | 6 => ⟨((50763811828409/562949953421312), (-202866554092547/2251799813685248)), (16314959/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-276474835/134217728), (-5165241105/134217728)), (1/134217728), by norm_num⟩, -6, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile027Terms3
