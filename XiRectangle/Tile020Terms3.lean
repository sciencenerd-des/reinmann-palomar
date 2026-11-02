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
namespace Reinmann.XiRectangle.Tile020Terms3
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
  | 0 => ⟨((-622309043/268435456), (-7494934535/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-207964168738381/2251799813685248), (-306980559145475/9007199254740992)), (612325/281474976710656), by norm_num⟩
  | 1 => ⟨((613046717/2147483648), (1809863931/17179869184)), (117/17179869184), by norm_num⟩
  | 2 => ⟨((-473738357/1073741824), (-1398591561/8589934592)), (23/2147483648), by norm_num⟩
  | 3 => ⟨((3904920995/8589934592), (1441035297/8589934592)), (97/8589934592), by norm_num⟩
  | 4 => ⟨((-3017569143/8589934592), (-139196915/1073741824)), (19/2147483648), by norm_num⟩
  | 5 => ⟨((3730973731/17179869184), (344210859/4294967296)), (3/536870912), by norm_num⟩
  | 6 => ⟨((-1922099699/17179869184), (-1418627171/34359738368)), (101/34359738368), by norm_num⟩
  | 7 => ⟨((848755967/17179869184), (313216915/17179869184)), (91/68719476736), by norm_num⟩
  | 8 => ⟨((-5247081453/274877906944), (-1936333563/274877906944)), (143/274877906944), by norm_num⟩
  | 9 => ⟨((3604211451/549755813888), (1330064277/549755813888)), (25/137438953472), by norm_num⟩
  | 10 => ⟨((-2228154121/1099511627776), (-822257029/1099511627776)), (63/1099511627776), by norm_num⟩
  | 11 => ⟨((5008959259/8796093022208), (1848459189/8796093022208)), (9/549755813888), by norm_num⟩
  | 12 => ⟨((-1290242143/8796093022208), (-476138819/8796093022208)), (151/35184372088832), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580955946170575/10141204801825835211973625643008), (-1815883420059/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222297956132839/79228162514264337593543950336), (-4296278866557/633825300114114700748351602688)), (11579/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118081760626843/2475880078570760549798248448), (-4832314879223/39614081257132168796771975168)), (13029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944527791652323/1237940039285380274899124224), (-320819861083/154742504910672534362390528)), (13847/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885360604506531/77371252455336267181195264), (-2565874526225/77371252455336267181195264)), (3463/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549112627131175/9671406556917033397649408), (-4809560737129/9671406556917033397649408)), (12991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258402323478499/604462909807314587353088), (-1051727987337/151115727451828646838272)), (2843/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887162970337481/75557863725914323419136), (-1708376721103/18889465931478580854784)), (2311/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648533281864879/2361183241434822606848), (-1280686601381/1180591620717411303424)), (6937/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620796132454823/590295810358705651712), (-879987989209/73786976294838206464)), (19089/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455664251369271/18446744073709551616), (-1099259178031/9223372036854775808)), (23879/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821733448570727/9223372036854775808), (-1235669020149/1152921504606846976)), (13445/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796488710528945/576460752303423488), (-9875381792061/1152921504606846976)), (26923/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193693291568285/144115188075855872), (-4314874767357/72057594037927936)), (11797/72057594037927936), by norm_num⟩
  | 4 => ⟨((745148028149903/18014398509481984), (-12922223084253/36028797018963968)), (4433/4503599627370496), by norm_num⟩
  | 3 => ⟨((1487563335590729/9007199254740992), (-16113616936169/9007199254740992)), (22229/4503599627370496), by norm_num⟩
  | 2 => ⟨((556126678245653/1125899906842624), (-8027477305505/1125899906842624)), (44651/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105405539448837/1125899906842624), (-11968029309905/562949953421312)), (33729/562949953421312), by norm_num⟩
  | 0 => ⟨((1084815892903061/1125899906842624), (-11822080934903/281474976710656)), (17107/140737488355328), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1084815892903061/1125899906842624), (-11822080934903/281474976710656)), (65258026659917787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1043244900185559/1125899906842624), (-91125551800311/1125899906842624)), (275221/1125899906842624), by norm_num⟩
  | 2 => ⟨((479641240312863/562949953421312), (-168871613923239/1125899906842624)), (69323/140737488355328), by norm_num⟩
  | 3 => ⟨((395996682399161/562949953421312), (-575523915499171/2251799813685248)), (2222779/2251799813685248), by norm_num⟩
  | 4 => ⟨((967131344887473/2251799813685248), (-50605200292219/140737488355328)), (4263359/2251799813685248), by norm_num⟩
  | 5 => ⟨((124236685974503/2251799813685248), (-695505881039277/2251799813685248)), (105127/35184372088832), by norm_num⟩
  | 6 => ⟨((-207964168738381/2251799813685248), (-306980559145475/9007199254740992)), (612325/281474976710656), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-622309043/268435456), (-7494934535/268435456)), (1/134217728), by norm_num⟩, -4, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-631258365/268435456), (-3801358965/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-856630328267639/9007199254740992), (41147686506381/9007199254740992)), (17602551/9007199254740992), by norm_num⟩
  | 1 => ⟨((5123061065/17179869184), (-246082941/17179869184)), (107/17179869184), by norm_num⟩
  | 2 => ⟨((-1003958021/2147483648), (385795819/17179869184)), (85/8589934592), by norm_num⟩
  | 3 => ⟨((2098603045/4294967296), (-201610093/8589934592)), (91/8589934592), by norm_num⟩
  | 4 => ⟨((-6580157709/17179869184), (39509205/2147483648)), (9/1073741824), by norm_num⟩
  | 5 => ⟨((4126409287/17179869184), (-99104707/8589934592)), (23/4294967296), by norm_num⟩
  | 6 => ⟨((-1078194371/8589934592), (103580745/17179869184)), (49/17179869184), by norm_num⟩
  | 7 => ⟨((7727250775/137438953472), (-92793379/34359738368)), (89/68719476736), by norm_num⟩
  | 8 => ⟨((-6057187527/274877906944), (290953103/274877906944)), (71/137438953472), by norm_num⟩
  | 9 => ⟨((4220505879/549755813888), (-202729283/549755813888)), (101/549755813888), by norm_num⟩
  | 10 => ⟨((-5293348709/2199023255552), (127131299/1099511627776)), (129/2199023255552), by norm_num⟩
  | 11 => ⟨((3017684411/4398046511104), (-9059533/274877906944)), (149/8796093022208), by norm_num⟩
  | 12 => ⟨((-6307954677/35184372088832), (151499271/17592186044416)), (79/17592186044416), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518632069/10141204801825835211973625643008), (4029753135795/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889164995476241/316912650057057350374175801344), (74481611811/9903520314283042199192993792)), (181/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1889247690198753/39614081257132168796771975168), (2680773117781/19807040628566084398385987584)), (3259/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888991170485967/2475880078570760549798248448), (88988635909/38685626227668133590597632)), (433/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((442664156058727/38685626227668133590597632), (5693731324939/154742504910672534362390528)), (3465/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549051896342635/9671406556917033397649408), (1334058915637/2417851639229258349412352)), (12999/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258349001645733/604462909807314587353088), (4667569035641/604462909807314587353088)), (2845/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887075980725845/75557863725914323419136), (7581730598037/75557863725914323419136)), (18501/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297001022944741/4722366482869645213696), (5683613106965/4722366482869645213696)), (13885/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620705529350349/590295810358705651712), (3905303147569/295147905179352825856)), (19105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822543025965625/73786976294838206464), (9756717276873/73786976294838206464)), (23903/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821604225756307/9223372036854775808), (1370914609257/1152921504606846976)), (26919/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592846956228767/1152921504606846976), (2739021045253/288230376151711744)), (26955/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193577741443631/144115188075855872), (9573943607769/144115188075855872)), (11813/72057594037927936), by norm_num⟩
  | 4 => ⟨((372529988492939/9007199254740992), (1791959021193/4503599627370496)), (555/562949953421312), by norm_num⟩
  | 3 => ⟨((185917296172743/1125899906842624), (17875452571231/9007199254740992)), (22271/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112021176153837/2251799813685248), (8904661212489/1125899906842624)), (11189/562949953421312), by norm_num⟩
  | 1 => ⟨((138129923111511/140737488355328), (3318615810909/140737488355328)), (33835/562949953421312), by norm_num⟩
  | 0 => ⟨((271003238108481/281474976710656), (52439242515807/1125899906842624)), (34373/281474976710656), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((271003238108481/281474976710656), (52439242515807/1125899906842624)), (131122590185069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((520620971617483/562949953421312), (100976681421653/1125899906842624)), (138781/562949953421312), by norm_num⟩
  | 2 => ⟨((953893403519855/1125899906842624), (93384105768113/562949953421312)), (563171/1125899906842624), by norm_num⟩
  | 3 => ⟨((194295748476459/281474976710656), (632940686428209/2251799813685248)), (570555/562949953421312), by norm_num⟩
  | 4 => ⟨((895035028993593/2251799813685248), (436904501593363/1125899906842624)), (277107/140737488355328), by norm_num⟩
  | 5 => ⟨((16673564340489/2251799813685248), (1389270328115255/4503599627370496)), (13931159/4503599627370496), by norm_num⟩
  | 6 => ⟨((-856630328267639/9007199254740992), (41147686506381/9007199254740992)), (17602551/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-631258365/268435456), (-3801358965/134217728)), (1/134217728), by norm_num⟩, -5, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-639826747/268435456), (-3852956691/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-1508423205458253/18014398509481984), (696236870140841/18014398509481984)), (37189639/18014398509481984), by norm_num⟩
  | 1 => ⟨((4571771761/17179869184), (-2110174419/17179869184)), (115/17179869184), by norm_num⟩
  | 2 => ⟨((-3632334189/8589934592), (838280987/4294967296)), (93/8589934592), by norm_num⟩
  | 3 => ⟨((3847917861/8589934592), (-444017017/2147483648)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((-764305631/2147483648), (705554991/4294967296)), (81/8589934592), by norm_num⟩
  | 5 => ⟨((3886407101/17179869184), (-1793833393/17179869184)), (105/17179869184), by norm_num⟩
  | 6 => ⟨((-1029267581/8589934592), (1900299695/34359738368)), (113/34359738368), by norm_num⟩
  | 7 => ⟨((3738363175/68719476736), (-862750675/34359738368)), (13/8589934592), by norm_num⟩
  | 8 => ⟨((-742544963/34359738368), (342733511/34359738368)), (21/34359738368), by norm_num⟩
  | 9 => ⟨((4195285091/549755813888), (-1936400973/549755813888)), (15/68719476736), by norm_num⟩
  | 10 => ⟨((-5333136741/2199023255552), (615398653/549755813888)), (155/2199023255552), by norm_num⟩
  | 11 => ⟨((770408893/1099511627776), (-177797277/549755813888)), (91/4398046511104), by norm_num⟩
  | 12 => ⟨((-1632267289/8796093022208), (1506798179/17592186044416)), (49/8796093022208), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580870939645499/10141204801825835211973625643008), (1764493105025/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778283645898277/633825300114114700748351602688), (4174242450395/633825300114114700748351602688)), (11577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889195722043037/39614081257132168796771975168), (2347514312101/19807040628566084398385987584)), (3257/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236117022102843/309485009821345068724781056), (1246813182995/618970019642690137449562112)), (6923/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770601880700137/154742504910672534362390528), (4985885858883/154742504910672534362390528)), (6925/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549000839861521/9671406556917033397649408), (4672815994777/9671406556917033397649408)), (12989/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258304592606665/604462909807314587353088), (1021815584947/151115727451828646838272)), (5685/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887004313201807/75557863725914323419136), (1659770043839/18889465931478580854784)), (4621/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296947706894131/4722366482869645213696), (2488464936645/2361183241434822606848)), (13871/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405158231298531/147573952589676412928), (6839412021049/590295810358705651712)), (19085/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911226663746117/36893488147419103232), (4271733791805/36893488147419103232)), (11937/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455376191423887/2305843009213693952), (2400858358033/2305843009213693952)), (26883/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592749306166205/1152921504606846976), (9593479761951/1152921504606846976)), (26915/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193494329209739/144115188075855872), (4191552466051/72057594037927936)), (11793/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489998887080219/36028797018963968), (1569037217529/4503599627370496)), (35449/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487194099564599/9007199254740992), (15651287947129/9007199254740992)), (11109/2251799813685248), by norm_num⟩
  | 2 => ⟨((1111887449590645/2251799813685248), (15592752038865/2251799813685248)), (2789/140737488355328), by norm_num⟩
  | 1 => ⟨((1104864969962477/1125899906842624), (23243105196959/1125899906842624)), (16851/281474976710656), by norm_num⟩
  | 0 => ⟨((1083767725524943/1125899906842624), (45904023490909/1125899906842624)), (136693/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1083767725524943/1125899906842624), (45904023490909/1125899906842624)), (521442417625045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1041340616862433/1125899906842624), (88372507767051/1125899906842624)), (274303/1125899906842624), by norm_num⟩
  | 2 => ⟨((1912391276800909/2251799813685248), (81735402225843/562949953421312)), (1100929/2251799813685248), by norm_num⟩
  | 3 => ⟨((1576671939652335/2251799813685248), (555324924613799/2251799813685248)), (2189669/2251799813685248), by norm_num⟩
  | 4 => ⟨((967008088443737/2251799813685248), (777658138798043/2251799813685248)), (518293/281474976710656), by norm_num⟩
  | 5 => ⟨((146705963944515/2251799813685248), (1335823381264251/4503599627370496)), (6425071/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1508423205458253/18014398509481984), (696236870140841/18014398509481984)), (37189639/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-639826747/268435456), (-3852956691/134217728)), (1/134217728), by norm_num⟩, -5, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-162011325/67108864), (-7804895581/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-35038210281901/562949953421312), (144644392558071/2251799813685248)), (9207181/4503599627370496), by norm_num⟩
  | 1 => ⟨((1720941895/8589934592), (-3552187641/17179869184)), (115/17179869184), by norm_num⟩
  | 2 => ⟨((-2769749131/8589934592), (2858512731/8589934592)), (47/4294967296), by norm_num⟩
  | 3 => ⟨((2971826173/8589934592), (-1533532921/4294967296)), (103/8589934592), by norm_num⟩
  | 4 => ⟨((-298935607/1073741824), (2468126023/8589934592)), (21/2147483648), by norm_num⟩
  | 5 => ⟨((3079157115/17179869184), (-3177836475/17179869184)), (55/8589934592), by norm_num⟩
  | 6 => ⟨((-3303808133/34359738368), (1704843501/17179869184)), (15/4294967296), by norm_num⟩
  | 7 => ⟨((3038442323/68719476736), (-3135816875/68719476736)), (7/4294967296), by norm_num⟩
  | 8 => ⟨((-2445092135/137438953472), (2523451283/137438953472)), (23/34359738368), by norm_num⟩
  | 9 => ⟨((437247109/68719476736), (-3610078369/549755813888)), (67/274877906944), by norm_num⟩
  | 10 => ⟨((-1125955319/549755813888), (1162039399/549755813888)), (11/137438953472), by norm_num⟩
  | 11 => ⟨((2635862077/4398046511104), (-1360167465/2199023255552)), (105/4398046511104), by norm_num⟩
  | 12 => ⟨((-1414085453/8796093022208), (2918806781/17592186044416)), (115/17592186044416), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (3048664543387/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778238842165419/633825300114114700748351602688), (3605914234239/633825300114114700748351602688)), (5785/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944572730493381/19807040628566084398385987584), (4055789990757/39614081257132168796771975168)), (13019/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888882962084413/2475880078570760549798248448), (2154107165643/1237940039285380274899124224)), (3459/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770548876879133/154742504910672534362390528), (269188703879/9671406556917033397649408)), (865/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387237843181559/2417851639229258349412352), (4036561121047/9671406556917033397649408)), (12979/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258261532638475/604462909807314587353088), (1765360953921/302231454903657293676544)), (11361/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886934759967215/75557863725914323419136), (1433761090457/18889465931478580854784)), (4617/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296895908415607/4722366482869645213696), (4299202648815/4722366482869645213696)), (6929/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810281148539995/295147905179352825856), (2954012040399/295147905179352825856)), (19065/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822365933345425/73786976294838206464), (7379963296911/73786976294838206464)), (23847/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821407670459373/9223372036854775808), (8295495977145/9223372036854775808)), (26849/9223372036854775808), by norm_num⟩
  | 6 => ⟨((12442607320279/9007199254740992), (4143399373649/576460752303423488)), (6719/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193412419014831/144115188075855872), (3620586511845/72057594037927936)), (5887/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489879437471711/36028797018963968), (1355278628823/4503599627370496)), (17691/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487050742590261/9007199254740992), (6759327860441/4503599627370496)), (44335/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223505960862921/4503599627370496), (26935110962213/4503599627370496)), (2781/140737488355328), by norm_num⟩
  | 1 => ⟨((2209370659083125/2251799813685248), (5018479290867/281474976710656)), (134299/2251799813685248), by norm_num⟩
  | 0 => ⟨((541747881788779/562949953421312), (39640176538119/1125899906842624)), (16991/140737488355328), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((541747881788779/562949953421312), (39640176538119/1125899906842624)), (64815521777105287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2082586061104305/2251799813685248), (38147230571289/562949953421312)), (271189/1125899906842624), by norm_num⟩
  | 2 => ⟨((1915748147985585/2251799813685248), (282244949749705/2251799813685248)), (269187/562949953421312), by norm_num⟩
  | 3 => ⟨((797235334382359/1125899906842624), (480247166266851/2251799813685248)), (2102039/2251799813685248), by norm_num⟩
  | 4 => ⟨((1026600747897029/2251799813685248), (340056880596625/1125899906842624)), (3873469/2251799813685248), by norm_num⟩
  | 5 => ⟨((262614093768181/2251799813685248), (1240261752670427/4503599627370496)), (366979/140737488355328), by norm_num⟩
  | 6 => ⟨((-35038210281901/562949953421312), (144644392558071/2251799813685248)), (9207181/4503599627370496), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-7804895581/268435456)), (1/134217728), by norm_num⟩, -5, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-20498171/8388608), (-1974998777/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-9864368623613/281474976710656), (22367534075937/281474976710656)), (34718417/18014398509481984), by norm_num⟩
  | 1 => ⟨((980806435/8589934592), (-2223986369/8589934592)), (109/17179869184), by norm_num⟩
  | 2 => ⟨((-1597781025/8589934592), (3622981145/8589934592)), (45/4294967296), by norm_num⟩
  | 3 => ⟨((1735241609/8589934592), (-3934674109/8589934592)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((-706698085/4294967296), (3204887023/8589934592)), (83/8589934592), by norm_num⟩
  | 5 => ⟨((1841992467/17179869184), (-2088366263/8589934592)), (55/8589934592), by norm_num⟩
  | 6 => ⟨((-2000463093/34359738368), (567008241/4294967296)), (121/34359738368), by norm_num⟩
  | 7 => ⟨((232775067/8589934592), (-4222554485/68719476736)), (115/68719476736), by norm_num⟩
  | 8 => ⟨((-94800455/8589934592), (3439372537/137438953472)), (95/137438953472), by norm_num⟩
  | 9 => ⟨((2196402021/549755813888), (-4980359003/549755813888)), (35/137438953472), by norm_num⟩
  | 10 => ⟨((-357804491/274877906944), (3245298085/1099511627776)), (93/1099511627776), by norm_num⟩
  | 11 => ⟨((847826599/2199023255552), (-3844907075/4398046511104)), (7/274877906944), by norm_num⟩
  | 12 => ⟨((-920766969/8796093022208), (2087846405/8796093022208)), (123/17592186044416), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395198185306375/2535301200456458802993406410752), (2587183956281/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778195472315055/633825300114114700748351602688), (764983336965/158456325028528675187087900672)), (2891/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944548394562777/19807040628566084398385987584), (430210969481/4951760157141521099596496896)), (13011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944415702365923/1237940039285380274899124224), (3655881077479/2475880078570760549798248448)), (13827/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110656093464811/9671406556917033397649408), (1827427603937/77371252455336267181195264)), (6915/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774451694700093/4835703278458516698824704), (856334272407/2417851639229258349412352)), (6485/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629109866929625/302231454903657293676544), (2996080644045/604462909807314587353088)), (1419/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886867186576457/75557863725914323419136), (2433294676431/37778931862957161709568)), (4613/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648422766993623/2361183241434822606848), (3648156293839/4722366482869645213696)), (13845/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620493528288537/590295810358705651712), (2506657267273/295147905179352825856)), (19045/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911140357709777/36893488147419103232), (6262295110111/73786976294838206464)), (5955/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227664102546079/1152921504606846976), (7039107473773/9223372036854775808)), (419/144115188075855872), by norm_num⟩
  | 6 => ⟨((796280079773855/576460752303423488), (3515822698443/576460752303423488)), (26839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193331967103303/144115188075855872), (1536075810201/36028797018963968)), (11755/72057594037927936), by norm_num⟩
  | 4 => ⟨((744880803954193/18014398509481984), (4599851386497/18014398509481984)), (35317/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486908421285451/9007199254740992), (11470359244695/9007199254740992)), (22119/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223236139836401/4503599627370496), (22853098379231/4503599627370496)), (88749/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209002718467873/2251799813685248), (34061252937415/2251799813685248)), (33453/562949953421312), by norm_num⟩
  | 0 => ⟨((2166401237371603/2251799813685248), (67252854828509/2251799813685248)), (135195/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2166401237371603/2251799813685248), (67252854828509/2251799813685248)), (515728001121139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2082232775003691/2251799813685248), (129404636266321/2251799813685248)), (536423/2251799813685248), by norm_num⟩
  | 2 => ⟨((958999051151011/1125899906842624), (239320185776361/2251799813685248)), (65857/140737488355328), by norm_num⟩
  | 3 => ⟨((1608243569035273/2251799813685248), (407687805436321/2251799813685248)), (2019001/2251799813685248), by norm_num⟩
  | 4 => ⟨((537400797338401/1125899906842624), (582344209536127/2251799813685248)), (903759/562949953421312), by norm_num⟩
  | 5 => ⟨((724819039934079/4503599627370496), (1111829712848033/4503599627370496)), (5320759/2251799813685248), by norm_num⟩
  | 6 => ⟨((-9864368623613/281474976710656), (22367534075937/281474976710656)), (34718417/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20498171/8388608), (-1974998777/67108864)), (1/134217728), by norm_num⟩, -5, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-165884901/67108864), (-3995752553/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-28282794282597/4503599627370496), (758336757456955/9007199254740992)), (3928651/2251799813685248), by norm_num⟩
  | 1 => ⟨((177794411/8589934592), (-595892487/2147483648)), (101/17179869184), by norm_num⟩
  | 2 => ⟨((-292990687/8589934592), (7855857707/17179869184)), (169/17179869184), by norm_num⟩
  | 3 => ⟨((321883169/8589934592), (-4315270907/8589934592)), (95/8589934592), by norm_num⟩
  | 4 => ⟨((-530437207/17179869184), (7111214471/17179869184)), (159/17179869184), by norm_num⟩
  | 5 => ⟨((87411725/4294967296), (-4687480563/17179869184)), (53/8589934592), by norm_num⟩
  | 6 => ⟨((-384126381/34359738368), (5149723749/34359738368)), (59/17179869184), by norm_num⟩
  | 7 => ⟨((90429849/17179869184), (-4849328395/68719476736)), (113/68719476736), by norm_num⟩
  | 8 => ⟨((-149021015/68719476736), (3995648825/137438953472)), (189/274877906944), by norm_num⟩
  | 9 => ⟨((436576849/549755813888), (-5852891867/549755813888)), (35/137438953472), by norm_num⟩
  | 10 => ⟨((-575554429/2199023255552), (7716070715/2199023255552)), (187/2199023255552), by norm_num⟩
  | 11 => ⟨((344897001/4398046511104), (-4623801877/4398046511104)), (113/4398046511104), by norm_num⟩
  | 12 => ⟨((-94727021/4398046511104), (2539882781/8796093022208)), (63/8796093022208), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (2143121941093/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778153440066781/633825300114114700748351602688), (2534610556559/633825300114114700748351602688)), (11557/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889049600706033/39614081257132168796771975168), (712705534169/9903520314283042199192993792)), (3251/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472195348909901/618970019642690137449562112), (3028234521855/2475880078570760549798248448)), (6909/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885223815446171/77371252455336267181195264), (1513687668095/77371252455336267181195264)), (6911/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548856794864655/9671406556917033397649408), (1418625893769/4835703278458516698824704)), (405/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258179116995585/604462909807314587353088), (1240841527683/302231454903657293676544)), (11343/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943400735729171/37778931862957161709568), (4031025183869/75557863725914323419136)), (18437/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296796498768357/4722366482869645213696), (377721691649/590295810358705651712)), (13833/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810213256227175/295147905179352825856), (4152509975717/590295810358705651712)), (19027/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822197556179193/73786976294838206464), (648374603515/9223372036854775808)), (23795/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455305026094175/2305843009213693952), (5830369296495/9223372036854775808)), (837/288230376151711744), by norm_num⟩
  | 6 => ⟨((199058561151987/144115188075855872), (1456030561089/288230376151711744)), (26803/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193252929140763/144115188075855872), (636135843413/18014398509481984)), (11737/72057594037927936), by norm_num⟩
  | 4 => ⟨((744822695578467/18014398509481984), (7619608963023/36028797018963968)), (35255/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486767230046659/9007199254740992), (9500017497427/9007199254740992)), (2759/562949953421312), by norm_num⟩
  | 2 => ⟨((2222965934071681/4503599627370496), (9463363455761/2251799813685248)), (88515/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208627633942231/2251799813685248), (7051856171223/562949953421312)), (133343/2251799813685248), by norm_num⟩
  | 0 => ⟨((270721333053677/281474976710656), (55687805009805/2251799813685248)), (67245/562949953421312), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((270721333053677/281474976710656), (55687805009805/2251799813685248)), (256519319774436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((16262898802897/17592186044416), (107120547504903/2251799813685248)), (66339/281474976710656), by norm_num⟩
  | 2 => ⟨((1919263090155125/2251799813685248), (198052774042385/2251799813685248)), (1031715/2251799813685248), by norm_num⟩
  | 3 => ⟨((1618414694671129/2251799813685248), (42201284591579/281474976710656)), (1940197/2251799813685248), by norm_num⟩
  | 4 => ⟨((278142556206169/562949953421312), (121323713949923/562949953421312)), (3370703/2251799813685248), by norm_num⟩
  | 5 => ⟨((890222480710167/4503599627370496), (959098768091099/4503599627370496)), (2391833/1125899906842624), by norm_num⟩
  | 6 => ⟨((-28282794282597/4503599627370496), (758336757456955/9007199254740992)), (3928651/2251799813685248), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-3995752553/134217728)), (1/134217728), by norm_num⟩, -5, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile020Terms3
