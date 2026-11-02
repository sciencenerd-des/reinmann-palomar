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
namespace Reinmann.XiRectangle.Tile006Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨6,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1833/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1833/640))
  have he : value ((3/4), (1833/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

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

def J_negLog2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17862266831/34359738368), (-17052882865/8589934592)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-33695765420251/140737488355328), (-1225587651588733/2251799813685248)), (112795/1125899906842624), by norm_num⟩
  | 1 => ⟨((22808715623/137438953472), (51850135817/137438953472)), (11/137438953472), by norm_num⟩
  | 2 => ⟨((-7904898463/137438953472), (-35939775453/274877906944)), (9/274877906944), by norm_num⟩
  | 3 => ⟨((7305677443/549755813888), (33215405367/1099511627776)), (19/2199023255552), by norm_num⟩
  | 4 => ⟨((-40511277773/17592186044416), (-92092658325/17592186044416)), (29/17592186044416), by norm_num⟩
  | 5 => ⟨((22464222375/70368744177664), (25533506587/35184372088832)), (9/35184372088832), by norm_num⟩
  | 6 => ⟨((-10380674935/281474976710656), (-94391883203/1125899906842624)), (9/281474976710656), by norm_num⟩
  | 7 => ⟨((2055810161/562949953421312), (74774248811/9007199254740992)), (15/4503599627370496), by norm_num⟩
  | 8 => ⟨((-11399832135/36028797018963968), (-25914779871/36028797018963968)), (23/72057594037927936), by norm_num⟩
  | 9 => ⟨((28095152011/1152921504606846976), (63867579031/1152921504606846976)), (31/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-15579260323/9223372036854775808), (-70831411735/18446744073709551616)), (9/4611686018427387904), by norm_num⟩
  | 11 => ⟨((31414459253/295147905179352825856), (71413226675/295147905179352825856)), (19/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-29033125147/4722366482869645213696), (-4124989727/295147905179352825856)), (37/4722366482869645213696), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24739040482979/158456325028528675187087900672), (-2585966593577/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781163921665277/633825300114114700748351602688), (-3068209662705/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946217915680009/19807040628566084398385987584), (-3451564046441/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946189299029891/1237940039285380274899124224), (-916772744751/618970019642690137449562112)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774044082143831/154742504910672534362390528), (-916717650897/38685626227668133590597632)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776113834905103/4835703278458516698824704), (-107420530337/302231454903657293676544)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157640979310725/75557863725914323419136), (-3007540549297/604462909807314587353088)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891591640999923/75557863725914323419136), (-4886813909781/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300387816625695/4722366482869645213696), (-3664725714871/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625362446961329/590295810358705651712), (-1259593093371/147573952589676412928)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228545535388185/9223372036854775808), (-1574256670737/18446744073709551616)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914076642222155/4611686018427387904), (-7082863285549/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((12495282694615/9007199254740992), (-1770311815813/288230376151711744)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199308493349917/144115188075855872), (-3097135733467/72057594037927936)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498716399432107/36028797018963968), (-4643881385085/18014398509481984)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((374521100287221/2251799813685248), (-11603315253139/9007199254740992)), (173/4503599627370496), by norm_num⟩
  | 2 => ⟨((561383879532453/1125899906842624), (-2898428014803/562949953421312)), (87/562949953421312), by norm_num⟩
  | 1 => ⟨((1121160074713997/1125899906842624), (-1085405448597/70368744177664)), (523/1125899906842624), by norm_num⟩
  | 0 => ⟨((139531779465727/140737488355328), (-4329526796037/140737488355328)), (1057/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139531779465727/140737488355328), (-4329526796037/140737488355328)), (4032139304732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1105625681168173/1125899906842624), (-34339483255257/562949953421312)), (1081/562949953421312), by norm_num⟩
  | 2 => ⟨((270381793935933/281474976710656), (-134884510903023/1125899906842624)), (4511/1125899906842624), by norm_num⟩
  | 3 => ⟨((1022743845693933/1125899906842624), (-259137181275053/1125899906842624)), (2437/281474976710656), by norm_num⟩
  | 4 => ⟨((434698008782435/562949953421312), (-117697388430719/281474976710656)), (11099/562949953421312), by norm_num⟩
  | 5 => ⟨((237235400863099/562949953421312), (-90883425922297/140737488355328)), (52847/1125899906842624), by norm_num⟩
  | 6 => ⟨((-33695765420251/140737488355328), (-1225587651588733/2251799813685248)), (112795/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/34359738368), (-17052882865/8589934592)), (1/17179869184), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/34359738368), (-54056359741/17179869184)), (3/34359738368), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1975666411120479/4503599627370496), (9684012789725/4503599627370496)), (457793/4503599627370496), by norm_num⟩
  | 1 => ⟨((66238140795/137438953472), (-649351529/274877906944)), (33/274877906944), by norm_num⟩
  | 2 => ⟨((-284257951/1073741824), (356692785/274877906944)), (5/68719476736), by norm_num⟩
  | 3 => ⟨((106594740265/1099511627776), (-130622359/274877906944)), (31/1099511627776), by norm_num⟩
  | 4 => ⟨((-58553145781/2199023255552), (574013315/4398046511104)), (37/4398046511104), by norm_num⟩
  | 5 => ⟨((12865441099/2199023255552), (-504494465/17592186044416)), (35/17592186044416), by norm_num⟩
  | 6 => ⟨((-75382035683/70368744177664), (369495879/70368744177664)), (7/17592186044416), by norm_num⟩
  | 7 => ⟨((47323217569/281474976710656), (-463923101/562949953421312)), (37/562949953421312), by norm_num⟩
  | 8 => ⟨((-103979736721/4503599627370496), (127417905/1125899906842624)), (43/4503599627370496), by norm_num⟩
  | 9 => ⟨((101540814697/36028797018963968), (-497716893/36028797018963968)), (11/9007199254740992), by norm_num⟩
  | 10 => ⟨((-44621594731/144115188075855872), (109359579/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 11 => ⟨((35652241681/1152921504606846976), (-349509171/2305843009213693952)), (17/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-104447975545/36893488147419103232), (63995845/4611686018427387904)), (13/9223372036854775808), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197862808528795/1267650600228229401496703205376), (4085890304905/10141204801825835211973625643008)), (115/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780686543410475/633825300114114700748351602688), (1211354833207/158456325028528675187087900672)), (137/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891898366469129/39614081257132168796771975168), (2725327692459/19807040628566084398385987584)), (77/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945903513095355/1237940039285380274899124224), (5790829642853/2475880078570760549798248448)), (41/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443367982635459/38685626227668133590597632), (5790276131185/154742504910672534362390528)), (163/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551690661923391/9671406556917033397649408), (678474435923/1208925819614629174706176)), (153/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315164334264175/151115727451828646838272), (4748732351759/604462909807314587353088)), (67/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890825929055165/75557863725914323419136), (3857792796303/37778931862957161709568)), (109/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299812523740475/4722366482869645213696), (1446430527179/1180591620717411303424)), (41/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((203071222582901/73786976294838206464), (7953795136223/590295810358705651712)), (225/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913685496990437/36893488147419103232), (621242661979/4611686018427387904)), (281/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827032459466077/9223372036854775808), (11179117543829/9223372036854775808)), (317/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598271145494339/1152921504606846976), (2793762316991/288230376151711744)), (317/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198319348058273/144115188075855872), (4886792003283/72057594037927936)), (139/72057594037927936), by norm_num⟩
  | 4 => ⟨((748611611753247/18014398509481984), (14651189603391/36028797018963968)), (209/18014398509481984), by norm_num⟩
  | 3 => ⟨((1496201410440707/9007199254740992), (18297869926013/9007199254740992)), (523/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120860048613345/2251799813685248), (9136806393165/1125899906842624)), (263/1125899906842624), by norm_num⟩
  | 1 => ⟨((559118462620025/562949953421312), (27349491954463/1125899906842624)), (795/1125899906842624), by norm_num⟩
  | 0 => ⟨((69385181162625/70368744177664), (850837130927/17592186044416)), (1613/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((69385181162625/70368744177664), (850837130927/17592186044416)), (6153110984420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((273003057816167/281474976710656), (53692463979367/562949953421312)), (1669/562949953421312), by norm_num⟩
  | 2 => ⟨((1048902467529921/1125899906842624), (3254775748485/17592186044416)), (7113/1125899906842624), by norm_num⟩
  | 3 => ⟨((469315761116663/562949953421312), (194060152912383/562949953421312)), (7943/562949953421312), by norm_num⟩
  | 4 => ⟨((324359100794665/562949953421312), (647130266646137/1125899906842624)), (37441/1125899906842624), by norm_num⟩
  | 5 => ⟨((3655250437963/2251799813685248), (46607737977123/70368744177664)), (43093/562949953421312), by norm_num⟩
  | 6 => ⟨((-1975666411120479/4503599627370496), (9684012789725/4503599627370496)), (457793/4503599627370496), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/34359738368), (-54056359741/17179869184)), (3/34359738368), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17862266831/17179869184), (-17052882865/4294967296)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-537970340394799/2251799813685248), (1173734574703437/4503599627370496)), (556445/4503599627370496), by norm_num⟩
  | 1 => ⟨((22759559611/68719476736), (-49656421581/137438953472)), (13/68719476736), by norm_num⟩
  | 2 => ⟨((-15775724575/68719476736), (68838417231/274877906944)), (19/137438953472), by norm_num⟩
  | 3 => ⟨((58319461389/549755813888), (-7952525803/68719476736)), (37/549755813888), by norm_num⟩
  | 4 => ⟨((-40423970233/1099511627776), (44098166709/1099511627776)), (7/274877906944), by norm_num⟩
  | 5 => ⟨((22415808795/2199023255552), (-48906431875/4398046511104)), (33/4398046511104), by norm_num⟩
  | 6 => ⟨((-41433212443/17592186044416), (45199140487/17592186044416)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((65644147169/140737488355328), (-71610644097/140737488355328)), (53/140737488355328), by norm_num⟩
  | 8 => ⟨((-22750527765/281474976710656), (24818358027/281474976710656)), (39/562949953421312), by norm_num⟩
  | 9 => ⟨((56069205961/4503599627370496), (-3822838865/281474976710656)), (25/2251799813685248), by norm_num⟩
  | 10 => ⟨((-62182739245/36028797018963968), (33917311757/18014398509481984)), (29/18014398509481984), by norm_num⟩
  | 11 => ⟨((31346756645/144115188075855872), (-68391822593/288230376151711744)), (61/288230376151711744), by norm_num⟩
  | 12 => ⟨((-28970554651/1152921504606846976), (31603732669/1152921504606846976)), (59/2305843009213693952), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414715929/10141204801825835211973625643008), (3012617196731/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222544876942487/79228162514264337593543950336), (3571365185427/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945765138187683/19807040628566084398385987584), (3923239673/38685626227668133590597632)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891416390993731/2475880078570760549798248448), (4268030007081/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773081813429793/154742504910672534362390528), (4267518311279/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96957842343723/604462909807314587353088), (2000127342563/4835703278458516698824704)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((315084587736539/151115727451828646838272), (1749839528013/302231454903657293676544)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890308608132957/75557863725914323419136), (2842979361119/37778931862957161709568)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162428179423361/590295810358705651712), (4263576634975/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812019500021387/295147905179352825856), (5860967467219/590295810358705651712)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456677429060975/18446744073709551616), (3662016648665/36893488147419103232)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456572885769405/2305843009213693952), (2059136178817/2305843009213693952)), (105/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798767001788899/576460752303423488), (4116401373513/576460752303423488)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149709824074747/18014398509481984), (7199491266573/144115188075855872)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496270571319213/36028797018963968), (10790811081863/36028797018963968)), (553/36028797018963968), by norm_num⟩
  | 3 => ⟨((747512711220189/4503599627370496), (421055022917/281474976710656)), (693/9007199254740992), by norm_num⟩
  | 2 => ⟨((559853136142935/1125899906842624), (13451615270225/2251799813685248)), (87/281474976710656), by norm_num⟩
  | 1 => ⟨((558280843603101/562949953421312), (10061002203723/562949953421312)), (525/562949953421312), by norm_num⟩
  | 0 => ⟨((1107033507213261/1125899906842624), (10005502257033/281474976710656)), (2123/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1107033507213261/1125899906842624), (10005502257033/281474976710656)), (8098606589889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1087060596992591/1125899906842624), (78702742136965/1125899906842624)), (4327/1125899906842624), by norm_num⟩
  | 2 => ⟨((522029806011131/562949953421312), (151975587407739/1125899906842624)), (8961/1125899906842624), by norm_num⟩
  | 3 => ⟨((236913576376485/281474976710656), (70464333401867/281474976710656)), (19039/1125899906842624), by norm_num⟩
  | 4 => ⟨((727067407378387/1125899906842624), (1853401569243/4398046511104)), (41583/1125899906842624), by norm_num⟩
  | 5 => ⟨((134783061681007/562949953421312), (612793825794389/1125899906842624)), (177507/2251799813685248), by norm_num⟩
  | 6 => ⟨((-537970340394799/2251799813685248), (1173734574703437/4503599627370496)), (556445/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/17179869184), (-17052882865/4294967296)), (1/8589934592), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20737449597/17179869184), (-79191135647/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-69147291313665/2251799813685248), (2616741794757/8796093022208)), (429953/4503599627370496), by norm_num⟩
  | 1 => ⟨((6792497081/137438953472), (-32902214465/68719476736)), (23/137438953472), by norm_num⟩
  | 2 => ⟨((-5466051161/137438953472), (52954071363/137438953472)), (39/274877906944), by norm_num⟩
  | 3 => ⟨((11729693293/549755813888), (-56817526713/274877906944)), (11/137438953472), by norm_num⟩
  | 4 => ⟨((-589944159/68719476736), (91444281583/1099511627776)), (37/1099511627776), by norm_num⟩
  | 5 => ⟨((12153324745/4398046511104), (-29434778731/1099511627776)), (25/2199023255552), by norm_num⟩
  | 6 => ⟨((-3260003601/4398046511104), (63164598445/8796093022208)), (29/8796093022208), by norm_num⟩
  | 7 => ⟨((2998156223/17592186044416), (-116182285099/70368744177664)), (55/70368744177664), by norm_num⟩
  | 8 => ⟨((-9650692585/281474976710656), (23373521799/70368744177664)), (23/140737488355328), by norm_num⟩
  | 9 => ⟨((3451597895/562949953421312), (-66876857121/1125899906842624)), (17/562949953421312), by norm_num⟩
  | 10 => ⟨((-8888212017/9007199254740992), (21526829863/2251799813685248)), (23/4503599627370496), by norm_num⟩
  | 11 => ⟨((650228427/4503599627370496), (-100788643247/72057594037927936)), (55/72057594037927936), by norm_num⟩
  | 12 => ⟨((-5581345505/288230376151711744), (54071021195/288230376151711744)), (61/576460752303423488), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673631/10141204801825835211973625643008), (2180121897753/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780103857324817/633825300114114700748351602688), (322969369069/79228162514264337593543950336)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472810861730153/9903520314283042199192993792), (2906406348275/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945555954803677/1237940039285380274899124224), (3087675696639/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886388820628885/77371252455336267181195264), (3087247030289/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551040644545495/9671406556917033397649408), (361729832941/1208925819614629174706176)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260089450475193/604462909807314587353088), (2531653437651/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889904760351457/75557863725914323419136), (2056541523823/37778931862957161709568)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299123087900649/4722366482869645213696), (192754080877/295147905179352825856)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202953018336947/73786976294838206464), (1059844013815/147573952589676412928)), (149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228274057572245/9223372036854775808), (5297399723839/73786976294838206464)), (373/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456427858011051/2305843009213693952), (5957072106345/9223372036854775808)), (419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596956142943643/1152921504606846976), (5953944465927/1152921504606846976)), (105/288230376151711744), by norm_num⟩
  | 5 => ⟨((1197175494056123/144115188075855872), (5206183622275/144115188075855872)), (23/9007199254740992), by norm_num⟩
  | 4 => ⟨((1495520977064207/36028797018963968), (487640118199/2251799813685248)), (69/4503599627370496), by norm_num⟩
  | 3 => ⟨((1494097261035991/9007199254740992), (4870249119433/4503599627370496)), (691/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118791333359489/2251799813685248), (9722051222357/2251799813685248)), (693/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115222248669445/1125899906842624), (14536991497213/1125899906842624)), (1043/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104485990785763/1125899906842624), (28889835723339/1125899906842624)), (2103/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104485990785763/1125899906842624), (28889835723339/1125899906842624)), (8022312644576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((541369030153177/562949953421312), (14170184506903/281474976710656)), (4235/1125899906842624), by norm_num⟩
  | 2 => ⟨((519188692559341/562949953421312), (109015716185377/1125899906842624)), (8573/1125899906842624), by norm_num⟩
  | 3 => ⟨((473551494706515/562949953421312), (50270656219725/281474976710656)), (8737/562949953421312), by norm_num⟩
  | 4 => ⟨((760786856203763/1125899906842624), (676599949904589/2251799813685248)), (4455/140737488355328), by norm_num⟩
  | 5 => ⟨((51553180337969/140737488355328), (114297093744117/281474976710656)), (69583/1125899906842624), by norm_num⟩
  | 6 => ⟨((-69147291313665/2251799813685248), (2616741794757/8796093022208)), (429953/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20737449597/17179869184), (-79191135647/17179869184)), (1/8589934592), by norm_num⟩, -1, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2885830621/2147483648), (-88162125471/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((119572582668311/1125899906842624), (536488940728953/2251799813685248)), (156107/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3269123951/17179869184), (-58670601787/137438953472)), (19/137438953472), by norm_num⟩
  | 2 => ⟨((23429935181/137438953472), (52561803159/137438953472)), (19/137438953472), by norm_num⟩
  | 3 => ⟨((-27987205483/274877906944), (-31392702843/137438953472)), (25/274877906944), by norm_num⟩
  | 4 => ⟨((25073170221/549755813888), (7031021573/68719476736)), (3/68719476736), by norm_num⟩
  | 5 => ⟨((-17970036067/1099511627776), (-80626556683/2199023255552)), (9/549755813888), by norm_num⟩
  | 6 => ⟨((5366330381/1099511627776), (48154465469/4398046511104)), (23/4398046511104), by norm_num⟩
  | 7 => ⟨((-21977538915/17592186044416), (-24651776997/8796093022208)), (25/17592186044416), by norm_num⟩
  | 8 => ⟨((39378463461/140737488355328), (88340109735/140737488355328)), (47/140737488355328), by norm_num⟩
  | 9 => ⟨((-31358548795/562949953421312), (-17587136459/140737488355328)), (5/70368744177664), by norm_num⟩
  | 10 => ⟨((11237395349/1125899906842624), (50419069259/2251799813685248)), (15/1125899906842624), by norm_num⟩
  | 11 => ⟨((-7321712555/4503599627370496), (-32850489009/9007199254740992)), (41/18014398509481984), by norm_num⟩
  | 12 => ⟨((17491663735/72057594037927936), (78480233001/144115188075855872)), (51/144115188075855872), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (1499923711327/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889947329697187/316912650057057350374175801344), (888611317971/316912650057057350374175801344)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891008237478819/39614081257132168796771975168), (1999135270101/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890862170944695/2475880078570760549798248448), (2123789770245/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886264047663299/77371252455336267181195264), (2123461933325/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550806899949361/9671406556917033397649408), (1990397289985/9671406556917033397649408)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629942564298609/302231454903657293676544), (425109721/147573952589676412928)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889573120856367/75557863725914323419136), (707219383989/18889465931478580854784)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298874693741191/4722366482869645213696), (265135888799/590295810358705651712)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623283149570299/590295810358705651712), (728891769285/147573952589676412928)), (149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825767030944737/73786976294838206464), (14230733289/288230376151711744)), (93/18446744073709551616), by norm_num⟩
  | 7 => ⟨((57038560811561/288230376151711744), (4096539081687/9223372036854775808)), (419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596480058498243/1152921504606846976), (4094149985401/1152921504606846976)), (419/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196760495349351/144115188075855872), (1789847463797/72057594037927936)), (367/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494901625247885/36028797018963968), (5364173330381/36028797018963968)), (551/36028797018963968), by norm_num⟩
  | 3 => ⟨((373332141980581/2251799813685248), (3347914404803/4503599627370496)), (689/9007199254740992), by norm_num⟩
  | 2 => ⟨((2236061733405333/4503599627370496), (13363526059327/4503599627370496)), (1379/4503599627370496), by norm_num⟩
  | 1 => ⟨((2228204100060415/2251799813685248), (9987536064905/1125899906842624)), (2073/2251799813685248), by norm_num⟩
  | 0 => ⟨((2204654421075829/2251799813685248), (9917486895777/562949953421312)), (4171/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2204654421075829/2251799813685248), (9917486895777/562949953421312)), (15911110884856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2157797234948667/2251799813685248), (77678774810637/2251799813685248)), (8315/2251799813685248), by norm_num⟩
  | 2 => ⟨((516259803251099/562949953421312), (148872066230681/2251799813685248)), (8255/1125899906842624), by norm_num⟩
  | 3 => ⟨((941962965215653/1125899906842624), (273049720156265/2251799813685248)), (16233/1125899906842624), by norm_num⟩
  | 4 => ⟨((771520794290225/1125899906842624), (456883817978059/2251799813685248)), (62199/2251799813685248), by norm_num⟩
  | 5 => ⟨((964665912021565/2251799813685248), (156539388627045/562949953421312)), (27621/562949953421312), by norm_num⟩
  | 6 => ⟨((119572582668311/1125899906842624), (536488940728953/2251799813685248)), (156107/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-88162125471/17179869184)), (1/8589934592), by norm_num⟩, -1, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-25072861353/17179869184), (-95746989293/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((793635917450555/4503599627370496), (341060555542895/2251799813685248)), (220007/4503599627370496), by norm_num⟩
  | 1 => ⟨((-47129644361/137438953472), (-20253698623/68719476736)), (15/137438953472), by norm_num⟩
  | 2 => ⟨((22927513321/68719476736), (19705938853/68719476736)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((-29743253909/137438953472), (-51127981881/274877906944)), (23/274877906944), by norm_num⟩
  | 4 => ⟨((57877699647/549755813888), (49745229421/549755813888)), (3/68719476736), by norm_num⟩
  | 5 => ⟨((-45049921259/1099511627776), (-38719898719/1099511627776)), (5/274877906944), by norm_num⟩
  | 6 => ⟨((58442065995/4398046511104), (50230295925/4398046511104)), (7/1099511627776), by norm_num⟩
  | 7 => ⟨((-16246144193/4398046511104), (-27926755037/8796093022208)), (33/17592186044416), by norm_num⟩
  | 8 => ⟨((7903384217/8796093022208), (54342956057/70368744177664)), (17/35184372088832), by norm_num⟩
  | 9 => ⟨((-54681868657/281474976710656), (-46998448765/281474976710656)), (31/281474976710656), by norm_num⟩
  | 10 => ⟨((42562401275/1125899906842624), (36581903377/1125899906842624)), (13/562949953421312), by norm_num⟩
  | 11 => ⟨((-60234624443/9007199254740992), (-51770979675/9007199254740992)), (19/4503599627370496), by norm_num⟩
  | 12 => ⟨((39070389009/36028797018963968), (33580558259/36028797018963968)), (13/18014398509481984), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693182059/10141204801825835211973625643008), (28900760597/316912650057057350374175801344)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779717280956925/633825300114114700748351602688), (1095592733153/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236351096637179/4951760157141521099596496896), (1232382255335/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890650347644369/2475880078570760549798248448), (654605566901/1237940039285380274899124224)), (27/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((221539549129493/19342813113834066795298816), (327247948245/38685626227668133590597632)), (27/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775304278790425/4835703278458516698824704), (1226946804255/9671406556917033397649408)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629855853752239/302231454903657293676544), (268336376503/151115727451828646838272)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889291552375447/75557863725914323419136), (871874892467/37778931862957161709568)), (9/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((649331863985653/2361183241434822606848), (653715186873/2361183241434822606848)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622993413650659/590295810358705651712), (1797096285637/590295810358705651712)), (297/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912702686861543/36893488147419103232), (561360003849/18446744073709551616)), (93/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824827785970573/9223372036854775808), (2524841407879/9223372036854775808)), (209/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596074778132395/1152921504606846976), (1261622030565/576460752303423488)), (209/576460752303423488), by norm_num⟩
  | 5 => ⟨((299101715867347/36028797018963968), (1103021397935/72057594037927936)), (183/72057594037927936), by norm_num⟩
  | 4 => ⟨((747186575720903/18014398509481984), (826368955023/9007199254740992)), (549/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492671423746271/9007199254740992), (2062786091807/4503599627370496)), (687/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117378881780457/2251799813685248), (8232354813029/4503599627370496)), (687/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113136925818081/1125899906842624), (12301656971729/2251799813685248)), (129/140737488355328), by norm_num⟩
  | 0 => ⟨((1100448105627245/1125899906842624), (24416403712337/2251799813685248)), (4143/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1100448105627245/1125899906842624), (24416403712337/2251799813685248)), (15804299361418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1075439286944785/1125899906842624), (47728905648141/2251799813685248)), (4095/1125899906842624), by norm_num⟩
  | 2 => ⟨((2053468768884619/2251799813685248), (11397447487325/281474976710656)), (7997/1125899906842624), by norm_num⟩
  | 3 => ⟨((934457015987273/1125899906842624), (166297570986447/2251799813685248)), (30467/2251799813685248), by norm_num⟩
  | 4 => ⟨((769425584755759/1125899906842624), (276042179247907/2251799813685248)), (27537/1125899906842624), by norm_num⟩
  | 5 => ⟨((3975749655159/8796093022208), (94321845971501/562949953421312)), (44389/1125899906842624), by norm_num⟩
  | 6 => ⟨((793635917450555/4503599627370496), (341060555542895/2251799813685248)), (220007/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-25072861353/17179869184), (-95746989293/17179869184)), (1/8589934592), by norm_num⟩, -1, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-13396700123/8589934592), (-102317297191/17179869184)), (3/17179869184), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((112054194682731/562949953421312), (76145917771453/1125899906842624)), (56889/1125899906842624), by norm_num⟩
  | 1 => ⟨((-14221810751/34359738368), (-19328733477/137438953472)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((59146848147/137438953472), (10048242835/68719476736)), (19/137438953472), by norm_num⟩
  | 3 => ⟨((-81994942065/274877906944), (-27859644763/274877906944)), (29/274877906944), by norm_num⟩
  | 4 => ⟨((85251844369/549755813888), (452597677/8589934592)), (33/549755813888), by norm_num⟩
  | 5 => ⟨((-70910490675/1099511627776), (-24093450527/1099511627776)), (15/549755813888), by norm_num⟩
  | 6 => ⟨((98302813367/4398046511104), (16700307303/2199023255552)), (45/4398046511104), by norm_num⟩
  | 7 => ⟨((-58404272509/8796093022208), (-19844178723/8796093022208)), (29/8796093022208), by norm_num⟩
  | 8 => ⟨((30362067617/17592186044416), (20632404799/35184372088832)), (1/1099511627776), by norm_num⟩
  | 9 => ⟨((-28060508753/70368744177664), (-19068390953/140737488355328)), (31/140737488355328), by norm_num⟩
  | 10 => ⟨((93360300131/1125899906842624), (31721283425/1125899906842624)), (27/562949953421312), by norm_num⟩
  | 11 => ⟨((-35297688443/2251799813685248), (-11993191729/2251799813685248)), (43/4503599627370496), by norm_num⟩
  | 12 => ⟨((97865972899/36028797018963968), (8313047033/9007199254740992)), (63/36028797018963968), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521241/10141204801825835211973625643008), (213325301539/5070602400912917605986812821504)), (57/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1779563255408083/633825300114114700748351602688), (252673994561/316912650057057350374175801344)), (271/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236329443371397/4951760157141521099596496896), (568438187981/39614081257132168796771975168)), (305/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472616590132165/618970019642690137449562112), (603869479797/2475880078570760549798248448)), (81/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772132479739057/154742504910672534362390528), (37735087579/9671406556917033397649408)), (81/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387609054317539/2417851639229258349412352), (565911507241/9671406556917033397649408)), (19/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((629780494053487/302231454903657293676544), (495057792763/604462909807314587353088)), (133/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472261695060257/18889465931478580854784), (50265860789/4722366482869645213696)), (27/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1298480277330837/4722366482869645213696), (603002145927/4722366482869645213696)), (81/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101421336102849/36893488147419103232), (414411136641/295147905179352825856)), (445/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825090641440853/73786976294838206464), (1035569537007/73786976294838206464)), (557/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824474141800793/9223372036854775808), (145548237969/1152921504606846976)), (313/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398930417625199/288230376151711744), (1163599136869/1152921504606846976)), (313/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196098497180793/144115188075855872), (1017264839421/144115188075855872)), (137/36028797018963968), by norm_num⟩
  | 4 => ⟨((373477951499485/9007199254740992), (1524130215445/36028797018963968)), (821/36028797018963968), by norm_num⟩
  | 3 => ⟨((746048422451039/4503599627370496), (1902074414411/9007199254740992)), (1027/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116807449350081/2251799813685248), (1897449814763/2251799813685248)), (1027/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112287615171257/1125899906842624), (2834640940621/1125899906842624)), (771/562949953421312), by norm_num⟩
  | 0 => ⟨((2197561337172837/2251799813685248), (702914085833/140737488355328)), (6177/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2197561337172837/2251799813685248), (702914085833/140737488355328)), (23563393599700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1072286558224573/1125899906842624), (5487865516261/562949953421312)), (12119/2251799813685248), by norm_num⟩
  | 2 => ⟨((2042238371795339/2251799813685248), (41812345063127/2251799813685248)), (23321/2251799813685248), by norm_num⟩
  | 3 => ⟨((1851403161904841/2251799813685248), (75842244042925/2251799813685248)), (43169/2251799813685248), by norm_num⟩
  | 4 => ⟨((379911837758959/562949953421312), (124713191264751/2251799813685248)), (73895/2251799813685248), by norm_num⟩
  | 5 => ⟨((1018640590293349/2251799813685248), (2630119327117/35184372088832)), (26981/562949953421312), by norm_num⟩
  | 6 => ⟨((112054194682731/562949953421312), (76145917771453/1125899906842624)), (56889/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13396700123/8589934592), (-102317297191/17179869184)), (3/17179869184), by norm_num⟩, -1, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 12 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨6,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile006Terms0
