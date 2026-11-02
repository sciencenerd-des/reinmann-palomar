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
namespace Reinmann.XiRectangle.Tile002Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (141/128))
  have he : value ((3/4), (141/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-17862266831/34359738368), (-3279400551/4294967296)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((7556463734153/17592186044416), (-925850910879217/2251799813685248)), (71863/2251799813685248), by norm_num⟩
  | 1 => ⟨((-40919855721/137438953472), (39169369415/137438953472)), (5/137438953472), by norm_num⟩
  | 2 => ⟨((14181741311/137438953472), (-54300275949/549755813888)), (9/549755813888), by norm_num⟩
  | 3 => ⟨((-52426848027/2199023255552), (50184110903/2199023255552)), (11/2199023255552), by norm_num⟩
  | 4 => ⟨((36339521895/8796093022208), (-34784974981/8796093022208)), (5/4398046511104), by norm_num⟩
  | 5 => ⟨((-40301819431/70368744177664), (19288885867/35184372088832)), (13/70368744177664), by norm_num⟩
  | 6 => ⟨((37246790013/562949953421312), (-35653431613/562949953421312)), (7/281474976710656), by norm_num⟩
  | 7 => ⟨((-29505722837/4503599627370496), (28243514971/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 8 => ⟨((20451808595/36028797018963968), (-19576912771/36028797018963968)), (19/72057594037927936), by norm_num⟩
  | 9 => ⟨((-25201979493/576460752303423488), (12061939459/288230376151711744)), (13/576460752303423488), by norm_num⟩
  | 10 => ⟨((1746868103/576460752303423488), (-13377118925/4611686018427387904)), (31/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-56358944601/295147905179352825856), (13486999661/73786976294838206464)), (17/147573952589676412928), by norm_num⟩
  | 12 => ⟨((52086724733/4722366482869645213696), (-24929268771/2361183241434822606848)), (17/2361183241434822606848), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24739040482979/158456325028528675187087900672), (-994602536003/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781168193423785/633825300114114700748351602688), (-295020159879/158456325028528675187087900672)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((473110224391809/9903520314283042199192993792), (-5185655541/154742504910672534362390528)), (51/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473096074281113/618970019642690137449562112), (-1410423383323/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774050136915739/154742504910672534362390528), (-1410339095137/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552233724037139/9671406556917033397649408), (-1322103347513/9671406556917033397649408)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261133509744407/604462909807314587353088), (-1156750877167/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891601571543953/75557863725914323419136), (-1879552270401/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300395884106337/4722366482869645213696), (-1409517290761/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812687273140301/295147905179352825856), (-1937847551795/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914190458289131/36893488147419103232), (-2421951371115/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((914087035823381/4611686018427387904), (-1362101486975/4611686018427387904)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599419564132743/1152921504606846976), (-2723587614505/1152921504606846976)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199331864591885/144115188075855872), (-297805867081/18014398509481984)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((187344660142383/4503599627370496), (-446535760797/4503599627370496)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((749072843873995/4503599627370496), (-4462935351215/9007199254740992)), (43/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122844304317775/2251799813685248), (-4459302568755/2251799813685248)), (43/562949953421312), by norm_num⟩
  | 1 => ⟨((1121312975977553/1125899906842624), (-6679874011245/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | 0 => ⟨((279177997883003/281474976710656), (-13323441379783/1125899906842624)), (519/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((279177997883003/281474976710656), (-13323441379783/1125899906842624)), (1979832175826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((553720695047307/562949953421312), (-13214715328471/562949953421312)), (1043/1125899906842624), by norm_num⟩
  | 2 => ⟨((136083135614511/140737488355328), (-12998067256357/281474976710656)), (2101/1125899906842624), by norm_num⟩
  | 3 => ⟨((525130370777367/562949953421312), (-100545648204693/1125899906842624)), (2129/562949953421312), by norm_num⟩
  | 4 => ⟨((970724121421361/1125899906842624), (-187581767085665/1125899906842624)), (4353/562949953421312), by norm_num⟩
  | 5 => ⟨((805682987495875/1125899906842624), (-323457076321351/1125899906842624)), (8957/562949953421312), by norm_num⟩
  | 6 => ⟨((7556463734153/17592186044416), (-925850910879217/2251799813685248)), (71863/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/34359738368), (-3279400551/4294967296)), (1/34359738368), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-28311023105/34359738368), (-41581815185/34359738368)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((5446137056957/35184372088832), (-462154966545793/1125899906842624)), (133735/2251799813685248), by norm_num⟩
  | 1 => ⟨((-23371848033/137438953472), (61978653017/137438953472)), (11/137438953472), by norm_num⟩
  | 2 => ⟨((12838299729/137438953472), (-4255656865/17179869184)), (7/137438953472), by norm_num⟩
  | 3 => ⟨((-18805751797/549755813888), (99740094469/1099511627776)), (23/1099511627776), by norm_num⟩
  | 4 => ⟨((10330115011/1099511627776), (-6848480841/274877906944)), (15/2199023255552), by norm_num⟩
  | 5 => ⟨((-18158066071/8796093022208), (12038120337/2199023255552)), (29/17592186044416), by norm_num⟩
  | 6 => ⟨((26598232699/70368744177664), (-17633635913/17592186044416)), (3/8796093022208), by norm_num⟩
  | 7 => ⟨((-33395594629/562949953421312), (88560133065/562949953421312)), (33/562949953421312), by norm_num⟩
  | 8 => ⟨((36688810647/4503599627370496), (-97293250471/4503599627370496)), (39/4503599627370496), by norm_num⟩
  | 9 => ⟨((-35828247319/36028797018963968), (95011164953/36028797018963968)), (41/36028797018963968), by norm_num⟩
  | 10 => ⟨((31489082229/288230376151711744), (-41752173351/144115188075855872)), (39/288230376151711744), by norm_num⟩
  | 11 => ⟨((-25159485597/2305843009213693952), (33359600525/1152921504606846976)), (33/2305843009213693952), by norm_num⟩
  | 12 => ⟨((18427013369/18446744073709551616), (-97731378885/36893488147419103232)), (51/36893488147419103232), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197862808528795/1267650600228229401496703205376), (-788203861335/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780697196166851/633825300114114700748351602688), (-934723632531/316912650057057350374175801344)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945955495451089/19807040628566084398385987584), (-2102970476777/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891821226997243/2475880078570760549798248448), (-2234217956937/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110842938561341/9671406556917033397649408), (-34906347869/2417851639229258349412352)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551705746205071/9671406556917033397649408), (-2094155956063/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260671476277291/604462909807314587353088), (-1832161554561/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890850668102719/75557863725914323419136), (-46513138201/1180591620717411303424)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299832619913311/4722366482869645213696), (-2232261681841/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812299958694239/295147905179352825856), (-383595037765/73786976294838206464)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456853104932349/18446744073709551616), (-479381396947/9223372036854775808)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827084223268157/9223372036854775808), (-4313196273047/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1598329354477249/1152921504606846976), (-4311651053969/1152921504606846976)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198377525397663/144115188075855872), (-3770956514587/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((374331240645645/9007199254740992), (-5652958992179/36028797018963968)), (69/9007199254740992), by norm_num⟩
  | 3 => ⟨((1496353876344751/9007199254740992), (-7060117333521/9007199254740992)), (345/9007199254740992), by norm_num⟩
  | 2 => ⟨((1121050380859565/2251799813685248), (-7050997645885/2251799813685248)), (173/1125899906842624), by norm_num⟩
  | 1 => ⟨((1118616837772187/1125899906842624), (-2638426439757/281474976710656)), (519/1125899906842624), by norm_num⟩
  | 0 => ⟨((277824716384721/281474976710656), (-10508149990411/562949953421312)), (261/281474976710656), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277824716384721/281474976710656), (-10508149990411/562949953421312)), (995637060069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1096494880388767/1125899906842624), (-41487507343363/1125899906842624)), (2101/1125899906842624), by norm_num⟩
  | 2 => ⟨((533164538942015/562949953421312), (-80807963701959/1125899906842624)), (531/140737488355328), by norm_num⟩
  | 3 => ⟨((502055186465777/562949953421312), (-9566556593565/70368744177664)), (8657/1125899906842624), by norm_num⟩
  | 4 => ⟨((437342951069087/562949953421312), (-273015493486223/1125899906842624)), (4449/281474976710656), by norm_num⟩
  | 5 => ⟨((613320920908707/1125899906842624), (-212099496381853/562949953421312)), (72563/2251799813685248), by norm_num⟩
  | 6 => ⟨((5446137056957/35184372088832), (-462154966545793/1125899906842624)), (133735/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/34359738368), (-41581815185/34359738368)), (1/17179869184), by norm_num⟩, 0, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-17862266831/17179869184), (-3279400551/2147483648)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((69569996725881/4503599627370496), (-795371173727673/2251799813685248)), (243211/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2943252385/137438953472), (67298496895/137438953472)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((4080214185/274877906944), (-93295526757/274877906944)), (19/274877906944), by norm_num⟩
  | 3 => ⟨((-3770918611/549755813888), (86223375107/549755813888)), (19/549755813888), by norm_num⟩
  | 4 => ⟨((5227603207/2199023255552), (-119530978707/2199023255552)), (29/2199023255552), by norm_num⟩
  | 5 => ⟨((-2898798739/4398046511104), (1035657011/68719476736)), (9/2199023255552), by norm_num⟩
  | 6 => ⟨((5358117795/35184372088832), (-61257620241/17592186044416)), (9/8796093022208), by norm_num⟩
  | 7 => ⟨((-4244530563/140737488355328), (97052678303/140737488355328)), (31/140737488355328), by norm_num⟩
  | 8 => ⟨((2942084393/562949953421312), (-67271790331/562949953421312)), (3/70368744177664), by norm_num⟩
  | 9 => ⟨((-3625417781/4503599627370496), (82896447643/4503599627370496)), (1/140737488355328), by norm_num⟩
  | 10 => ⟨((4020716981/36028797018963968), (-91935102339/36028797018963968)), (37/36028797018963968), by norm_num⟩
  | 11 => ⟨((-4053743475/288230376151711744), (92690264699/288230376151711744)), (39/288230376151711744), by norm_num⟩
  | 12 => ⟨((3746454481/2305843009213693952), (-21415998547/576460752303423488)), (19/1152921504606846976), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414715929/10141204801825835211973625643008), (-994602536003/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890181426588475/316912650057057350374175801344), (-147383845941/39614081257132168796771975168)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891534821879707/39614081257132168796771975168), (-663164621815/9903520314283042199192993792)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891421503951139/2475880078570760549798248448), (-1409075031323/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886543622539501/77371252455336267181195264), (-2817813039511/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775665454086053/4835703278458516698824704), (-2641341653741/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630171720581955/302231454903657293676544), (-2256656147/590295810358705651712)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890317513938439/75557863725914323419136), (-3754404519113/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299432669407887/4722366482869645213696), (-175951002031/295147905179352825856)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812024923834337/295147905179352825856), (-1934983831483/295147905179352825856)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826724626195077/73786976294838206464), (-4836028134303/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826310172214351/9223372036854775808), (-1359640905901/2305843009213693952)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597554949940097/1152921504606846976), (-1359025975655/288230376151711744)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197699524688213/144115188075855872), (-4753824160419/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((1496307170361157/36028797018963968), (-7125203813743/36028797018963968)), (69/9007199254740992), by norm_num⟩
  | 3 => ⟨((1495080256761881/9007199254740992), (-8896825461269/9007199254740992)), (345/9007199254740992), by norm_num⟩
  | 2 => ⟨((559887351372131/1125899906842624), (-277572231313/70368744177664)), (173/1125899906842624), by norm_num⟩
  | 1 => ⟨((17448409542343/17592186044416), (-6643599590703/562949953421312)), (521/1125899906842624), by norm_num⟩
  | 0 => ⟨((553720695047307/562949953421312), (-26429430656943/1125899906842624)), (525/562949953421312), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((553720695047307/562949953421312), (-26429430656943/1125899906842624)), (2002718211936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((136083135614511/140737488355328), (-25996134512715/562949953421312)), (2115/1125899906842624), by norm_num⟩
  | 2 => ⟨((525130370777367/562949953421312), (-100545648204697/1125899906842624)), (2143/562949953421312), by norm_num⟩
  | 3 => ⟨((60670257588835/70368744177664), (-23447720885709/140737488355328)), (4381/562949953421312), by norm_num⟩
  | 4 => ⟨((805682987495871/1125899906842624), (-323457076321363/1125899906842624)), (18029/1125899906842624), by norm_num⟩
  | 5 => ⟨((967227357971559/2251799813685248), (-925850910879247/2251799813685248)), (18081/562949953421312), by norm_num⟩
  | 6 => ⟨((69569996725881/4503599627370496), (-795371173727673/2251799813685248)), (243211/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/17179869184), (-3279400551/2147483648)), (1/17179869184), by norm_num⟩, 0, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-41474899193/34359738368), (-30458129095/17179869184)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-135178741411779/2251799813685248), (-1319477433054559/4503599627370496)), (220289/4503599627370496), by norm_num⟩
  | 1 => ⟨((13278917931/137438953472), (64807647869/137438953472)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((-10685796977/137438953472), (-13037985687/34359738368)), (11/137438953472), by norm_num⟩
  | 3 => ⟨((11465417853/274877906944), (111913751821/549755813888)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((-18452878175/1099511627776), (-5628694847/68719476736)), (23/1099511627776), by norm_num⟩
  | 5 => ⟨((11879504691/2199023255552), (14494455815/549755813888)), (17/2199023255552), by norm_num⟩
  | 6 => ⟨((-3186554205/2199023255552), (-62207804557/8796093022208)), (5/2199023255552), by norm_num⟩
  | 7 => ⟨((1465303185/4398046511104), (6983789/4294967296)), (5/8796093022208), by norm_num⟩
  | 8 => ⟨((-18866515993/281474976710656), (-1438716773/4398046511104)), (17/140737488355328), by norm_num⟩
  | 9 => ⟨((6747663581/562949953421312), (65863831317/1125899906842624)), (13/562949953421312), by norm_num⟩
  | 10 => ⟨((-4343978235/2251799813685248), (-5300187359/562949953421312)), (35/9007199254740992), by norm_num⟩
  | 11 => ⟨((5084627827/18014398509481984), (99261934297/72057594037927936)), (43/72057594037927936), by norm_num⟩
  | 12 => ⟨((-5455595197/144115188075855872), (-832062085/4503599627370496)), (3/36028797018963968), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673669/10141204801825835211973625643008), (-1154697785795/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445025855554773/158456325028528675187087900672), (-2736962667843/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891242931771253/39614081257132168796771975168), (-3078745419943/39614081257132168796771975168)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891111330159329/2475880078570760549798248448), (-3270763274823/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772777025708287/154742504910672534362390528), (-3270309078883/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775520014562155/4835703278458516698824704), (-3065432203811/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630044436827069/302231454903657293676544), (-670442662351/151115727451828646838272)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944951875593599/37778931862957161709568), (-4356972624607/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649561134105107/2361183241434822606848), (-1633468967003/2361183241434822606848)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811811458803521/295147905179352825856), (-2245376765279/295147905179352825856)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826190771307695/73786976294838206464), (-5611512921301/73786976294838206464)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456427330386477/2305843009213693952), (-6310300000021/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399238442532723/288230376151711744), (-6306985446531/1152921504606846976)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197173123115243/144115188075855872), (-5514884071157/144115188075855872)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((373879208032055/9007199254740992), (-4132435708749/18014398509481984)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((747045526025105/4503599627370496), (-5159023701511/4503599627370496)), (173/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118783586852541/2251799813685248), (-5149246152891/1125899906842624)), (347/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115206799804983/1125899906842624), (-15398877827743/1125899906842624)), (261/562949953421312), by norm_num⟩
  | 0 => ⟨((1104439864753617/1125899906842624), (-7650619232501/281474976710656)), (1053/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104439864753617/1125899906842624), (-7650619232501/281474976710656)), (4016880515670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1082557069109967/1125899906842624), (-60038366246039/1125899906842624)), (531/281474976710656), by norm_num⟩
  | 2 => ⟨((1037681232015391/1125899906842624), (-57727118905027/562949953421312)), (539/140737488355328), by norm_num⟩
  | 3 => ⟨((944535701429209/1125899906842624), (-53203972664011/281474976710656)), (4417/562949953421312), by norm_num⟩
  | 4 => ⟨((752160190094957/1125899906842624), (-714138815837687/2251799813685248)), (9081/562949953421312), by norm_num⟩
  | 5 => ⟨((778481971316879/2251799813685248), (-954164369692489/2251799813685248)), (71573/2251799813685248), by norm_num⟩
  | 6 => ⟨((-135178741411779/2251799813685248), (-1319477433054559/4503599627370496)), (220289/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/34359738368), (-30458129095/17179869184)), (1/17179869184), by norm_num⟩, 0, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-2885830621/2147483648), (-67817019593/34359738368)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-460647890548219/4503599627370496), (-1080669558860095/4503599627370496)), (200183/4503599627370496), by norm_num⟩
  | 1 => ⟨((25188300167/137438953472), (59091183935/137438953472)), (13/137438953472), by norm_num⟩
  | 2 => ⟨((-22565687669/137438953472), (-26469297091/68719476736)), (13/137438953472), by norm_num⟩
  | 3 => ⟨((13477428187/137438953472), (31617742471/137438953472)), (17/274877906944), by norm_num⟩
  | 4 => ⟨((-24148309575/549755813888), (-14162847367/137438953472)), (17/549755813888), by norm_num⟩
  | 5 => ⟨((34614369877/2199023255552), (81204530819/2199023255552)), (27/2199023255552), by norm_num⟩
  | 6 => ⟨((-10336770833/2199023255552), (-24249831173/2199023255552)), (9/2199023255552), by norm_num⟩
  | 7 => ⟨((21166865167/17592186044416), (24828494075/8796093022208)), (5/4398046511104), by norm_num⟩
  | 8 => ⟨((-37925931097/140737488355328), (-88973378731/140737488355328)), (19/70368744177664), by norm_num⟩
  | 9 => ⟨((30201842743/562949953421312), (70852841711/562949953421312)), (1/17592186044416), by norm_num⟩
  | 10 => ⟨((-21645775089/2251799813685248), (-50780500023/2251799813685248)), (3/281474976710656), by norm_num⟩
  | 11 => ⟨((28206561807/18014398509481984), (33085978825/9007199254740992)), (33/18014398509481984), by norm_num⟩
  | 12 => ⟨((-33692916141/144115188075855872), (-9880352643/18014398509481984)), (21/72057594037927936), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (-2571010258673/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779891390478771/633825300114114700748351602688), (-3046326686115/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29546943257987/618970019642690137449562112), (-856674875935/9903520314283042199192993792)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890857819142939/2475880078570760549798248448), (-227522993015/154742504910672534362390528)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443130868122545/38685626227668133590597632), (-227487813487/9671406556917033397649408)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775401139092451/4835703278458516698824704), (-3411719185653/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157485099603979/75557863725914323419136), (-2984656310485/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889565542544163/75557863725914323419136), (-4848945382173/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649434269248515/2361183241434822606848), (-3635728139101/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623273920438661/590295810358705651712), (-4997532391513/590295810358705651712)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825754346955999/73786976294838206464), (-6244525067991/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456304525020591/2305843009213693952), (-7021804325009/9223372036854775808)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798231122190375/576460752303423488), (-3508848517635/576460752303423488)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299185674214539/36028797018963968), (-6135865143435/144115188075855872)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494870513030255/36028797018963968), (-9194560543657/36028797018963968)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((23332530778699/140737488355328), (-1434630117975/1125899906842624)), (173/4503599627370496), by norm_num⟩
  | 2 => ⟨((139746592740025/281474976710656), (-715800751061/140737488355328)), (87/562949953421312), by norm_num⟩
  | 1 => ⟨((1113986168550433/1125899906842624), (-8559341646719/562949953421312)), (523/1125899906842624), by norm_num⟩
  | 0 => ⟨((1101981403801469/1125899906842624), (-33995454892595/1125899906842624)), (1057/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1101981403801469/1125899906842624), (-33995454892595/1125899906842624)), (4032139304732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((538772281620093/562949953421312), (-33273258908483/562949953421312)), (1067/562949953421312), by norm_num⟩
  | 2 => ⟨((513666374650743/562949953421312), (-63688466479517/562949953421312)), (2169/562949953421312), by norm_num⟩
  | 3 => ⟨((922984084483591/1125899906842624), (-232451382115065/1125899906842624)), (8899/1125899906842624), by norm_num⟩
  | 4 => ⟨((708647340952603/1125899906842624), (-762230904557337/2251799813685248)), (36531/2251799813685248), by norm_num⟩
  | 5 => ⟨((634038716415867/2251799813685248), (-959504304820865/2251799813685248)), (35359/1125899906842624), by norm_num⟩
  | 6 => ⟨((-460647890548219/4503599627370496), (-1080669558860095/4503599627370496)), (200183/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-67817019593/34359738368)), (1/17179869184), by norm_num⟩, 0, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-50145722707/34359738368), (-36825765113/17179869184)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-567137669683717/4503599627370496), (-439744824647891/2251799813685248)), (22793/562949953421312), by norm_num⟩
  | 1 => ⟨((16839583547/68719476736), (52228022295/137438953472)), (13/137438953472), by norm_num⟩
  | 2 => ⟨((-16384158265/68719476736), (-12703879831/34359738368)), (7/68719476736), by norm_num⟩
  | 3 => ⟨((42509466469/274877906944), (16480405797/68719476736)), (5/68719476736), by norm_num⟩
  | 4 => ⟨((-10339950279/137438953472), (-32069388901/274877906944)), (21/549755813888), by norm_num⟩
  | 5 => ⟨((16096491351/549755813888), (49923319469/1099511627776)), (9/549755813888), by norm_num⟩
  | 6 => ⟨((-41763101179/4398046511104), (-64764196019/4398046511104)), (25/4398046511104), by norm_num⟩
  | 7 => ⟨((46438424251/17592186044416), (72014460759/17592186044416)), (15/8796093022208), by norm_num⟩
  | 8 => ⟨((-2823906283/4398046511104), (-70066835035/70368744177664)), (31/70368744177664), by norm_num⟩
  | 9 => ⟨((9769009593/70368744177664), (30298614535/140737488355328)), (29/281474976710656), by norm_num⟩
  | 10 => ⟨((-30415383861/1125899906842624), (-47166705221/1125899906842624)), (3/140737488355328), by norm_num⟩
  | 11 => ⟨((10761018935/2251799813685248), (16687667343/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 12 => ⟨((-13959983973/18014398509481984), (-10824233749/9007199254740992)), (25/36028797018963968), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693182021/10141204801825835211973625643008), (-2792202324939/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779712077247949/633825300114114700748351602688), (-1653890607843/316912650057057350374175801344)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472700653985607/9903520314283042199192993792), (-3720761207301/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890643422197463/2475880078570760549798248448), (-494089838411/309485009821345068724781056)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886154518197569/77371252455336267181195264), (-3952054874513/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775300601396061/4835703278458516698824704), (-3704346167865/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259704814357523/604462909807314587353088), (-3240597670815/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889279493302435/75557863725914323419136), (-5264649024541/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298653933661909/4722366482869645213696), (-3947329960175/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622978728637863/590295810358705651712), (-5425699085583/590295810358705651712)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((114086574519417/4611686018427387904), (-6779304799613/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912401287459881/4611686018427387904), (-3811421138577/4611686018427387904)), (105/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798023218649455/576460752303423488), (-952249827919/144115188075855872)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196378549620685/144115188075855872), (-6660300890205/144115188075855872)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494323662885015/36028797018963968), (-9979558547859/36028797018963968)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((746298656087323/4503599627370496), (-12455392635357/9007199254740992)), (347/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117286454317123/2251799813685248), (-12426823035137/2251799813685248)), (349/2251799813685248), by norm_num⟩
  | 1 => ⟨((69559544128405/70368744177664), (-18568858886099/1125899906842624)), (131/281474976710656), by norm_num⟩
  | 0 => ⟨((274974654066163/281474976710656), (-18426253750793/562949953421312)), (1059/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274974654066163/281474976710656), (-18426253750793/562949953421312)), (4039768699264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1073291552301951/1125899906842624), (-18000721805079/281474976710656)), (535/281474976710656), by norm_num⟩
  | 2 => ⟨((1018536668761767/1125899906842624), (-137277017477749/1125899906842624)), (4355/1125899906842624), by norm_num⟩
  | 3 => ⟨((452336819593993/562949953421312), (-248373190599937/1125899906842624)), (4471/562949953421312), by norm_num⟩
  | 4 => ⟨((672124712892989/1125899906842624), (-49892685142611/140737488355328)), (36631/2251799813685248), by norm_num⟩
  | 5 => ⟨((259736861098273/1125899906842624), (-953096635980095/2251799813685248)), (17427/562949953421312), by norm_num⟩
  | 6 => ⟨((-567137669683717/4503599627370496), (-439744824647891/2251799813685248)), (22793/562949953421312), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50145722707/34359738368), (-36825765113/17179869184)), (1/17179869184), by norm_num⟩, 0, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-53586800493/34359738368), (-9838201653/4294967296)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-156041873560041/1125899906842624), (-711884312734571/4503599627370496)), (41727/1125899906842624), by norm_num⟩
  | 1 => ⟨((4951171175/17179869184), (11293959143/34359738368)), (13/137438953472), by norm_num⟩
  | 2 => ⟨((-41182684085/137438953472), (-5871281953/17179869184)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((57091322723/274877906944), (1017415633/4294967296)), (25/274877906944), by norm_num⟩
  | 4 => ⟨((-29679517035/274877906944), (-33850501319/274877906944)), (29/549755813888), by norm_num⟩
  | 5 => ⟨((3085841033/68719476736), (7039013865/137438953472)), (13/549755813888), by norm_num⟩
  | 6 => ⟨((-34223072187/2199023255552), (-9758145229/549755813888)), (5/549755813888), by norm_num⟩
  | 7 => ⟨((20332822283/4398046511104), (46380554421/8796093022208)), (13/4398046511104), by norm_num⟩
  | 8 => ⟨((-42280915315/35184372088832), (-48222825795/35184372088832)), (29/35184372088832), by norm_num⟩
  | 9 => ⟨((19537931495/70368744177664), (22283677159/70368744177664)), (29/140737488355328), by norm_num⟩
  | 10 => ⟨((-4062798639/70368744177664), (-37070083189/562949953421312)), (13/281474976710656), by norm_num⟩
  | 11 => ⟨((6144256193/562949953421312), (14015467443/1125899906842624)), (21/2251799813685248), by norm_num⟩
  | 12 => ⟨((-34070990855/18014398509481984), (-19429563485/9007199254740992)), (31/18014398509481984), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521203/10141204801825835211973625643008), (-2983807608009/10141204801825835211973625643008)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779556717253051/633825300114114700748351602688), (-3534182686621/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945313906392733/19807040628566084398385987584), (-3975393302533/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890457661379217/2475880078570760549798248448), (-4223181598941/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772123239102717/154742504910672534362390528), (-2111211795225/77371252455336267181195264)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550426979119575/9671406556917033397649408), (-3957716787441/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314888082495347/151115727451828646838272), (-3462196922633/604462909807314587353088)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944515816900607/37778931862957161709568), (-2812280128613/37778931862957161709568)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298467975797173/4722366482869645213696), (-4217099301215/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811361467001363/295147905179352825856), (-5796365339161/590295810358705651712)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825065295495787/73786976294838206464), (-3621118905253/36893488147419103232)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824442480456857/9223372036854775808), (-2035773077625/2305843009213693952)), (211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797843040235195/576460752303423488), (-8137561846595/1152921504606846976)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196062943356817/144115188075855872), (-1778536579497/36028797018963968)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((373462417053535/9007199254740992), (-5329391289705/18014398509481984)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492003800901913/9007199254740992), (-6650861004441/4503599627370496)), (347/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116691428715247/2251799813685248), (-6634552241793/1125899906842624)), (87/562949953421312), by norm_num⟩
  | 1 => ⟨((1112056425730179/1125899906842624), (-4955543023717/281474976710656)), (263/562949953421312), by norm_num⟩
  | 0 => ⟨((274522837632735/281474976710656), (-4914845484643/140737488355328)), (531/562949953421312), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((274522837632735/281474976710656), (-4914845484643/140737488355328)), (2025606395530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((534798271853115/562949953421312), (-76695262633315/1125899906842624)), (2147/1125899906842624), by norm_num⟩
  | 2 => ⟨((252721089166279/281474976710656), (-36429964747613/281474976710656)), (4373/1125899906842624), by norm_num⟩
  | 3 => ⟨((444379158024887/562949953421312), (-261667888972451/1125899906842624)), (4493/562949953421312), by norm_num⟩
  | 4 => ⟨((80093849355959/140737488355328), (-826217360723031/2251799813685248)), (4591/281474976710656), by norm_num⟩
  | 5 => ⟨((426152978341837/2251799813685248), (-940402299321313/2251799813685248)), (68757/2251799813685248), by norm_num⟩
  | 6 => ⟨((-156041873560041/1125899906842624), (-711884312734571/4503599627370496)), (41727/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-53586800493/34359738368), (-9838201653/4294967296)), (1/17179869184), by norm_num⟩, 0, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile002Terms0
