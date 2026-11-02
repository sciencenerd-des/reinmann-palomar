/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile020Gamma
public import XiRectangle.Tile020Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile020
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨20,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

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
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile020Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-896524111/536870912), (6745131617/536870912)), (415/536870912), by norm_num⟩
  | 1 => ⟨((2859168337/1073741824), (-1937480851/1073741824)), (945/536870912), by norm_num⟩
  | 2 => ⟨((-411553343/536870912), (85641495/268435456)), (5189/2147483648), by norm_num⟩
  | 3 => ⟨((107397119/536870912), (2553137/134217728)), (40167/17179869184), by norm_num⟩
  | 4 => ⟨((-17275421/536870912), (-1537563/67108864)), (242231/137438953472), by norm_num⟩
  | 5 => ⟨((721669/268435456), (3290087/536870912)), (300909/274877906944), by norm_num⟩
  | 6 => ⟨((139651/1073741824), (-1071597/1073741824)), (2614987/4398046511104), by norm_num⟩
  | 7 => ⟨((-183341/2147483648), (229839/2147483648)), (10516055/35184372088832), by norm_num⟩
  | 8 => ⟨((68801/4294967296), (-50909/8589934592)), (43528883/281474976710656), by norm_num⟩
  | 9 => ⟨((-16667/8589934592), (-395/1073741824)), (211129749/2251799813685248), by norm_num⟩
  | 10 => ⟨((10955/68719476736), (9749/68719476736)), (1274588327/18014398509481984), by norm_num⟩
  | 11 => ⟨((-1795/274877906944), (-2843/137438953472)), (4549161627/72057594037927936), by norm_num⟩
  | 12 => ⟨((-261/549755813888), (1115/549755813888)), (4384928411/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile020Zeta.zetaJet_sound

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

def J_negativeHalfLogPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2458288711/4294967296), 0), (1/8589934592), by norm_num⟩
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
theorem S_negativeHalfLogPi : Sound J_negativeHalfLogPi F_negativeHalfLogPi c := by
  apply sound_round (sound_scale (A_logpi hcre) S_logpi)
  intro k
  fin_cases k <;> norm_num [J_negativeHalfLogPi, J_logpi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_piArg : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-460929133/1073741824), (-5551315249/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-2458288711/4294967296), 0), (1/8589934592), by norm_num⟩
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
theorem S_piArg : Sound J_piArg F_piArg c := by
  apply sound_round (sound_mul (A_negativeHalfLogPi hcre) (A_variable hcre) S_negativeHalfLogPi S_variable)
  intro k
  fin_cases k <;> norm_num [J_piArg, J_negativeHalfLogPi, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_piPower : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((647720846472565/2251799813685248), (657507307077121/1125899906842624)), (3017991/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1414233037/8589934592), (-5742403141/17179869184)), (29/17179869184), by norm_num⟩
  | 2 => ⟨((1618914823/34359738368), (1643375123/17179869184)), (19/34359738368), by norm_num⟩
  | 3 => ⟨((-154435015/17179869184), (-5016588311/274877906944)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((2828582033/2199023255552), (1435659641/549755813888)), (39/2199023255552), by norm_num⟩
  | 5 => ⟨((-1295184955/8796093022208), (-2629507995/8796093022208)), (19/8796093022208), by norm_num⟩
  | 6 => ⟨((988424617/70368744177664), (2006717591/70368744177664)), (31/140737488355328), by norm_num⟩
  | 7 => ⟨((-2586238169/2251799813685248), (-2625313827/1125899906842624)), (43/2251799813685248), by norm_num⟩
  | 8 => ⟨((740136031/9007199254740992), (3005275197/18014398509481984)), (13/9007199254740992), by norm_num⟩
  | 9 => ⟨((-753116297/144115188075855872), (-764495185/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 10 => ⟨((344845893/1152921504606846976), (5600899109/9223372036854775808)), (27/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-2296758689/147573952589676412928), (-2331460581/73786976294838206464)), (47/147573952589676412928), by norm_num⟩
  | 12 => ⟨((876389437/1180591620717411303424), (3558523473/2361183241434822606848)), (19/1180591620717411303424), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583416590173537/10141204801825835211973625643008), (1449963206819/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781307373645553/633825300114114700748351602688), (860307811197/316912650057057350374175801344)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1892597417251773/39614081257132168796771975168), (7560998617/154742504910672534362390528)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1892550529350989/2475880078570760549798248448), (1028250640493/1237940039285380274899124224)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1774216290468129/154742504910672534362390528), (1028199817793/77371252455336267181195264)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552389409409867/9671406556917033397649408), (481941662845/2417851639229258349412352)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261269650872625/604462909807314587353088), (1686687803139/604462909807314587353088)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236477830524843/9444732965739290427392), (685166281919/18889465931478580854784)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1300561551524349/4722366482869645213696), (1027660795751/2361183241434822606848)), (1727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812801058137681/295147905179352825856), (1412889555509/295147905179352825856)), (2375/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828665045082027/73786976294838206464), (1765895852191/36893488147419103232)), (5939/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828493257087923/9223372036854775808), (3972671302747/9223372036854775808)), (1671/2305843009213693952), by norm_num⟩
  | 6 => ⟨((799869087916175/576460752303423488), (3971928180309/1152921504606846976)), (209/36028797018963968), by norm_num⟩
  | 5 => ⟨((1199610004597313/144115188075855872), (3474600916191/144115188075855872)), (5855/144115188075855872), by norm_num⟩
  | 4 => ⟨((93698325078299/2251799813685248), (5210228319683/36028797018963968)), (4395/18014398509481984), by norm_num⟩
  | 3 => ⟨((749331665927933/4503599627370496), (3254928135043/4503599627370496)), (1375/1125899906842624), by norm_num⟩
  | 2 => ⟨((1123358566937761/2251799813685248), (3252730006175/1125899906842624)), (11019/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122075925167287/1125899906842624), (9747190422167/1125899906842624)), (259/17592186044416), by norm_num⟩
  | 0 => ⟨((1118204164884439/1125899906842624), (19450328907433/1125899906842624)), (33341/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1118204164884439/1125899906842624), (19450328907433/1125899906842624)), (127185825828170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((277556253329769/281474976710656), (38634764352465/1125899906842624)), (67379/1125899906842624), by norm_num⟩
  | 2 => ⟨((1093442612172499/1125899906842624), (2381055451017/35184372088832)), (137507/1125899906842624), by norm_num⟩
  | 3 => ⟨((1056764680076175/1125899906842624), (147994540616741/1125899906842624)), (142849/562949953421312), by norm_num⟩
  | 4 => ⟨((243105359177629/281474976710656), (138907022211639/562949953421312)), (305709/562949953421312), by norm_num⟩
  | 5 => ⟨((192828599153777/281474976710656), (479886943012607/1125899906842624)), (1357877/1125899906842624), by norm_num⟩
  | 6 => ⟨((647720846472565/2251799813685248), (657507307077121/1125899906842624)), (3017991/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-460929133/1073741824), (-5551315249/1073741824)), (1/536870912), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem piPowerValue_checks : CertifiedScalarExp.Checks piPowerValue := by
  constructor
  · norm_num [piPowerValue, CertifiedScalarExp.reduced, piPowerValuePoly, piPowerValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        piPowerValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, piPowerValueSquares, piPowerValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, piPowerValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_piPower : Sound J_piPower F_piPower c := by
  apply exp_sound (A_piArg hcre) S_piArg piPowerValue piPowerValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue,J_piArg]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_piPower,J_piArg,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_piGamma : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19821297/549755813888), (-5589195641/1099511627776)), (117/137438953472), by norm_num⟩
  | 1 => ⟨((3845338293/1099511627776), (-136009813/137438953472)), (2711/1099511627776), by norm_num⟩
  | 2 => ⟨((590113935/1099511627776), (2387932247/2199023255552)), (3895/1099511627776), by norm_num⟩
  | 3 => ⟨((-3855482567/17592186044416), (1068426413/8796093022208)), (59819/17592186044416), by norm_num⟩
  | 4 => ⟨((-1754371291/140737488355328), (-5051967299/140737488355328)), (173281/70368744177664), by norm_num⟩
  | 5 => ⟨((5977166493/1125899906842624), (456757313/1125899906842624)), (1618935/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1795661537/4503599627370496), (3036690373/4503599627370496)), (1589271/2251799813685248), by norm_num⟩
  | 7 => ⟨((-284089887/4503599627370496), (-3193006893/36028797018963968)), (2698975/9007199254740992), by norm_num⟩
  | 8 => ⟨((1976682167/144115188075855872), (-722276513/288230376151711744)), (32389905/288230376151711744), by norm_num⟩
  | 9 => ⟨((-1102992025/2305843009213693952), (3817783101/2305843009213693952)), (43630565/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-175786007/1152921504606846976), (-2580372477/18446744073709551616)), (53543545/4611686018427387904), by norm_num⟩
  | 11 => ⟨((1649864525/73786976294838206464), (-1281538039/147573952589676412928)), (487321515/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-549096569/2361183241434822606848), (1587394129/590295810358705651712)), (533327693/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4392978825/68719476736), (138052685/17179869184)), (553/34359738368), by norm_num⟩
  | 1 => ⟨((-367722931/137438953472), (4414697013/137438953472)), (3531/68719476736), by norm_num⟩
  | 2 => ⟨((-5896560333/1099511627776), (-35947033/274877906944)), (11529/137438953472), by norm_num⟩
  | 3 => ⟨((-831799261/17592186044416), (-6205408085/35184372088832)), (1636389/17592186044416), by norm_num⟩
  | 4 => ⟨((-6661729901/140737488355328), (-846487097/140737488355328)), (11082213/140737488355328), by norm_num⟩
  | 5 => ⟨((-35140743/281474976710656), (-5449278145/1125899906842624)), (61132393/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1483656717/18014398509481984), (-31916035/562949953421312)), (573668261/18014398509481984), by norm_num⟩
  | 7 => ⟨((109925713/72057594037927936), (-2345335305/72057594037927936)), (74054287/4503599627370496), by norm_num⟩
  | 8 => ⟨((440083943/576460752303423488), (-38290689/144115188075855872)), (1118524863/144115188075855872), by norm_num⟩
  | 9 => ⟨((2310443/144115188075855872), (-274493255/2305843009213693952)), (4096766601/1152921504606846976), by norm_num⟩
  | 10 => ⟨((14093549/2305843009213693952), (-2016405/2305843009213693952)), (8070374497/4611686018427387904), by norm_num⟩
  | 11 => ⟨((1102201/4611686018427387904), (-123635/576460752303423488)), (4862104045/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-9087/576460752303423488), (43829/1152921504606846976)), (7471361633/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((34320147/536870912), (2157073/268435456)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-2872835/1073741824), (8622455/268435456)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-719795/134217728), (-70209/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-50769/1073741824), (-94687/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-50825/1073741824), (-3229/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-67/536870912), (-5197/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-11/134217728), (-61/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((1/536870912), (-35/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨((1/1073741824), 0), (1/10000000), by norm_num⟩
  | 9 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 10 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 11 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | 12 => ⟨(0, 0), (1/10000000), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨20,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨20,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(41063773/536870912)) (L:=(35420400469/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile020
