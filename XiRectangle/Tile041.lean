/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile041Gamma
public import XiRectangle.Tile041Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile041
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-73174195/8796093022208), (1925639831/8796093022208)), (455/2199023255552), by norm_num⟩
  | 1 => ⟨((-734011713/4398046511104), (912978663/4398046511104)), (239/549755813888), by norm_num⟩
  | 2 => ⟨((-672295261/4398046511104), (363921131/8796093022208)), (1033/2199023255552), by norm_num⟩
  | 3 => ⟨((-506167363/8796093022208), (-372098787/17592186044416)), (6091/17592186044416), by norm_num⟩
  | 4 => ⟨((-708684483/70368744177664), (-497906413/35184372088832)), (1713/8796093022208), by norm_num⟩
  | 5 => ⟨((-42994021/281474976710656), (-1079897423/281474976710656)), (25045/281474976710656), by norm_num⟩
  | 6 => ⟨((190338119/562949953421312), (-677933981/1125899906842624)), (38641/1125899906842624), by norm_num⟩
  | 7 => ⟨((201196669/2251799813685248), (-484305599/9007199254740992)), (51771/4503599627370496), by norm_num⟩
  | 8 => ⟨((1954295187/144115188075855872), (-126374783/144115188075855872)), (246839/72057594037927936), by norm_num⟩
  | 9 => ⟨((843297943/576460752303423488), (326281917/576460752303423488)), (541159/576460752303423488), by norm_num⟩
  | 10 => ⟨((1095598167/9223372036854775808), (261584055/2305843009213693952)), (296265/1152921504606846976), by norm_num⟩
  | 11 => ⟨((506396331/73786976294838206464), (528168947/36893488147419103232)), (1625417/18446744073709551616), by norm_num⟩
  | 12 => ⟨((182719963/1180591620717411303424), (838077841/590295810358705651712)), (58890955/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile041Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((546491907/536870912), (1173926025/536870912)), (4647/536870912), by norm_num⟩
  | 1 => ⟨((-154415543/67108864), (1196620765/134217728)), (2881/134217728), by norm_num⟩
  | 2 => ⟨((78794119/33554432), (-217796797/67108864)), (7781/268435456), by norm_num⟩
  | 3 => ⟨((-15900543/16777216), (5998039/8388608)), (29377/1073741824), by norm_num⟩
  | 4 => ⟨((4420573/16777216), (-5976581/67108864)), (43009/2147483648), by norm_num⟩
  | 5 => ⟨((-7349129/134217728), (-46917/67108864)), (205575/17179869184), by norm_num⟩
  | 6 => ⟨((1177547/134217728), (225941/67108864)), (835127/137438953472), by norm_num⟩
  | 7 => ⟨((-4489/4194304), (-516635/536870912)), (742509/274877906944), by norm_num⟩
  | 8 => ⟨((11975/134217728), (192207/1073741824)), (4765387/4398046511104), by norm_num⟩
  | 9 => ⟨((-2133/1073741824), (-54651/2147483648)), (29338797/70368744177664), by norm_num⟩
  | 10 => ⟨((-8001/8589934592), (24679/8589934592)), (48411315/281474976710656), by norm_num⟩
  | 11 => ⟨((7473/34359738368), (-8689/34359738368)), (207590805/2251799813685248), by norm_num⟩
  | 12 => ⟨((-4259/137438953472), (2107/137438953472)), (1234742439/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile041Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/16), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((11/16), (17907/1280))
  have he : value ((11/16), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-52814797/134217728), (-1074721093/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-307286089/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-58003607935103/562949953421312), (-1501447906127037/2251799813685248)), (62012989/2251799813685248), by norm_num⟩
  | 1 => ⟨((253290037/4294967296), (409782479/1073741824)), (35/2147483648), by norm_num⟩
  | 2 => ⟨((-72487169/4294967296), (-938180501/8589934592)), (21/4294967296), by norm_num⟩
  | 3 => ⟨((221275277/68719476736), (1431951011/68719476736)), (33/34359738368), by norm_num⟩
  | 4 => ⟨((-253300423/549755813888), (-819598559/274877906944)), (39/274877906944), by norm_num⟩
  | 5 => ⟨((57992113/1099511627776), (187643793/549755813888)), (37/2199023255552), by norm_num⟩
  | 6 => ⟨((-22128435/4398046511104), (-1145607775/35184372088832)), (29/17592186044416), by norm_num⟩
  | 7 => ⟨((115799227/281474976710656), (93672247/35184372088832)), (39/281474976710656), by norm_num⟩
  | 8 => ⟨((-33139709/1125899906842624), (-857835365/4503599627370496)), (23/2251799813685248), by norm_num⟩
  | 9 => ⟨((67441805/36028797018963968), (218219951/18014398509481984)), (3/4503599627370496), by norm_num⟩
  | 10 => ⟨((-247048479/2305843009213693952), (-799369279/1152921504606846976)), (45/1152921504606846976), by norm_num⟩
  | 11 => ⟨((102837737/18446744073709551616), (1330999133/36893488147419103232)), (77/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-39240477/147573952589676412928), (-253939081/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583463188246237/10141204801825835211973625643008), (-17545678399/79228162514264337593543950336)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890680233117239/316912650057057350374175801344), (-2665217056579/633825300114114700748351602688)), (5779/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946328504325007/19807040628566084398385987584), (-374781992273/4951760157141521099596496896)), (13005/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892613679074095/2475880078570760549798248448), (-3185518166113/2475880078570760549798248448)), (3455/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774279253298541/154742504910672534362390528), (-398171656403/19342813113834066795298816)), (13823/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552448238512333/9671406556917033397649408), (-186633337583/604462909807314587353088)), (6481/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261320927811481/604462909807314587353088), (-1306356324331/302231454903657293676544)), (22689/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945952798521087/37778931862957161709568), (-4245369040207/75557863725914323419136)), (2305/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((325155860137795/1180591620717411303424), (-3183773774501/4722366482869645213696)), (13835/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((406421671169665/147573952589676412928), (-2188638791803/295147905179352825856)), (19031/295147905179352825856), by norm_num⟩
  | 8 => ⟨((28574530660151/1152921504606846976), (-5470979556407/73786976294838206464)), (2975/4611686018427387904), by norm_num⟩
  | 7 => ⟨((914305099175363/4611686018427387904), (-3077001206505/4611686018427387904)), (53581/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399963438584343/288230376151711744), (-6152939481807/1152921504606846976)), (53621/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18745462551243/2251799813685248), (-1345656237171/36028797018963968)), (11741/36028797018963968), by norm_num⟩
  | 4 => ⟨((1499319535740835/36028797018963968), (-8071539978983/36028797018963968)), (70535/36028797018963968), by norm_num⟩
  | 3 => ⟨((374710223030829/2251799813685248), (-630326384057/562949953421312)), (44163/4503599627370496), by norm_num⟩
  | 2 => ⟨((280882024285637/562949953421312), (-629931457205/140737488355328)), (88563/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122310168830199/1125899906842624), (-15102506923287/1125899906842624)), (133435/1125899906842624), by norm_num⟩
  | 0 => ⟨((34956018349079/35184372088832), (-30141316410237/1125899906842624)), (269241/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((34956018349079/35184372088832), (-30141316410237/1125899906842624)), (1027072910789107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1110525784325057/1125899906842624), (-29945693128799/562949953421312)), (137351/281474976710656), by norm_num⟩
  | 2 => ⟨((546087859155853/562949953421312), (-118147143087615/1125899906842624)), (1142255/1125899906842624), by norm_num⟩
  | 3 => ⟨((1047063815429117/1125899906842624), (-114608270312459/562949953421312)), (2455809/1125899906842624), by norm_num⟩
  | 4 => ⟨((927082775956589/1125899906842624), (-213166680383905/562949953421312)), (2783819/562949953421312), by norm_num⟩
  | 5 => ⟨((601938356023445/1125899906842624), (-702098495934541/1125899906842624)), (6692719/562949953421312), by norm_num⟩
  | 6 => ⟨((-58003607935103/562949953421312), (-1501447906127037/2251799813685248)), (62012989/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-52814797/134217728), (-1074721093/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1291511503/8796093022208), (-149617647/8796093022208)), (1457/8796093022208), by norm_num⟩
  | 1 => ⟨((314774025/4398046511104), (876342173/8796093022208)), (1935/4398046511104), by norm_num⟩
  | 2 => ⟨((-381375341/17592186044416), (763930173/17592186044416)), (10413/17592186044416), by norm_num⟩
  | 3 => ⟨((-1699829579/140737488355328), (-3291851/35184372088832)), (76097/140737488355328), by norm_num⟩
  | 4 => ⟨((-465776645/562949953421312), (-1082922067/562949953421312)), (105883/281474976710656), by norm_num⟩
  | 5 => ⟨((863942985/4503599627370496), (-50770185/281474976710656)), (954649/4503599627370496), by norm_num⟩
  | 6 => ⟨((360201285/18014398509481984), (486478235/36028797018963968)), (3625445/36028797018963968), by norm_num⟩
  | 7 => ⟨((-600530169/576460752303423488), (371763685/288230376151711744)), (23835023/576460752303423488), by norm_num⟩
  | 8 => ⟨((-195679801/4611686018427387904), (-295286355/2305843009213693952)), (4327057/288230376151711744), by norm_num⟩
  | 9 => ⟨((1155702743/73786976294838206464), (47761811/73786976294838206464)), (362135009/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-88773151/295147905179352825856), (867792353/590295810358705651712)), (437455441/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-510731567/4722366482869645213696), (-7716771/147573952589676412928)), (2073301617/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((67348783/9444732965739290427392), (-62468929/9444732965739290427392)), (1418181681/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((102613195/549755813888), (667932505/2199023255552)), (4287/2199023255552), by norm_num⟩
  | 1 => ⟨((-364149743/1099511627776), (441480719/274877906944)), (4545/549755813888), by norm_num⟩
  | 2 => ⟨((-483982125/549755813888), (-60917639/549755813888)), (18413/1099511627776), by norm_num⟩
  | 3 => ⟨((132398407/8796093022208), (-1732135577/8796093022208)), (194009/8796093022208), by norm_num⟩
  | 4 => ⟨((44238603/2199023255552), (20299057/70368744177664)), (1513533/70368744177664), by norm_num⟩
  | 5 => ⟨((346430519/2251799813685248), (1412466751/4503599627370496)), (9377145/562949953421312), by norm_num⟩
  | 6 => ⟨((1231979281/9007199254740992), (70739879/4503599627370496)), (96444207/9007199254740992), by norm_num⟩
  | 7 => ⟨((9134083/144115188075855872), (433183921/36028797018963968)), (849409389/144115188075855872), by norm_num⟩
  | 8 => ⟨((22469535/576460752303423488), (28305583/288230376151711744)), (1640306487/576460752303423488), by norm_num⟩
  | 9 => ⟨((-628539/144115188075855872), (67998289/1152921504606846976)), (1419478431/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-5769507/2305843009213693952), (509337/2305843009213693952)), (141373671/288230376151711744), by norm_num⟩
  | 11 => ⟨((-245511/4611686018427387904), (133655/1152921504606846976)), (436119105/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-410093/18446744073709551616), (-350617/18446744073709551616)), (726081971/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6263/33554432), (326139/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-355615/1073741824), (862267/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-472639/536870912), (-29745/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((8081/536870912), (-105721/536870912)), (1/10000000), by norm_num⟩
  | 4 => ⟨((21601/1073741824), (155/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((165/1073741824), (337/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((147/1073741824), (17/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨(0, (13/1073741824)), (1/10000000), by norm_num⟩
  | 8 => ⟨(0, 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨41,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨41,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/262144)) (K:=(2361277/1073741824)) (L:=(24498981/68719476736)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile041
