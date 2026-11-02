/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile043Gamma
public import XiRectangle.Tile043Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile043
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-199572833/4398046511104), (569853151/2199023255552)), (985/4398046511104), by norm_num⟩
  | 1 => ⟨((-1013984733/4398046511104), (60603347/274877906944)), (2035/4398046511104), by norm_num⟩
  | 2 => ⟨((-824012573/4398046511104), (28835809/1099511627776)), (4369/8796093022208), by norm_num⟩
  | 3 => ⟨((-286325595/4398046511104), (-583979537/17592186044416)), (6429/17592186044416), by norm_num⟩
  | 4 => ⟨((-352339115/35184372088832), (-636067433/35184372088832)), (905/4398046511104), by norm_num⟩
  | 5 => ⟨((84113803/281474976710656), (-1281804263/281474976710656)), (26523/281474976710656), by norm_num⟩
  | 6 => ⟨((264344245/562949953421312), (-757974419/1125899906842624)), (41037/1125899906842624), by norm_num⟩
  | 7 => ⟨((1005550169/9007199254740992), (-488837551/9007199254740992)), (110253/9007199254740992), by norm_num⟩
  | 8 => ⟨((1169115989/72057594037927936), (19757243/72057594037927936)), (131635/36028797018963968), by norm_num⟩
  | 9 => ⟨((30607915/18014398509481984), (116526415/144115188075855872)), (576713/576460752303423488), by norm_num⟩
  | 10 => ⟨((76810837/576460752303423488), (675597649/4611686018427387904)), (626961/2305843009213693952), by norm_num⟩
  | 11 => ⟨((8220875/1152921504606846976), (329327911/18446744073709551616)), (6743195/73786976294838206464), by norm_num⟩
  | 12 => ⟨((11407833/147573952589676412928), (2046788321/1180591620717411303424)), (59666819/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile043Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((178002245/268435456), (503151879/134217728)), (1479/268435456), by norm_num⟩
  | 1 => ⟨((-101583673/67108864), (65192483/8388608)), (109/8388608), by norm_num⟩
  | 2 => ⟨((250620461/134217728), (-192065533/67108864)), (4541/268435456), by norm_num⟩
  | 3 => ⟨((-103115397/134217728), (43512545/67108864)), (16841/1073741824), by norm_num⟩
  | 4 => ⟨((29063633/134217728), (-11830679/134217728)), (24337/2147483648), by norm_num⟩
  | 5 => ⟨((-6126067/134217728), (655105/268435456)), (115143/17179869184), by norm_num⟩
  | 6 => ⟨((250155/33554432), (19013/8388608)), (467511/137438953472), by norm_num⟩
  | 7 => ⟨((-504441/536870912), (-777187/1073741824)), (1669555/1099511627776), by norm_num⟩
  | 8 => ⟨((181705/2147483648), (301353/2147483648)), (2737867/4398046511104), by norm_num⟩
  | 9 => ⟨((-3601/1073741824), (-44079/2147483648)), (17951917/70368744177664), by norm_num⟩
  | 10 => ⟨((-9425/17179869184), (40977/17179869184)), (34042547/281474976710656), by norm_num⟩
  | 11 => ⟨((5373/34359738368), (-7517/34359738368)), (174527893/2251799813685248), by norm_num⟩
  | 12 => ⟨((-3251/137438953472), (249/17179869184)), (1164749991/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile043Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (17907/1280))
  have he : value ((7/8), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4201177/8388608), (-1074721093/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-52101137977583/562949953421312), (-337164994162109/562949953421312)), (55796161/2251799813685248), by norm_num⟩
  | 1 => ⟨((227515143/4294967296), (1472331411/4294967296)), (63/4294967296), by norm_num⟩
  | 2 => ⟨((-32555423/2147483648), (-1685421769/17179869184)), (75/17179869184), by norm_num⟩
  | 3 => ⟨((198758217/68719476736), (1286235113/68719476736)), (59/68719476736), by norm_num⟩
  | 4 => ⟨((-227524471/549755813888), (-1472391775/549755813888)), (35/274877906944), by norm_num⟩
  | 5 => ⟨((208363249/4398046511104), (1348392695/4398046511104)), (67/4398046511104), by norm_num⟩
  | 6 => ⟨((-39753273/8796093022208), (-514515139/17592186044416)), (53/35184372088832), by norm_num⟩
  | 7 => ⟨((208030901/562949953421312), (673120979/281474976710656)), (9/70368744177664), by norm_num⟩
  | 8 => ⟨((-119069595/4503599627370496), (-1541083403/9007199254740992)), (85/9007199254740992), by norm_num⟩
  | 9 => ⟨((121157799/72057594037927936), (1568110425/144115188075855872)), (89/144115188075855872), by norm_num⟩
  | 10 => ⟨((-110954363/1152921504606846976), (-1436050295/2305843009213693952)), (21/576460752303423488), by norm_num⟩
  | 11 => ⟨((184745855/36893488147419103232), (1195556139/36893488147419103232)), (9/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-140989401/590295810358705651712), (-456196281/295147905179352825856)), (7/73786976294838206464), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583323394017219/10141204801825835211973625643008), (-17545678399/79228162514264337593543950336)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890597291339075/316912650057057350374175801344), (-1332373156471/316912650057057350374175801344)), (5779/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((946235199194171/19807040628566084398385987584), (-374712193351/4951760157141521099596496896)), (13005/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473103853717255/618970019642690137449562112), (-3184890016485/2475880078570760549798248448)), (3455/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774080999451721/154742504910672534362390528), (-796176472069/38685626227668133590597632)), (13823/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((194032798318353/1208925819614629174706176), (-1492733045093/4835703278458516698824704)), (25923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261158318369059/604462909807314587353088), (-1306043549765/302231454903657293676544)), (22689/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891641377399067/75557863725914323419136), (-2122137219699/37778931862957161709568)), (2305/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1300425293956527/4722366482869645213696), (-3182884514677/4722366482869645213696)), (13835/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625414262630563/590295810358705651712), (-4375943874795/590295810358705651712)), (38061/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914214739524517/36893488147419103232), (-1367286500243/18446744073709551616)), (47599/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828227215874519/9223372036854775808), (-3075855455147/4611686018427387904)), (26791/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799735424230993/576460752303423488), (-3075181074459/576460752303423488)), (53621/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199374647082721/144115188075855872), (-5380048376127/144115188075855872)), (11741/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498817275003825/36028797018963968), (-4033516344903/18014398509481984)), (70535/36028797018963968), by norm_num⟩
  | 3 => ⟨((46819167857341/281474976710656), (-5039232320935/4503599627370496)), (44163/4503599627370496), by norm_num⟩
  | 2 => ⟨((561450518655785/1125899906842624), (-10070462451761/2251799813685248)), (88563/2251799813685248), by norm_num⟩
  | 1 => ⟨((280342685434719/281474976710656), (-7542821644045/562949953421312)), (33359/281474976710656), by norm_num⟩
  | 0 => ⟨((558359223271277/562949953421312), (-7522704071267/281474976710656)), (134621/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((558359223271277/562949953421312), (-7522704071267/281474976710656)), (513538362743186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1106807651417541/1125899906842624), (-59690864903421/1125899906842624)), (548485/1125899906842624), by norm_num⟩
  | 2 => ⟨((271218642629799/281474976710656), (-117357334507839/1125899906842624)), (568263/562949953421312), by norm_num⟩
  | 3 => ⟨((1033111453982039/1125899906842624), (-226162178534163/1125899906842624)), (1213579/562949953421312), by norm_num⟩
  | 4 => ⟨((451270108103669/562949953421312), (-415047084880581/1125899906842624)), (2714679/562949953421312), by norm_num⟩
  | 5 => ⟨((570490107779627/1125899906842624), (-332708692351553/562949953421312)), (6353721/562949953421312), by norm_num⟩
  | 6 => ⟨((-52101137977583/562949953421312), (-337164994162109/562949953421312)), (55796161/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-4201177/8388608), (-1074721093/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((1402138993/8796093022208), (14049167/4398046511104)), (715/4398046511104), by norm_num⟩
  | 1 => ⟨((273326987/4398046511104), (509518261/4398046511104)), (3733/8796093022208), by norm_num⟩
  | 2 => ⟨((-503736053/17592186044416), (377830633/8796093022208)), (1243/2199023255552), by norm_num⟩
  | 3 => ⟨((-1777306557/140737488355328), (-112440831/70368744177664)), (36193/70368744177664), by norm_num⟩
  | 4 => ⟨((-179367231/281474976710656), (-586973205/281474976710656)), (100591/281474976710656), by norm_num⟩
  | 5 => ⟨((480863123/2251799813685248), (-184958857/1125899906842624)), (907203/4503599627370496), by norm_num⟩
  | 6 => ⟨((669944615/36028797018963968), (542955437/36028797018963968)), (862427/9007199254740992), by norm_num⟩
  | 7 => ⟨((-156488621/144115188075855872), (633924895/576460752303423488)), (2840041/72057594037927936), by norm_num⟩
  | 8 => ⟨((-9563317/576460752303423488), (-1150179497/9223372036854775808)), (132231667/9223372036854775808), by norm_num⟩
  | 9 => ⟨((1099445039/73786976294838206464), (243032363/73786976294838206464)), (43285985/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-149576107/295147905179352825856), (397962853/295147905179352825856)), (836419387/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-431567539/4722366482869645213696), (-153654033/2361183241434822606848)), (1972675217/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((72716191/9444732965739290427392), (-44860575/9444732965739290427392)), (1328961839/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6440923/68719476736), (1318733491/2199023255552)), (3549/2199023255552), by norm_num⟩
  | 1 => ⟨((-181201609/274877906944), (848704699/549755813888)), (3561/549755813888), by norm_num⟩
  | 2 => ⟨((-953975265/1099511627776), (-243536119/1099511627776)), (6961/549755813888), by norm_num⟩
  | 3 => ⟨((8304655/274877906944), (-432309909/2199023255552)), (71799/4398046511104), by norm_num⟩
  | 4 => ⟨((1430860239/70368744177664), (41768007/70368744177664)), (276581/17592186044416), by norm_num⟩
  | 5 => ⟨((346543905/1125899906842624), (23941261/70368744177664)), (27213649/2251799813685248), by norm_num⟩
  | 6 => ⟨((1233014579/9007199254740992), (284793609/9007199254740992)), (69693075/9007199254740992), by norm_num⟩
  | 7 => ⟨((8443693/72057594037927936), (882323681/72057594037927936)), (153234985/36028797018963968), by norm_num⟩
  | 8 => ⟨((7941513/288230376151711744), (57223763/288230376151711744)), (74039995/36028797018963968), by norm_num⟩
  | 9 => ⟨((-1235957/144115188075855872), (136951241/2305843009213693952)), (64344101/72057594037927936), by norm_num⟩
  | 10 => ⟨((-2858225/1152921504606846976), (341587/576460752303423488)), (1661365839/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-119017/2305843009213693952), (303773/2305843009213693952)), (165704061/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-190029/9223372036854775808), (7521/2305843009213693952)), (148659185/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((100639/1073741824), (643913/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-707819/1073741824), (828813/536870912)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-29113/33554432), (-59457/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((4055/134217728), (-211089/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((21833/1073741824), (637/1073741824)), (1/10000000), by norm_num⟩
  | 5 => ⟨((165/536870912), (365/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((147/1073741824), (17/536870912)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨43,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨43,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/1048576)) (K:=(2783767/1073741824)) (L:=(667371651/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile043
