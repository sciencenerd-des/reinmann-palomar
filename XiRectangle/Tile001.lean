/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile001Gamma
public import XiRectangle.Tile001Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile001
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((230874834417/274877906944), (-657957759/34359738368)), (447/274877906944), by norm_num⟩
  | 1 => ⟨((-23620840849/2199023255552), (311068955393/2199023255552)), (9325/2199023255552), by norm_num⟩
  | 2 => ⟨((384827767545/4398046511104), (-81869266413/2199023255552)), (6277/1099511627776), by norm_num⟩
  | 3 => ⟨((-79636110189/8796093022208), (232644802401/8796093022208)), (46505/8796093022208), by norm_num⟩
  | 4 => ⟨((165285347143/35184372088832), (-162176726713/17592186044416)), (133175/35184372088832), by norm_num⟩
  | 5 => ⟨((-6301034925/17592186044416), (269054308079/70368744177664)), (78717/35184372088832), by norm_num⟩
  | 6 => ⟨((-31273758023/281474976710656), (-376925808951/281474976710656)), (162455/140737488355328), by norm_num⟩
  | 7 => ⟨((22088558055/140737488355328), (258545767343/562949953421312)), (307049/562949953421312), by norm_num⟩
  | 8 => ⟨((-102241318887/1125899906842624), (-327685275973/2251799813685248)), (549419/2251799813685248), by norm_num⟩
  | 9 => ⟨((12204475233/281474976710656), (24083963431/562949953421312)), (472675/4503599627370496), by norm_num⟩
  | 10 => ⟨((-332174917631/18014398509481984), (-25140411803/2251799813685248)), (392035/9007199254740992), by norm_num⟩
  | 11 => ⟨((32720871547/4503599627370496), (83728456095/36028797018963968)), (625519/36028797018963968), by norm_num⟩
  | 12 => ⟨((-193874399361/72057594037927936), (-902245995/4503599627370496)), (958375/144115188075855872), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile001Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((56824062413/68719476736), (49223835747/137438953472)), (16687/274877906944), by norm_num⟩
  | 1 => ⟨((18755036685/34359738368), (1742114913/17179869184)), (17053/274877906944), by norm_num⟩
  | 2 => ⟨((665884673/8589934592), (-156553305/17179869184)), (277451/4398046511104), by norm_num⟩
  | 3 => ⟨((-84322937/17179869184), (-10362997/8589934592)), (4463789/70368744177664), by norm_num⟩
  | 4 => ⟨((-14757551/34359738368), (12257259/34359738368)), (17699507/281474976710656), by norm_num⟩
  | 5 => ⟨((3820983/34359738368), (-864397/34359738368)), (139498901/2251799813685248), by norm_num⟩
  | 6 => ⟨((-505805/68719476736), (-81671/34359738368)), (1101573287/18014398509481984), by norm_num⟩
  | 7 => ⟨((-57463/137438953472), (22677/34359738368)), (8727651637/144115188075855872), by norm_num⟩
  | 8 => ⟨((34473/274877906944), (-3831/68719476736)), (138879062857/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-11649/1099511627776), (-13/137438953472)), (138556101449/2305843009213693952), by norm_num⟩
  | 10 => ⟨((307/2199023255552), (299/549755813888)), (138419786569/2305843009213693952), by norm_num⟩
  | 11 => ⟨((147/2199023255552), (-561/8796093022208)), (138372338505/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-293/35184372088832), (55/17592186044416)), (138356806473/2305843009213693952), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile001Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/640))
  have he : value ((3/4), (423/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-314660955039/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((-235995716279/549755813888), (-207971224971/549755813888)), (1/274877906944), by norm_num⟩
  | 1 => ⟨((-314660955039/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((340558787929343/562949953421312), (-541406612805275/2251799813685248)), (7637/2251799813685248), by norm_num⟩
  | 1 => ⟨((-190355382047/549755813888), (151309650897/1099511627776)), (5/1099511627776), by norm_num⟩
  | 2 => ⟨((108952747381/1099511627776), (-21651084925/549755813888)), (5/2199023255552), by norm_num⟩
  | 3 => ⟨((-166295288097/8796093022208), (132184767865/17592186044416)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((190363186161/70368744177664), (-151315854229/140737488355328)), (7/70368744177664), by norm_num⟩
  | 5 => ⟨((-348663085383/1125899906842624), (138572624431/1125899906842624)), (15/1125899906842624), by norm_num⟩
  | 6 => ⟨((266083369287/9007199254740992), (-52876074849/4503599627370496)), (13/9007199254740992), by norm_num⟩
  | 7 => ⟨((-348106954229/144115188075855872), (138351595717/144115188075855872)), (5/36028797018963968), by norm_num⟩
  | 8 => ⟨((199244216989/1152921504606846976), (-39593801593/576460752303423488)), (13/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-101369248787/9223372036854775808), (80576369739/18446744073709551616)), (15/18446744073709551616), by norm_num⟩
  | 10 => ⟨((371329307497/590295810358705651712), (-73790542827/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-77285773779/2361183241434822606848), (7679112697/590295810358705651712)), (27/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((235923559989/151115727451828646838272), (-46882718939/75557863725914323419136)), (11/75557863725914323419136), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98963536885819/633825300114114700748351602688), (-492774671571/10141204801825835211973625643008)), (3/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222663595969275/79228162514264337593543950336), (-584756767783/633825300114114700748351602688)), (7/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892599071002539/39614081257132168796771975168), (-164456433533/9903520314283042199192993792)), (7/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946276194855345/1237940039285380274899124224), (-349454601363/1237940039285380274899124224)), (1/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((443554566742545/38685626227668133590597632), (-21839835453/4835703278458516698824704)), (1/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552391385765509/9671406556917033397649408), (-327579221441/4835703278458516698824704)), (7/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261271503550473/604462909807314587353088), (-573227018823/604462909807314587353088)), (3/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472956471518457/18889465931478580854784), (-465712624897/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300564185256137/4722366482869645213696), (-698508867795/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 9 => ⟨((812803033181253/295147905179352825856), (-960352088201/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828670475622179/73786976294838206464), (-1200293716731/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 7 => ⟨((57140626375579/288230376151711744), (-1350129162987/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599745809417859/1152921504606846976), (-1349877611699/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199617636043381/144115188075855872), (-590429980983/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((187398318933655/4503599627370496), (-1770724163721/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 3 => ⟨((374670836887807/2251799813685248), (-2212415354931/9007199254740992)), (11/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123383569703523/2251799813685248), (-4421862216297/4503599627370496)), (11/1125899906842624), by norm_num⟩
  | 1 => ⟨((1122125880130301/1125899906842624), (-6625375784581/2251799813685248)), (65/2251799813685248), by norm_num⟩
  | 0 => ⟨((559176888437729/562949953421312), (-6610551784843/1125899906842624)), (65/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((559176888437729/562949953421312), (-6610551784843/1125899906842624)), (247959617232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2221638821099073/2251799813685248), (-26264983275617/2251799813685248)), (261/2251799813685248), by norm_num⟩
  | 2 => ⟨((1095787727682487/1125899906842624), (-25913185588701/1125899906842624)), (261/1125899906842624), by norm_num⟩
  | 3 => ⟨((2131768985251259/2251799813685248), (-100880551035435/2251799813685248)), (1041/2251799813685248), by norm_num⟩
  | 4 => ⟨((2013616882524425/2251799813685248), (-23875793554717/281474976710656)), (2065/2251799813685248), by norm_num⟩
  | 5 => ⟨((892212864576939/1125899906842624), (-341605506445191/2251799813685248)), (1011/562949953421312), by norm_num⟩
  | 6 => ⟨((340558787929343/562949953421312), (-541406612805275/2251799813685248)), (7637/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-235995716279/549755813888), (-207971224971/549755813888)), (1/274877906944), by norm_num⟩, 0, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((276806163445/549755813888), (-58694164011/274877906944)), (759/549755813888), by norm_num⟩
  | 1 => ⟨((-286617452765/1099511627776), (231308734069/1099511627776)), (4813/1099511627776), by norm_num⟩
  | 2 => ⟨((243452740253/2199023255552), (-4432227441/34359738368)), (3907/549755813888), by norm_num⟩
  | 3 => ⟨((-78109840811/2199023255552), (282454316989/4398046511104)), (17293/2199023255552), by norm_num⟩
  | 4 => ⟨((9583966411/1099511627776), (-245897587585/8796093022208)), (7331/1099511627776), by norm_num⟩
  | 5 => ⟨((-17945151765/17592186044416), (389838642441/35184372088832)), (81325/17592186044416), by norm_num⟩
  | 6 => ⟨((-17918531657/35184372088832), (-286645966635/70368744177664)), (96609/35184372088832), by norm_num⟩
  | 7 => ⟨((141984633609/281474976710656), (394005513167/281474976710656)), (408733/281474976710656), by norm_num⟩
  | 8 => ⟨((-81247363167/281474976710656), (-126313624327/281474976710656)), (3105/4398046511104), by norm_num⟩
  | 9 => ⟨((1200449705/8796093022208), (37269970373/281474976710656)), (90959/281474976710656), by norm_num⟩
  | 10 => ⟨((-65243590485/1125899906842624), (-156094133783/4503599627370496)), (636293/4503599627370496), by norm_num⟩
  | 11 => ⟨((205505203141/9007199254740992), (129929312459/18014398509481984)), (1069801/18014398509481984), by norm_num⟩
  | 12 => ⟨((-9511901551/1125899906842624), (-22025865797/36028797018963968)), (108255/4503599627370496), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((541866832543/1099511627776), (1034996847/274877906944)), (49661/1099511627776), by norm_num⟩
  | 1 => ⟨((49168135057/8796093022208), (265667285271/17592186044416)), (696307/8796093022208), by norm_num⟩
  | 2 => ⟨((394384758373/35184372088832), (8504224653/35184372088832)), (3531949/35184372088832), by norm_num⟩
  | 3 => ⟨((66594887987/562949953421312), (364367977879/1125899906842624)), (124337139/1125899906842624), by norm_num⟩
  | 4 => ⟨((267484821623/2251799813685248), (4567979783/1125899906842624)), (252515843/2251799813685248), by norm_num⟩
  | 5 => ⟨((84984306135/72057594037927936), (58795923469/18014398509481984)), (7859329761/72057594037927936), by norm_num⟩
  | 6 => ⟨((227878293647/288230376151711744), (20851109055/576460752303423488)), (30162812733/288230376151711744), by norm_num⟩
  | 7 => ⟨((17151046995/2305843009213693952), (24013083199/1152921504606846976)), (464793582257/4611686018427387904), by norm_num⟩
  | 8 => ⟨((17298494385/4611686018427387904), (472692543/2305843009213693952)), (452521302099/4611686018427387904), by norm_num⟩
  | 9 => ⟨((145718251/4611686018427387904), (455498147/4611686018427387904)), (111332526359/1152921504606846976), by norm_num⟩
  | 10 => ⟨((16863137/1152921504606846976), (-1068849/1152921504606846976)), (441549124759/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-1318357/4611686018427387904), (5593077/4611686018427387904)), (219858868773/2305843009213693952), by norm_num⟩
  | 12 => ⟨((824867/4611686018427387904), (-1848103/4611686018427387904)), (438884025015/4611686018427387904), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((529166829/1073741824), (1010739/268435456)), (1/10000000), by norm_num⟩
  | 1 => ⟨((3000985/536870912), (4053761/268435456)), (1/10000000), by norm_num⟩
  | 2 => ⟨((3008917/268435456), (32441/134217728)), (1/5000000), by norm_num⟩
  | 3 => ⟨((31755/268435456), (10859/33554432)), (1/5000000), by norm_num⟩
  | 4 => ⟨((127547/1073741824), (1089/268435456)), (1/5000000), by norm_num⟩
  | 5 => ⟨((633/536870912), (219/67108864)), (1/5000000), by norm_num⟩
  | 6 => ⟨((849/1073741824), (39/1073741824)), (1/5000000), by norm_num⟩
  | 7 => ⟨((1/134217728), (11/536870912)), (1/5000000), by norm_num⟩
  | 8 => ⟨((1/268435456), 0), (1/5000000), by norm_num⟩
  | 9 => ⟨(0, 0), (1/5000000), by norm_num⟩
  | 10 => ⟨(0, 0), (1/5000000), by norm_num⟩
  | 11 => ⟨(0, 0), (1/5000000), by norm_num⟩
  | 12 => ⟨(0, 0), (1/5000000), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem xiJet_sound : Sound xiJet xiCompleted c := by
  apply sound_round (xi_sound hc S_xiProduct)
  intro k
  fin_cases k <;> norm_num [xiJet,J_xiProduct,size]

set_option maxHeartbeats 5000000 in
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨1,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨1,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(8916751/134217728)) (L:=(270941323945/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile001
