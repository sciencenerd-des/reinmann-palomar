/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile035Gamma
public import XiRectangle.Tile035Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile035
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((173627427/1099511627776), (145059169/549755813888)), (407/1099511627776), by norm_num⟩
  | 1 => ⟨((-177746615/4398046511104), (806331589/2199023255552)), (3331/4398046511104), by norm_num⟩
  | 2 => ⟨((-323381971/2199023255552), (347996987/2199023255552)), (3589/4398046511104), by norm_num⟩
  | 3 => ⟨((-709201667/8796093022208), (282221379/17592186044416)), (5325/8796093022208), by norm_num⟩
  | 4 => ⟨((-1472905873/70368744177664), (-642940309/70368744177664)), (24217/70368744177664), by norm_num⟩
  | 5 => ⟨((-188855385/70368744177664), (-1166811471/281474976710656)), (44727/281474976710656), by norm_num⟩
  | 6 => ⟨((-39856723/2251799813685248), (-1951220897/2251799813685248)), (139347/2251799813685248), by norm_num⟩
  | 7 => ⟨((545679883/9007199254740992), (-1010890499/9007199254740992)), (47035/2251799813685248), by norm_num⟩
  | 8 => ⟨((479864127/36028797018963968), (-665737269/72057594037927936)), (225091/36028797018963968), by norm_num⟩
  | 9 => ⟨((1038158949/576460752303423488), (-194885001/576460752303423488)), (489427/288230376151711744), by norm_num⟩
  | 10 => ⟨((855725357/4611686018427387904), (167495219/4611686018427387904)), (509903/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1142870485/73786976294838206464), (689465219/73786976294838206464)), (4780587/36893488147419103232), by norm_num⟩
  | 12 => ⟨((305753909/295147905179352825856), (728393561/590295810358705651712)), (8628505/147573952589676412928), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile035Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((365333959/67108864), (65474369/16777216)), (617/67108864), by norm_num⟩
  | 1 => ⟨((-721096595/134217728), (406251343/67108864)), (1537/67108864), by norm_num⟩
  | 2 => ⟨((218356049/67108864), (-27391155/16777216)), (8357/268435456), by norm_num⟩
  | 3 => ⟨((-17624193/16777216), (5080737/33554432)), (31601/1073741824), by norm_num⟩
  | 4 => ⟨((16105003/67108864), (3278551/67108864)), (46113/2147483648), by norm_num⟩
  | 5 => ⟨((-5400949/134217728), (-1701075/67108864)), (220423/17179869184), by norm_num⟩
  | 6 => ⟨((1281253/268435456), (1743377/268435456)), (890423/137438953472), by norm_num⟩
  | 7 => ⟨((-160851/536870912), (-635171/536870912)), (3144115/1099511627776), by norm_num⟩
  | 8 => ⟨((-26325/1073741824), (44571/268435456)), (5007051/4398046511104), by norm_num⟩
  | 9 => ⟨((1485/134217728), (-19439/1073741824)), (30567597/70368744177664), by norm_num⟩
  | 10 => ⟨((-8733/4294967296), (6159/4294967296)), (49689267/281474976710656), by norm_num⟩
  | 11 => ⟨((2295/8589934592), (-1873/34359738368)), (210474389/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1883/68719476736), (-829/137438953472)), (1240640679/18014398509481984), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile035Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8601/640))
  have he : value ((5/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-48013451/134217728), (-1032409239/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((253867524422203/2251799813685248), (-777000434134303/1125899906842624)), (58465609/2251799813685248), by norm_num⟩
  | 1 => ⟨((-277147047/4294967296), (848250979/2147483648)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((79314627/4294967296), (-971018247/8589934592)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((-945769/268435456), (1482071477/68719476736)), (1/1073741824), by norm_num⟩
  | 4 => ⟨((138579205/274877906944), (-1696571513/549755813888)), (19/137438953472), by norm_num⟩
  | 5 => ⟨((-63454303/1099511627776), (388423223/1099511627776)), (9/549755813888), by norm_num⟩
  | 6 => ⟨((24212679/4398046511104), (-18526653/549755813888)), (57/35184372088832), by norm_num⟩
  | 7 => ⟨((-63353091/140737488355328), (1551214693/562949953421312)), (77/562949953421312), by norm_num⟩
  | 8 => ⟨((290088707/9007199254740992), (-1775721819/9007199254740992)), (91/9007199254740992), by norm_num⟩
  | 9 => ⟨((-295176189/144115188075855872), (903431927/72057594037927936)), (95/144115188075855872), by norm_num⟩
  | 10 => ⟨((67579401/576460752303423488), (-1654696843/2305843009213693952)), (89/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-112523869/18446744073709551616), (688793065/18446744073709551616)), (19/9223372036854775808), by norm_num⟩
  | 12 => ⟨((85872957/295147905179352825856), (-1051309343/590295810358705651712)), (15/147573952589676412928), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791754893166141/5070602400912917605986812821504), (-1835201275805/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445354255916177/158456325028528675187087900672), (-2178019282517/633825300114114700748351602688)), (361/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1892720710452507/39614081257132168796771975168), (-2450188751279/39614081257132168796771975168)), (25995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892681452733403/2475880078570760549798248448), (-2603230036829/2475880078570760549798248448)), (3453/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774347128754723/154742504910672534362390528), (-2603122560353/154742504910672534362390528)), (27629/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552511979895851/9671406556917033397649408), (-610078295171/2417851639229258349412352)), (25907/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261376809647601/604462909807314587353088), (-2135159784333/604462909807314587353088)), (11337/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891996607723407/75557863725914323419136), (-3469420371247/75557863725914323419136)), (9213/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((650345937942291/2361183241434822606848), (-650469430771/1180591620717411303424)), (27647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625781071340069/590295810358705651712), (-3577276975879/590295810358705651712)), (38027/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828888377569001/73786976294838206464), (-4471138677027/73786976294838206464)), (47553/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828744009372487/9223372036854775808), (-2514700780451/4611686018427387904)), (53523/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399997076822463/288230376151711744), (-5028614253647/1152921504606846976)), (13389/288230376151711744), by norm_num⟩
  | 5 => ⟨((18747315177611/2251799813685248), (-4399151072691/144115188075855872)), (23449/72057594037927936), by norm_num⟩
  | 4 => ⟨((1499499055334435/36028797018963968), (-6596952115277/36028797018963968)), (17605/9007199254740992), by norm_num⟩
  | 3 => ⟨((374767051829403/2251799813685248), (-8243080969019/9007199254740992)), (88153/9007199254740992), by norm_num⟩
  | 2 => ⟨((561879890584459/1125899906842624), (-8238409592741/2251799813685248)), (44173/1125899906842624), by norm_num⟩
  | 1 => ⟨((140333575048649/140737488355328), (-12345909338125/1125899906842624)), (66501/562949953421312), by norm_num⟩
  | 0 => ⟨((279838243178695/281474976710656), (-12322419555453/562949953421312)), (267939/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((279838243178695/281474976710656), (-12322419555453/562949953421312)), (1022106174949264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((556152328381737/562949953421312), (-24501533176453/562949953421312)), (544493/1125899906842624), by norm_num⟩
  | 2 => ⟨((1096740786140169/1125899906842624), (-96822707895731/1125899906842624)), (561617/562949953421312), by norm_num⟩
  | 3 => ⟨((530005246454787/562949953421312), (-188630289652607/1125899906842624)), (595369/281474976710656), by norm_num⟩
  | 4 => ⟨((30199200332203/35184372088832), (-88795675839897/281474976710656)), (2641095/562949953421312), by norm_num⟩
  | 5 => ⟨((717403690902441/1125899906842624), (-609715790079101/1125899906842624)), (3100061/281474976710656), by norm_num⟩
  | 6 => ⟨((253867524422203/2251799813685248), (-777000434134303/1125899906842624)), (58465609/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-48013451/134217728), (-1032409239/134217728)), (1/67108864), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((879158993/4398046511104), (-348460013/4398046511104)), (339/1099511627776), by norm_num⟩
  | 1 => ⟨((73710521/549755813888), (251961637/2199023255552)), (1749/2199023255552), by norm_num⟩
  | 2 => ⟨((-37060833/2199023255552), (586915537/8796093022208)), (9395/8796093022208), by norm_num⟩
  | 3 => ⟨((-583418261/35184372088832), (208825577/70368744177664)), (68921/70368744177664), by norm_num⟩
  | 4 => ⟨((-210798591/140737488355328), (-171673055/70368744177664)), (96583/140737488355328), by norm_num⟩
  | 5 => ⟨((264419865/1125899906842624), (-294985853/1125899906842624)), (219615/562949953421312), by norm_num⟩
  | 6 => ⟨((940346615/36028797018963968), (655471815/36028797018963968)), (1682657/9007199254740992), by norm_num⟩
  | 7 => ⟨((-515877867/288230376151711744), (908918859/576460752303423488)), (44603487/576460752303423488), by norm_num⟩
  | 8 => ⟨((-110580625/2305843009213693952), (-132952353/576460752303423488)), (130409893/4611686018427387904), by norm_num⟩
  | 9 => ⟨((970142953/36893488147419103232), (151257775/73786976294838206464)), (171109511/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-203746353/295147905179352825856), (695034729/295147905179352825856)), (1643834769/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-201420921/1180591620717411303424), (-4247065/36893488147419103232)), (1877903975/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((68975335/4722366482869645213696), (-47790713/4722366482869645213696)), (8902529/36893488147419103232), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((768243211/549755813888), (383500923/1099511627776)), (5991/1099511627776), by norm_num⟩
  | 1 => ⟨((-10705729/34359738368), (191231553/68719476736)), (2699/137438953472), by norm_num⟩
  | 2 => ⟨((-1368944887/1099511627776), (-24907249/274877906944)), (39287/1099511627776), by norm_num⟩
  | 3 => ⟨((44436719/4398046511104), (-265702507/1099511627776)), (192045/4398046511104), by norm_num⟩
  | 4 => ⟨((1423966009/70368744177664), (-2428637/17592186044416)), (1416779/35184372088832), by norm_num⟩
  | 5 => ⟨((306753585/2251799813685248), (-245943949/1125899906842624)), (33654381/1125899906842624), by norm_num⟩
  | 6 => ⟨((409198387/2251799813685248), (87372863/9007199254740992)), (41886773/2251799813685248), by norm_num⟩
  | 7 => ⟨((3275687/9007199254740992), (1601377853/144115188075855872)), (1438979369/144115188075855872), by norm_num⟩
  | 8 => ⟨((52003001/144115188075855872), (2807969/36028797018963968)), (1362656471/288230376151711744), by norm_num⟩
  | 9 => ⟨((-6647/4503599627370496), (39940441/576460752303423488)), (1161869119/576460752303423488), by norm_num⟩
  | 10 => ⟨((-3112545/2305843009213693952), (847975/2305843009213693952)), (1829586841/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-59973/2305843009213693952), (135297/576460752303423488)), (1394981553/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-126905/9223372036854775808), (-4439/1152921504606846976)), (286261457/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1500475/1073741824), (374513/1073741824)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-167277/536870912), (2987993/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-334215/268435456), (-48647/536870912)), (1/10000000), by norm_num⟩
  | 3 => ⟨((10849/1073741824), (-259475/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((679/33554432), (-37/268435456)), (1/10000000), by norm_num⟩
  | 5 => ⟨((73/536870912), (-235/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((195/1073741824), (5/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨(0, (3/268435456)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨35,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨35,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(33201/131072)) (K:=(680143/134217728)) (L:=(791811801/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile035
