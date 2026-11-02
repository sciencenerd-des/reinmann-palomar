/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile021Gamma
public import XiRectangle.Tile021Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile021
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2224480025/549755813888), (-2251910751/549755813888)), (431/549755813888), by norm_num⟩
  | 1 => ⟨((-368924461/1099511627776), (-6622894565/1099511627776)), (955/549755813888), by norm_num⟩
  | 2 => ⟨((1007974341/549755813888), (-329467413/137438953472)), (1079/549755813888), by norm_num⟩
  | 3 => ⟨((1020669817/1099511627776), (-974797495/4398046511104)), (6583/4398046511104), by norm_num⟩
  | 4 => ⟨((215379359/1099511627776), (741917673/8796093022208)), (7647/8796093022208), by norm_num⟩
  | 5 => ⟨((2837662453/140737488355328), (4189473873/140737488355328)), (57735/140737488355328), by norm_num⟩
  | 6 => ⟨((765184727/1125899906842624), (5459116913/1125899906842624)), (184323/1125899906842624), by norm_num⟩
  | 7 => ⟨((-518791459/4503599627370496), (5288714037/9007199254740992)), (511681/9007199254740992), by norm_num⟩
  | 8 => ⟨((-149890467/4503599627370496), (562896529/9007199254740992)), (1261189/72057594037927936), by norm_num⟩
  | 9 => ⟨((-809889161/144115188075855872), (3010153043/576460752303423488)), (2812629/576460752303423488), by norm_num⟩
  | 10 => ⟨((-2988751241/4611686018427387904), (695672359/2305843009213693952)), (5825063/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-4418498157/73786976294838206464), (258339309/18446744073709551616)), (23968673/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-6515088261/1180591620717411303424), (137721581/590295810358705651712)), (119988611/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile021Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-389602105/536870912), (1833041075/134217728)), (469/536870912), by norm_num⟩
  | 1 => ⟨((1212206021/536870912), (-1330834759/536870912)), (2145/1073741824), by norm_num⟩
  | 2 => ⟨((-402096637/536870912), (163012273/268435456)), (5881/2147483648), by norm_num⟩
  | 3 => ⟨((62650475/268435456), (-26658669/536870912)), (45447/17179869184), by norm_num⟩
  | 4 => ⟨((-1533265/33554432), (-3716859/268435456)), (273975/137438953472), by norm_num⟩
  | 5 => ⟨((1513123/268435456), (1599335/268435456)), (339053/274877906944), by norm_num⟩
  | 6 => ⟨((-38703/134217728), (-651823/536870912)), (2918091/4398046511104), by norm_num⟩
  | 7 => ⟨((-53229/1073741824), (88137/536870912)), (11630167/35184372088832), by norm_num⟩
  | 8 => ⟨((135607/8589934592), (-126511/8589934592)), (47067827/281474976710656), by norm_num⟩
  | 9 => ⟨((-10539/4294967296), (9621/17179869184)), (220435861/2251799813685248), by norm_num⟩
  | 10 => ⟨((8989/34359738368), (5579/68719476736)), (1299229863/18014398509481984), by norm_num⟩
  | 11 => ⟨((-653/34359738368), (-707/34359738368)), (4578783899/72057594037927936), by norm_num⟩
  | 12 => ⟨((163/274877906944), (181/68719476736)), (4391744155/72057594037927936), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile021Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6063/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6063/640))
  have he : value ((3/4), (6063/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-460929133/1073741824), (-5822111115/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((477685474493289/1125899906842624), (277946946401939/562949953421312)), (5304037/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1042977979/4294967296), (-75858635/268435456)), (13/8589934592), by norm_num⟩
  | 2 => ⟨((2387856125/34359738368), (1389402345/17179869184)), (17/34359738368), by norm_num⟩
  | 3 => ⟨((-3644600359/274877906944), (-1060326925/68719476736)), (29/274877906944), by norm_num⟩
  | 4 => ⟨((521510369/274877906944), (2427575839/1099511627776)), (19/1099511627776), by norm_num⟩
  | 5 => ⟨((-3820726433/17592186044416), (-1111567445/4398046511104)), (19/8796093022208), by norm_num⟩
  | 6 => ⟨((1457899911/70368744177664), (3393185265/140737488355328)), (31/140737488355328), by norm_num⟩
  | 7 => ⟨((-3814632225/2251799813685248), (-4439177807/2251799813685248)), (43/2251799813685248), by norm_num⟩
  | 8 => ⟨((545840439/4503599627370496), (317603719/2251799813685248)), (27/18014398509481984), by norm_num⟩
  | 9 => ⟨((-138853303/18014398509481984), (-1292695001/144115188075855872)), (15/144115188075855872), by norm_num⟩
  | 10 => ⟨((2034553929/4611686018427387904), (2367658561/4611686018427387904)), (29/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-1693828863/73786976294838206464), (-3942297475/147573952589676412928)), (25/73786976294838206464), by norm_num⟩
  | 12 => ⟨((646325507/590295810358705651712), (3008577159/2361183241434822606848)), (5/295147905179352825856), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583416590173537/10141204801825835211973625643008), (1121446758921/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781308006951441/633825300114114700748351602688), (665388888493/316912650057057350374175801344)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946299084253023/19807040628566084398385987584), (1497066032083/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892551374461739/2475880078570760549798248448), (1590562850783/2475880078570760549798248448)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443554297084781/38685626227668133590597632), (1590484313929/154742504910672534362390528)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776195153607141/4835703278458516698824704), (5824201551/37778931862957161709568)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261270492493517/604462909807314587353088), (1304537698097/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((945912058446901/37778931862957161709568), (1059858643757/37778931862957161709568)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300562747956413/4722366482869645213696), (1589651048327/4722366482869645213696)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625603910691261/590295810358705651712), (2185547692579/590295810358705651712)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457166878006631/18446744073709551616), (1365800426503/36893488147419103232)), (5935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914248170101211/4611686018427387904), (768148003127/2305843009213693952)), (6679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399935410889405/288230376151711744), (3072018293577/1152921504606846976)), (6681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199613471349223/144115188075855872), (2687370525009/144115188075855872)), (5849/144115188075855872), by norm_num⟩
  | 4 => ⟨((749589632939029/18014398509481984), (1007441175963/9007199254740992)), (4389/18014398509481984), by norm_num⟩
  | 3 => ⟨((93667026525711/562949953421312), (314684138395/562949953421312)), (5491/4503599627370496), by norm_num⟩
  | 2 => ⟨((280842481240027/562949953421312), (5031556179719/2251799813685248)), (10997/2251799813685248), by norm_num⟩
  | 1 => ⟨((280524654546133/281474976710656), (7538857314007/1125899906842624)), (4133/281474976710656), by norm_num⟩
  | 0 => ⟨((559136064359953/562949953421312), (15043795656735/1125899906842624)), (33211/1125899906842624), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((559136064359953/562949953421312), (15043795656735/1125899906842624)), (126689915183639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1110495018682645/1125899906842624), (7470938264957/281474976710656)), (66861/1125899906842624), by norm_num⟩
  | 2 => ⟨((1094507726959317/1125899906842624), (29474874907437/562949953421312)), (67721/562949953421312), by norm_num⟩
  | 3 => ⟨((530452167244639/562949953421312), (114612242673747/1125899906842624)), (277515/1125899906842624), by norm_num⟩
  | 4 => ⟨((493996861535809/562949953421312), (107995945553543/562949953421312)), (289745/562949953421312), by norm_num⟩
  | 5 => ⟨((825543278009013/1125899906842624), (379072120623237/1125899906842624)), (1239361/1125899906842624), by norm_num⟩
  | 6 => ⟨((477685474493289/1125899906842624), (277946946401939/562949953421312)), (5304037/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-460929133/1073741824), (-5822111115/1073741824)), (1/536870912), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((168062575/549755813888), (-1026858561/274877906944)), (813/1099511627776), by norm_num⟩
  | 1 => ⟨((2921031525/1099511627776), (-160273453/274877906944)), (4473/2199023255552), by norm_num⟩
  | 2 => ⟨((1718816629/4398046511104), (3667264297/4398046511104)), (6281/2199023255552), by norm_num⟩
  | 3 => ⟨((-2904917659/17592186044416), (1746638459/17592186044416)), (23769/8796093022208), by norm_num⟩
  | 4 => ⟨((-1749446221/140737488355328), (-3656737451/140737488355328)), (272755/140737488355328), by norm_num⟩
  | 5 => ⟨((2122090399/562949953421312), (-194525349/562949953421312)), (1265457/1125899906842624), by norm_num⟩
  | 6 => ⟨((-212989495/1125899906842624), (2232992249/4503599627370496)), (2471801/4503599627370496), by norm_num⟩
  | 7 => ⟨((-3753783277/72057594037927936), (-3631089881/72057594037927936)), (4180047/18014398509481984), by norm_num⟩
  | 8 => ⟨((4818069149/576460752303423488), (-1989496401/576460752303423488)), (49971601/576460752303423488), by norm_num⟩
  | 9 => ⟨((-65067457/1152921504606846976), (4969844951/4611686018427387904)), (67064507/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-4068004747/36893488147419103232), (-1113764327/18446744073709551616)), (41021231/4611686018427387904), by norm_num⟩
  | 11 => ⟨((3386961743/295147905179352825856), (-1223296571/147573952589676412928)), (373343907/147573952589676412928), by norm_num⟩
  | 12 => ⟨((657345131/2361183241434822606848), (224199467/147573952589676412928)), (3312928949/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6981526423/137438953472), (473203819/68719476736)), (487/34359738368), by norm_num⟩
  | 1 => ⟨((-696768147/274877906944), (3781372451/137438953472)), (12003/274877906944), by norm_num⟩
  | 2 => ⟨((-1396046983/274877906944), (-12795151/68719476736)), (4833/68719476736), by norm_num⟩
  | 3 => ⟨((-321355159/8796093022208), (-1100830033/4398046511104)), (170653/2199023255552), by norm_num⟩
  | 4 => ⟨((-2570344415/70368744177664), (-215673279/35184372088832)), (4623939/70368744177664), by norm_num⟩
  | 5 => ⟨((19807885/1125899906842624), (-346861987/70368744177664)), (51156367/1125899906842624), by norm_num⟩
  | 6 => ⟨((943080611/72057594037927936), (-3651727105/72057594037927936)), (481675237/18014398509481984), by norm_num⟩
  | 7 => ⟨((84452903/36028797018963968), (-1048316929/36028797018963968)), (997619743/72057594037927936), by norm_num⟩
  | 8 => ⟨((341242229/288230376151711744), (-113101007/576460752303423488)), (7534169979/1152921504606846976), by norm_num⟩
  | 9 => ⟨((38024945/2305843009213693952), (-205221001/2305843009213693952)), (106949285/36028797018963968), by norm_num⟩
  | 10 => ⟨((32015855/4611686018427387904), (-2050719/4611686018427387904)), (6600660707/4611686018427387904), by norm_num⟩
  | 11 => ⟨((647847/9223372036854775808), (-482125/2305843009213693952)), (7710291705/9223372036854775808), by norm_num⟩
  | 12 => ⟨((299/9007199254740992), (11095/576460752303423488)), (5775068007/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((54543175/1073741824), (3696905/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-2721751/1073741824), (7385493/268435456)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-1363327/268435456), (-49981/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-9807/268435456), (-268757/1073741824)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-9805/268435456), (-3291/536870912)), (1/10000000), by norm_num⟩
  | 5 => ⟨((19/1073741824), (-5293/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((7/536870912), (-27/536870912)), (1/10000000), by norm_num⟩
  | 7 => ⟨((3/1073741824), (-31/1073741824)), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨21,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨21,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(76885867/1073741824)) (L:=(28181525401/549755813888)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile021
