/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import XiRectangle.Tile013Gamma
public import XiRectangle.Tile013Zeta
public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile013
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2880126969/1099511627776), (67419848609/1099511627776)), (145/274877906944), by norm_num⟩
  | 1 => ⟨((-20800212409/549755813888), (19932446603/549755813888)), (1419/1099511627776), by norm_num⟩
  | 2 => ⟨((-87406649187/4398046511104), (-5686562585/4398046511104)), (1727/1099511627776), by norm_num⟩
  | 3 => ⟨((-50725658939/17592186044416), (-13681082167/4398046511104)), (5585/4398046511104), by norm_num⟩
  | 4 => ⟨((-9998337925/70368744177664), (-9054771257/17592186044416)), (109353/140737488355328), by norm_num⟩
  | 5 => ⟨((-8709271573/281474976710656), (-9856157403/140737488355328)), (54297/140737488355328), by norm_num⟩
  | 6 => ⟨((-3086578209/4503599627370496), (-70379137131/4503599627370496)), (730721/4503599627370496), by norm_num⟩
  | 7 => ⟨((9842551857/9007199254740992), (-11881199347/9007199254740992)), (134087/2251799813685248), by norm_num⟩
  | 8 => ⟨((3385748989/144115188075855872), (-54182457837/1152921504606846976)), (22488577/1152921504606846976), by norm_num⟩
  | 9 => ⟨((4933031347/2305843009213693952), (-117895862371/4611686018427387904)), (26820465/4611686018427387904), by norm_num⟩
  | 10 => ⟨((65719306243/18446744073709551616), (-9331931559/9223372036854775808)), (14895593/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-1812809903/36893488147419103232), (80464420351/295147905179352825856)), (129560803/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-7286151833/295147905179352825856), (-56531099115/1180591620717411303424)), (159039231/1180591620717411303424), by norm_num⟩
  | _ => zero
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := Reinmann.XiRectangle.Tile013Gamma.gammaJet_sound

def J_zetaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-34096765351/17179869184), (42802881113/8589934592)), (1471/17179869184), by norm_num⟩
  | 1 => ⟨((14517944223/8589934592), (6901532877/8589934592)), (2107/17179869184), by norm_num⟩
  | 2 => ⟨((-279161315/4294967296), (-1197839679/4294967296)), (40877/274877906944), by norm_num⟩
  | 3 => ⟨((-90958195/4294967296), (222877751/4294967296)), (161459/1099511627776), by norm_num⟩
  | 4 => ⟨((35898837/4294967296), (-19208395/4294967296)), (551115/4398046511104), by norm_num⟩
  | 5 => ⟨((-12208017/8589934592), (-1256833/4294967296)), (7031981/70368744177664), by norm_num⟩
  | 6 => ⟨((2183575/17179869184), (2664427/17179869184)), (22704819/281474976710656), by norm_num⟩
  | 7 => ⟨((-685/2147483648), (-869807/34359738368)), (156013973/2251799813685248), by norm_num⟩
  | 8 => ⟨((-123611/68719476736), (161675/68719476736)), (1147448487/18014398509481984), by norm_num⟩
  | 9 => ⟨((21451/68719476736), (-23069/274877906944)), (8834606389/144115188075855872), by norm_num⟩
  | 10 => ⟨((-16877/549755813888), (-6829/549755813888)), (69663926693/1152921504606846976), by norm_num⟩
  | 11 => ⟨((917/549755813888), (3013/1099511627776)), (69318945189/1152921504606846976), by norm_num⟩
  | 12 => ⟨((27/1099511627776), (-647/2199023255552)), (69213694373/1152921504606846976), by norm_num⟩
  | _ => zero
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := Reinmann.XiRectangle.Tile013Zeta.zetaJet_sound

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3807/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3807/640))
  have he : value ((3/4), (3807/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-9833154845/17179869184), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-3687433067/8589934592), (-116983814047/34359738368)), (3/34359738368), by norm_num⟩
  | 1 => ⟨((-9833154845/17179869184), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-1415443148740433/2251799813685248), (95304256717975/562949953421312)), (362417/2251799813685248), by norm_num⟩
  | 1 => ⟨((49447634097/137438953472), (-26635163797/274877906944)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((-7075523067/68719476736), (15245034007/549755813888)), (9/274877906944), by norm_num⟩
  | 3 => ⟨((21598833901/1099511627776), (-11634297359/2199023255552)), (15/2199023255552), by norm_num⟩
  | 4 => ⟨((-12362415333/4398046511104), (832382993/1099511627776)), (37/35184372088832), by norm_num⟩
  | 5 => ⟨((90570408275/281474976710656), (-24393054427/281474976710656)), (37/281474976710656), by norm_num⟩
  | 6 => ⟨((-17279775521/562949953421312), (4653909735/562949953421312)), (15/1125899906842624), by norm_num⟩
  | 7 => ⟨((90425944959/36028797018963968), (-24354146559/36028797018963968)), (21/18014398509481984), by norm_num⟩
  | 8 => ⟨((-103513281651/576460752303423488), (27878919411/576460752303423488)), (51/576460752303423488), by norm_num⟩
  | 9 => ⟨((105328664079/9223372036854775808), (-7091962719/2305843009213693952)), (55/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-96458295687/147573952589676412928), (6494705339/36893488147419103232)), (53/147573952589676412928), by norm_num⟩
  | 11 => ⟨((40152252295/1180591620717411303424), (-5407042401/590295810358705651712)), (23/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-61284644249/37778931862957161709568), (16505608081/37778931862957161709568)), (37/37778931862957161709568), by norm_num⟩
  | _ => zero

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791708295086541/5070602400912917605986812821504), (468697292465/1267650600228229401496703205376)), (115/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781298409573845/633825300114114700748351602688), (4449480537413/633825300114114700748351602688)), (137/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892586783690209/39614081257132168796771975168), (5005441468589/39614081257132168796771975168)), (153/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892538567370839/2475880078570760549798248448), (5318044827903/2475880078570760549798248448)), (163/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887101790854901/77371252455336267181195264), (5317778242479/154742504910672534362390528)), (163/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776188350801765/4835703278458516698824704), (4985133599761/9671406556917033397649408)), (153/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261257738316333/604462909807314587353088), (4361708109983/604462909807314587353088)), (67/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891801799251015/75557863725914323419136), (7087242962607/75557863725914323419136)), (109/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((325136154226267/1180591620717411303424), (5314965485321/4722366482869645213696)), (41/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625576717675907/590295810358705651712), (1826829487971/147573952589676412928)), (225/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828630127424083/73786976294838206464), (9133006054071/73786976294838206464)), (281/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828449618150317/9223372036854775808), (10273059156697/9223372036854775808)), (79/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599689093229771/1152921504606846976), (5135544234355/576460752303423488)), (79/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199560936022779/144115188075855872), (4492489346915/72057594037927936)), (277/144115188075855872), by norm_num⟩
  | 4 => ⟨((749543681439945/18014398509481984), (6736501945291/18014398509481984)), (417/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498534637735081/9007199254740992), (8416702511101/4503599627370496)), (261/4503599627370496), by norm_num⟩
  | 2 => ⟨((1123197810694189/2251799813685248), (16821555195161/2251799813685248)), (131/562949953421312), by norm_num⟩
  | 1 => ⟨((280438687114995/281474976710656), (25202445906331/1125899906842624)), (99/140737488355328), by norm_num⟩
  | 0 => ⟨((1117242324544481/1125899906842624), (50283773648223/1125899906842624)), (803/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((1117242324544481/1125899906842624), (50283773648223/1125899906842624)), (3063204051780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1106405592797843/1125899906842624), (99794235377731/1125899906842624)), (3331/1125899906842624), by norm_num⟩
  | 2 => ⟨((1078403541008051/1125899906842624), (196132710341079/1125899906842624)), (3569/562949953421312), by norm_num⟩
  | 3 => ⟨((998744338070315/1125899906842624), (187858803481445/562949953421312)), (8081/562949953421312), by norm_num⟩
  | 4 => ⟨((760570746512449/1125899906842624), (666570501315381/1125899906842624)), (39461/1125899906842624), by norm_num⟩
  | 5 => ⟨((29787645067595/281474976710656), (1801133549110349/2251799813685248)), (200077/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1415443148740433/2251799813685248), (95304256717975/562949953421312)), (362417/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-3687433067/8589934592), (-116983814047/34359738368)), (3/34359738368), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

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
  | 0 => ⟨((-13224199613/1099511627776), (-10472845853/274877906944)), (949/2199023255552), by norm_num⟩
  | 1 => ⟨((53938974815/2199023255552), (-8123953705/1099511627776)), (709/549755813888), by norm_num⟩
  | 2 => ⟨((706005381/1099511627776), (17411929639/2199023255552)), (8465/4398046511104), by norm_num⟩
  | 3 => ⟨((-29385287593/17592186044416), (-23357389795/35184372088832)), (8437/4398046511104), by norm_num⟩
  | 4 => ⟨((44270354399/140737488355328), (-30434474389/140737488355328)), (12677/8796093022208), by norm_num⟩
  | 5 => ⟨((1432364343/1125899906842624), (10751281567/140737488355328)), (983049/1125899906842624), by norm_num⟩
  | 6 => ⟨((-13303857105/1125899906842624), (-17145166599/2251799813685248)), (2004633/4503599627370496), by norm_num⟩
  | 7 => ⟨((81131935417/36028797018963968), (-17196633773/18014398509481984)), (7085003/36028797018963968), by norm_num⟩
  | 8 => ⟨((-5577309519/72057594037927936), (57688923855/144115188075855872)), (11088457/144115188075855872), by norm_num⟩
  | 9 => ⟨((-26977167151/576460752303423488), (-52665592099/1152921504606846976)), (1954583/72057594037927936), by norm_num⟩
  | 10 => ⟨((91335236127/9223372036854775808), (-2635748247/1152921504606846976)), (80702383/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-9174701099/18446744073709551616), (53732295903/36893488147419103232)), (97058475/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-10877222869/73786976294838206464), (-51398086893/295147905179352825856)), (112996835/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_piGamma : Sound J_piGamma F_piGamma c := by
  apply sound_round (sound_mul (A_piPower hcre) (A_gammaActual hcre) S_piPower S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_piGamma, J_piPower, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_xiProduct : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((117493509281/549755813888), (8623260735/549755813888)), (2007/274877906944), by norm_num⟩
  | 1 => ⟨((-1738191323/1099511627776), (17271028441/274877906944)), (20829/1099511627776), by norm_num⟩
  | 2 => ⟨((-111916408571/35184372088832), (18827584553/35184372088832)), (1016011/35184372088832), by norm_num⟩
  | 3 => ⟨((-10765599479/140737488355328), (100578910995/140737488355328)), (4503301/140737488355328), by norm_num⟩
  | 4 => ⟨((-43282935461/562949953421312), (495442981/140737488355328)), (31705333/1125899906842624), by norm_num⟩
  | 5 => ⟨((-16956261503/18014398509481984), (50710344765/18014398509481984)), (190768933/9007199254740992), by norm_num⟩
  | 6 => ⟨((-45471557519/72057594037927936), (-334820355/144115188075855872)), (2115601461/144115188075855872), by norm_num⟩
  | 7 => ⟨((-28151066179/4611686018427387904), (-842820185/576460752303423488)), (94093326951/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-14112750007/4611686018427387904), (-1343586215/9223372036854775808)), (70789007843/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-508448261/18446744073709551616), (-1269730825/18446744073709551616)), (3717453279/576460752303423488), by norm_num⟩
  | 10 => ⟨((-173223063/18446744073709551616), (-12956389/18446744073709551616)), (27315643975/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-6430821/18446744073709551616), (-3890715/9223372036854775808)), (105516046445/18446744073709551616), by norm_num⟩
  | 12 => ⟨((162555/2305843009213693952), (-26449/4611686018427387904)), (52095211989/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul (A_piGamma hcre) (A_zetaActual hcre) S_piGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_piGamma, J_zetaActual, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def xiJet : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((114739755/536870912), (8421153/536870912)), (1/10000000), by norm_num⟩
  | 1 => ⟨((-424363/268435456), (67464955/1073741824)), (1/10000000), by norm_num⟩
  | 2 => ⟨((-1707709/536870912), (143643/268435456)), (1/10000000), by norm_num⟩
  | 3 => ⟨((-82135/1073741824), (191839/268435456)), (1/10000000), by norm_num⟩
  | 4 => ⟨((-20639/268435456), (945/268435456)), (1/10000000), by norm_num⟩
  | 5 => ⟨((-1011/1073741824), (3023/1073741824)), (1/10000000), by norm_num⟩
  | 6 => ⟨((-339/536870912), (-3/1073741824)), (1/10000000), by norm_num⟩
  | 7 => ⟨((-7/1073741824), (-1/536870912)), (1/10000000), by norm_num⟩
  | 8 => ⟨((-3/1073741824), 0), (1/10000000), by norm_num⟩
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
theorem nonzero {z:ℂ} (hz:‖z-Data.centre ⟨13,by norm_num [Data.count]⟩‖≤
    (Data.radius ⟨13,by norm_num [Data.count]⟩:ℝ)) : xiCompleted z≠0 := by
  apply RectangleTileRules.certified_tile_nonzero (a:=xiJet) (c:=c)
    (r:=(174705/524288)) (K:=(112862407/1073741824)) (L:=(235619059585/1099511627776)) hc xiJet_sound
  · norm_num
  · norm_num
  · norm_num
  · norm_num [RectangleTileRules.derivativeBudget,xiJet,Finset.sum_range_succ,CertifiedTaylorModel.get,size]
  · norm_num
  · norm_num [xiJet]
  · norm_num [xiJet]
  · simpa only [c,Data.radius] using! hz

end Reinmann.XiRectangle.Tile013
