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
namespace Reinmann.XiRectangle.Tile021Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

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
  | 0 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-279097919/536870912), (-7050711185/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1285555693861333/2251799813685248), (-46783282058499/281474976710656)), (3255989/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3399197787/8589934592), (494807435/4294967296)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((4712288725/34359738368), (-685948757/17179869184)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((-4355079525/137438953472), (1267902525/137438953472)), (17/137438953472), by norm_num⟩
  | 4 => ⟨((1509355547/274877906944), (-1757686121/1099511627776)), (13/549755813888), by norm_num⟩
  | 5 => ⟨((-1673928867/2199023255552), (974668143/4398046511104)), (1/274877906944), by norm_num⟩
  | 6 => ⟨((6188155065/70368744177664), (-450392317/17592186044416)), (1/2199023255552), by norm_num⟩
  | 7 => ⟨((-4902059699/562949953421312), (178393237/70368744177664)), (27/562949953421312), by norm_num⟩
  | 8 => ⟨((849462215/1125899906842624), (-494611077/2251799813685248)), (21/4503599627370496), by norm_num⟩
  | 9 => ⟨((-2093519429/36028797018963968), (76186283/4503599627370496)), (7/18014398509481984), by norm_num⟩
  | 10 => ⟨((4643574687/1152921504606846976), (-675946333/576460752303423488)), (33/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-4681717385/18446744073709551616), (681498611/9223372036854775808)), (35/18446744073709551616), by norm_num⟩
  | 12 => ⟨((540853201/36893488147419103232), (-1259676909/295147905179352825856)), (17/147573952589676412928), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197912323863903/1267650600228229401496703205376), (-92257856541/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781168832952481/633825300114114700748351602688), (-437850121657/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892441656033501/39614081257132168796771975168), (-246279112699/19807040628566084398385987584)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892385150338661/2475880078570760549798248448), (-261657668475/1237940039285380274899124224)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110878190211473/9671406556917033397649408), (-261642044679/77371252455336267181195264)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776117315211839/4835703278458516698824704), (-122636408897/2417851639229258349412352)), (3231/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261134359395427/604462909807314587353088), (-429194235635/604462909807314587353088)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((29556297785321/1180591620717411303424), (-174344599257/18889465931478580854784)), (4595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300397091901689/4722366482869645213696), (-261489673535/2361183241434822606848)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625376357690387/590295810358705651712), (-719008130505/590295810358705651712)), (4739/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228547925850815/9223372036854775808), (-112328434279/9223372036854775808)), (1481/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828177183741907/9223372036854775808), (-252693372905/2305843009213693952)), (6665/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599423064290971/1152921504606846976), (-1010545516013/1152921504606846976)), (3333/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199335363564357/144115188075855872), (-883970916515/144115188075855872)), (2917/72057594037927936), by norm_num⟩
  | 4 => ⟨((749381700836803/18014398509481984), (-331360927787/9007199254740992)), (547/2251799813685248), by norm_num⟩
  | 3 => ⟨((1498154863216835/9007199254740992), (-1655907829321/9007199254740992)), (10943/9007199254740992), by norm_num⟩
  | 2 => ⟨((2245711528649209/4503599627370496), (-3309126636215/4503599627370496)), (21895/4503599627370496), by norm_num⟩
  | 1 => ⟨((2242671736034053/2251799813685248), (-2478486159245/1125899906842624)), (16433/1125899906842624), by norm_num⟩
  | 0 => ⟨((2233561055744143/2251799813685248), (-1235887949651/281474976710656)), (16457/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((2233561055744143/2251799813685248), (-1235887949651/281474976710656)), (62778475047874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1107713306618263/1125899906842624), (-19614043321809/2251799813685248)), (131169/2251799813685248), by norm_num⟩
  | 2 => ⟨((544867525314045/562949953421312), (-38594437484383/2251799813685248)), (260387/2251799813685248), by norm_num⟩
  | 3 => ⟨((1054401097914079/1125899906842624), (-74709503092419/2251799813685248)), (512973/2251799813685248), by norm_num⟩
  | 4 => ⟨((1972406767370913/2251799813685248), (-34982586643145/562949953421312)), (497417/1125899906842624), by norm_num⟩
  | 5 => ⟨((859492022904063/1125899906842624), (-122568427647491/1125899906842624)), (1866441/2251799813685248), by norm_num⟩
  | 6 => ⟨((1285555693861333/2251799813685248), (-46783282058499/281474976710656)), (3255989/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/536870912), (-7050711185/1073741824)), (1/536870912), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-55294967/67108864), (-87305569/8388608)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-547905932421029/2251799813685248), (410985698141671/1125899906842624)), (5452493/1125899906842624), by norm_num⟩
  | 1 => ⟨((574051085/2147483648), (-3444777973/8589934592)), (3/536870912), by norm_num⟩
  | 2 => ⟨((-2522638305/17179869184), (3784475413/17179869184)), (55/17179869184), by norm_num⟩
  | 3 => ⟨((1847600961/34359738368), (-2771780797/34359738368)), (21/17179869184), by norm_num⟩
  | 4 => ⟨((-7928895/536870912), (3045112445/137438953472)), (3/8589934592), by norm_num⟩
  | 5 => ⟨((111498003/34359738368), (-1338159181/274877906944)), (11/137438953472), by norm_num⟩
  | 6 => ⟨((-2613185627/4398046511104), (980078747/1099511627776)), (33/2199023255552), by norm_num⟩
  | 7 => ⟨((3281003249/35184372088832), (-4922178539/35184372088832)), (43/17592186044416), by norm_num⟩
  | 8 => ⟨((-450568811/35184372088832), (2703782915/140737488355328)), (49/140737488355328), by norm_num⟩
  | 9 => ⟨((880000769/562949953421312), (-2640363677/1125899906842624)), (25/562949953421312), by norm_num⟩
  | 10 => ⟨((-773423727/4503599627370496), (1160294393/4503599627370496)), (91/18014398509481984), by norm_num⟩
  | 11 => ⟨((77244801/4503599627370496), (-1854128987/72057594037927936)), (75/144115188075855872), by norm_num⟩
  | 12 => ⟨((-1810391203/1152921504606846976), (339494815/144115188075855872)), (57/1152921504606846976), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (2811994351555/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890346565564041/316912650057057350374175801344), (3334717963053/633825300114114700748351602688)), (723/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945953086740705/19807040628566084398385987584), (3751267840067/39614081257132168796771975168)), (6509/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945907904010063/1237940039285380274899124224), (996346342683/618970019642690137449562112)), (6917/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773481260047477/154742504910672534362390528), (3985006485527/154742504910672534362390528)), (3459/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551699990091583/9671406556917033397649408), (3735540950203/9671406556917033397649408)), (811/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315166520198185/151115727451828646838272), (1634097814489/302231454903657293676544)), (5679/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890841227748607/75557863725914323419136), (2655031338057/37778931862957161709568)), (9231/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299824951260627/4722366482869645213696), (1990943017491/2361183241434822606848)), (3463/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624588417271105/590295810358705651712), (2737009465219/295147905179352825856)), (1191/73786976294838206464), by norm_num⟩
  | 8 => ⟨((456849152929709/18446744073709551616), (6840911608135/73786976294838206464)), (11917/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913532235116161/4611686018427387904), (7693808166659/9223372036854775808)), (1677/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1598307141907629/1152921504606846976), (7691035202431/1152921504606846976)), (13429/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198355324825381/144115188075855872), (6726534537945/144115188075855872)), (2941/36028797018963968), by norm_num⟩
  | 4 => ⟨((748643069291273/18014398509481984), (10083555089103/36028797018963968)), (8837/18014398509481984), by norm_num⟩
  | 3 => ⟨((93518480897885/562949953421312), (6296751351999/4503599627370496)), (11071/4503599627370496), by norm_num⟩
  | 2 => ⟨((560488873982685/1125899906842624), (12577072228145/2251799813685248)), (2777/281474976710656), by norm_num⟩
  | 1 => ⟨((139808981985723/140737488355328), (18824466845047/1125899906842624)), (33509/1125899906842624), by norm_num⟩
  | 0 => ⟨((555432670266877/562949953421312), (18741989054293/562949953421312)), (33881/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((555432670266877/562949953421312), (18741989054293/562949953421312)), (129245760204124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1094783602603691/1125899906842624), (36983440404507/562949953421312)), (138227/1125899906842624), by norm_num⟩
  | 2 => ⟨((264916985475883/281474976710656), (35961335351975/281474976710656)), (286977/1125899906842624), by norm_num⟩
  | 3 => ⟨((978954397415521/1125899906842624), (135383523842343/562949953421312)), (38345/70368744177664), by norm_num⟩
  | 4 => ⟨((786070691300815/1125899906842624), (29428525395019/70368744177664)), (1361985/1125899906842624), by norm_num⟩
  | 5 => ⟨((351897512328909/1125899906842624), (657476599065665/1125899906842624)), (1520487/562949953421312), by norm_num⟩
  | 6 => ⟨((-547905932421029/2251799813685248), (410985698141671/1125899906842624)), (5452493/1125899906842624), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-87305569/8388608)), (1/268435456), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-279097919/268435456), (-7050711185/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((1343439325375253/4503599627370496), (-213669134395713/1125899906842624)), (9678517/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1776125299/4294967296), (564972527/2147483648)), (7/2147483648), by norm_num⟩
  | 2 => ⟨((2462232487/8589934592), (-1566436457/8589934592)), (41/17179869184), by norm_num⟩
  | 3 => ⟨((-4551172017/34359738368), (1447694685/17179869184)), (5/4294967296), by norm_num⟩
  | 4 => ⟨((788658013/17179869184), (-2006930979/68719476736)), (15/34359738368), by norm_num⟩
  | 5 => ⟨((-874649725/68719476736), (139109855/17179869184)), (35/274877906944), by norm_num⟩
  | 6 => ⟨((3233391951/1099511627776), (-2057036881/1099511627776)), (17/549755813888), by norm_num⟩
  | 7 => ⟨((-5122780605/8796093022208), (3259038433/8796093022208)), (7/1099511627776), by norm_num⟩
  | 8 => ⟨((3550840933/35184372088832), (-2258993301/35184372088832)), (41/35184372088832), by norm_num⟩
  | 9 => ⟨((-4375565123/281474976710656), (1391835411/140737488355328)), (53/281474976710656), by norm_num⟩
  | 10 => ⟨((2426328503/1125899906842624), (-3087189731/2251799813685248)), (61/2251799813685248), by norm_num⟩
  | 11 => ⟨((-4892517123/18014398509481984), (3112548157/18014398509481984)), (1/281474976710656), by norm_num⟩
  | 12 => ⟨((4521645933/144115188075855872), (-1438302653/72057594037927936)), (61/144115188075855872), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414717067/10141204801825835211973625643008), (-738062852329/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111272838205649/39614081257132168796771975168), (-437475424745/316912650057057350374175801344)), (5769/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945768925923585/19807040628566084398385987584), (-492114044087/19807040628566084398385987584)), (3245/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891424912186781/2475880078570760549798248448), (-1045631360457/2475880078570760549798248448)), (431/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((886545432876061/77371252455336267181195264), (-1045506522433/154742504910672534362390528)), (6897/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387833632048975/2417851639229258349412352), (-61251858963/604462909807314587353088)), (3233/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260346834246407/604462909807314587353088), (-214348356379/151115727451828646838272)), (2829/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890323450453409/75557863725914323419136), (-1393015737005/75557863725914323419136)), (9195/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649718745766671/2361183241434822606848), (-1044544341199/4722366482869645213696)), (6897/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812028539297313/295147905179352825856), (-1435895179363/590295810358705651712)), (9485/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826734565042969/73786976294838206464), (-1794339188659/73786976294838206464)), (5929/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913161295131355/4611686018427387904), (-2017903374393/9223372036854775808)), (13343/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399392228167121/288230376151711744), (-504248367907/288230376151711744)), (6673/576460752303423488), by norm_num⟩
  | 5 => ⟨((299428369487501/36028797018963968), (-440961536601/36028797018963968)), (11681/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496331567278791/36028797018963968), (-1321862092419/18014398509481984)), (17529/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495116809580553/9007199254740992), (-1650539613055/4503599627370496)), (5481/2251799813685248), by norm_num⟩
  | 2 => ⟨((1119820319343493/2251799813685248), (-3295720826563/2251799813685248)), (21943/2251799813685248), by norm_num⟩
  | 1 => ⟨((1116789220843415/1125899906842624), (-9860409701389/2251799813685248)), (32963/1125899906842624), by norm_num⟩
  | 0 => ⟨((2215426613236525/2251799813685248), (-1225877707613/140737488355328)), (132241/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2215426613236525/2251799813685248), (-1225877707613/140737488355328)), (504459389693450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1089735050628089/1125899906842624), (-38594437484381/2251799813685248)), (262515/2251799813685248), by norm_num⟩
  | 2 => ⟨((1054401097914077/1125899906842624), (-74709503092415/2251799813685248)), (517165/2251799813685248), by norm_num⟩
  | 3 => ⟨((986203383685453/1125899906842624), (-34982586643143/562949953421312)), (1002963/2251799813685248), by norm_num⟩
  | 4 => ⟨((1718984045808115/2251799813685248), (-245136855294967/2251799813685248)), (470423/562949953421312), by norm_num⟩
  | 5 => ⟨((160694461732665/281474976710656), (-187133128233983/1125899906842624)), (3282593/2251799813685248), by norm_num⟩
  | 6 => ⟨((1343439325375253/4503599627370496), (-213669134395713/1125899906842624)), (9678517/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/268435456), (-7050711185/536870912)), (1/268435456), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-162011325/134217728), (-4092811097/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-603126879419135/2251799813685248), (-149805234681673/1125899906842624)), (14851741/4503599627370496), by norm_num⟩
  | 1 => ⟨((115715893/268435456), (1839463991/8589934592)), (47/8589934592), by norm_num⟩
  | 2 => ⟨((-744950181/2147483648), (-1480251543/8589934592)), (39/8589934592), by norm_num⟩
  | 3 => ⟨((1598601419/8589934592), (397062159/4294967296)), (11/4294967296), by norm_num⟩
  | 4 => ⟨((-5145699461/68719476736), (-2556187569/68719476736)), (73/68719476736), by norm_num⟩
  | 5 => ⟨((3312673519/137438953472), (822805037/68719476736)), (49/137438953472), by norm_num⟩
  | 6 => ⟨((-3554361569/549755813888), (-1765671495/549755813888)), (27/274877906944), by norm_num⟩
  | 7 => ⟨((102152219/68719476736), (811925327/1099511627776)), (51/2199023255552), by norm_num⟩
  | 8 => ⟨((-5261044931/17592186044416), (-2613486807/17592186044416)), (21/4398046511104), by norm_num⟩
  | 9 => ⟨((235203477/4398046511104), (29210033/1099511627776)), (31/35184372088832), by norm_num⟩
  | 10 => ⟨((-4845381031/562949953421312), (-300875101/70368744177664)), (41/281474976710656), by norm_num⟩
  | 11 => ⟨((2835759975/2251799813685248), (88043599/140737488355328)), (49/2251799813685248), by norm_num⟩
  | 12 => ⟨((-760663269/4503599627370496), (-1511474199/18014398509481984)), (27/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (-3491701147217/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780098280303351/633825300114114700748351602688), (-4138163164753/633825300114114700748351602688)), (5789/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236404605491251/4951760157141521099596496896), (-4654909692579/39614081257132168796771975168)), (3257/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891104482482209/2475880078570760549798248448), (-2472614751033/1237940039285380274899124224)), (6923/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886384875700849/77371252455336267181195264), (-4944540792315/154742504910672534362390528)), (6925/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551032756337125/9671406556917033397649408), (-4634775153963/9671406556917033397649408)), (6495/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157510257128823/75557863725914323419136), (-4054696325577/604462909807314587353088)), (5685/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236236478165623/9444732965739290427392), (-6587508950329/75557863725914323419136)), (4621/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649556290737257/2361183241434822606848), (-4939430504485/4722366482869645213696)), (6935/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623608392801661/590295810358705651712), (-424360287655/36893488147419103232)), (4771/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913085404155199/36893488147419103232), (-8484276581721/73786976294838206464)), (373/2305843009213693952), by norm_num⟩
  | 7 => ⟨((912842190357725/4611686018427387904), (-4770391237367/4611686018427387904)), (13441/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596925729457985/1152921504606846976), (-9535745026395/1152921504606846976)), (841/72057594037927936), by norm_num⟩
  | 5 => ⟨((299286276161617/36028797018963968), (-2084526894601/36028797018963968)), (11791/144115188075855872), by norm_num⟩
  | 4 => ⟨((373866962443449/9007199254740992), (-1561977159523/4503599627370496)), (17723/36028797018963968), by norm_num⟩
  | 3 => ⟨((747008839233421/4503599627370496), (-15599907233389/9007199254740992)), (11107/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118692044819143/2251799813685248), (-1946260806231/281474976710656)), (22307/2251799813685248), by norm_num⟩
  | 1 => ⟨((139378030089761/140737488355328), (-11640246802793/562949953421312)), (16845/562949953421312), by norm_num⟩
  | 0 => ⟨((551947406681423/562949953421312), (-46261944123387/1125899906842624)), (68305/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((551947406681423/562949953421312), (-46261944123387/1125899906842624)), (260562901023482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((67526184171791/70368744177664), (-90715559817569/1125899906842624)), (69777/562949953421312), by norm_num⟩
  | 2 => ⟨((1029466101432473/1125899906842624), (-43525542988393/281474976710656)), (145161/562949953421312), by norm_num⟩
  | 3 => ⟨((914369813393655/1125899906842624), (-159190246950631/562949953421312)), (620699/1125899906842624), by norm_num⟩
  | 4 => ⟨((326275014450033/562949953421312), (-517128584925567/1125899906842624)), (679605/562949953421312), by norm_num⟩
  | 5 => ⟨((281374153968197/2251799813685248), (-599435653182619/1125899906842624)), (5648243/2251799813685248), by norm_num⟩
  | 6 => ⟨((-603126879419135/2251799813685248), (-149805234681673/1125899906842624)), (14851741/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-4092811097/268435456)), (1/268435456), by norm_num⟩, -2, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-90182207/67108864), (-1139114001/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-352364745514777/4503599627370496), (1120661526410187/4503599627370496)), (25144137/4503599627370496), by norm_num⟩
  | 1 => ⟨((75263127/536870912), (-478733993/1073741824)), (11/1073741824), by norm_num⟩
  | 2 => ⟨((-269706841/2147483648), (3431104661/8589934592)), (5/536870912), by norm_num⟩
  | 3 => ⟨((1288666097/17179869184), (-2049238089/8589934592)), (97/17179869184), by norm_num⟩
  | 4 => ⟨((-1154489841/34359738368), (3671741751/34359738368)), (11/4294967296), by norm_num⟩
  | 5 => ⟨((413713621/34359738368), (-5263102441/137438953472)), (1/1073741824), by norm_num⟩
  | 6 => ⟨((-123545883/34359738368), (6286809091/549755813888)), (155/549755813888), by norm_num⟩
  | 7 => ⟨((2023904053/2199023255552), (-1609207103/549755813888)), (161/2199023255552), by norm_num⟩
  | 8 => ⟨((-906587313/4398046511104), (2883312065/4398046511104)), (73/4398046511104), by norm_num⟩
  | 9 => ⟨((1443899025/35184372088832), (-4592179285/35184372088832)), (59/17592186044416), by norm_num⟩
  | 10 => ⟨((-258711975/35184372088832), (3291232287/140737488355328)), (43/70368744177664), by norm_num⟩
  | 11 => ⟨((674254009/562949953421312), (-4288797539/1125899906842624)), (57/562949953421312), by norm_num⟩
  | 12 => ⟨((-402700335/2251799813685248), (5122995735/9007199254740992)), (69/4503599627370496), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646016907/5070602400912917605986812821504), (610740731651/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55621620993773/19807040628566084398385987584), (2894606558407/633825300114114700748351602688)), (5781/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891004938186177/39614081257132168796771975168), (1628018030349/19807040628566084398385987584)), (13009/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472714614977653/618970019642690137449562112), (1729531502187/1237940039285380274899124224)), (13825/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221565519145695/19342813113834066795298816), (864632073845/38685626227668133590597632)), (13827/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775401479351229/4835703278458516698824704), (101306318445/302231454903657293676544)), (12967/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629940717324673/302231454903657293676544), (354501109571/75557863725914323419136)), (11349/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889566658389419/75557863725914323419136), (143982795285/2361183241434822606848)), (18447/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162358680600859/590295810358705651712), (107957979157/147573952589676412928)), (13841/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623275279353191/590295810358705651712), (2374318584915/295147905179352825856)), (19039/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825756214569403/73786976294838206464), (5933525920043/73786976294838206464)), (23811/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912610216629065/4611686018427387904), (1668023799271/2305843009213693952)), (26805/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399116216839967/288230376151711744), (6668194168435/1152921504606846976)), (26827/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598372658766585/72057594037927936), (2915141171025/72057594037927936)), (11749/72057594037927936), by norm_num⟩
  | 4 => ⟨((747437547014281/18014398509481984), (8736651162623/36028797018963968)), (1103/1125899906842624), by norm_num⟩
  | 3 => ⟨((746644415485841/4503599627370496), (5452734282723/4503599627370496)), (22103/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117981300212613/2251799813685248), (2720615742999/562949953421312)), (44335/2251799813685248), by norm_num⟩
  | 1 => ⟨((1114003230790371/1125899906842624), (8133112175603/562949953421312)), (8353/140737488355328), by norm_num⟩
  | 0 => ⟨((137754039880237/140737488355328), (32302832874051/1125899906842624)), (134943/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((137754039880237/140737488355328), (32302832874051/1125899906842624)), (514766697410201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((538871951150619/562949953421312), (63236111145339/1125899906842624)), (271909/1125899906842624), by norm_num⟩
  | 2 => ⟨((128511991403481/140737488355328), (121062863186929/1125899906842624)), (551103/1125899906842624), by norm_num⟩
  | 3 => ⟨((231442648815747/281474976710656), (55273224692909/281474976710656)), (70311/70368744177664), by norm_num⟩
  | 4 => ⟨((1435596752881349/2251799813685248), (727174070306933/2251799813685248)), (4583691/2251799813685248), by norm_num⟩
  | 5 => ⟨((680413906709241/2251799813685248), (927194973343279/2251799813685248)), (4402467/1125899906842624), by norm_num⟩
  | 6 => ⟨((-352364745514777/4503599627370496), (1120661526410187/4503599627370496)), (25144137/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-90182207/67108864), (-1139114001/67108864)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-391763459/268435456), (-4948462187/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((957621392705095/4503599627370496), (105507240556547/1125899906842624)), (11473129/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1777119815/4294967296), (-783186379/4294967296)), (11/2147483648), by norm_num⟩
  | 2 => ⟨((864528871/2147483648), (1524010323/8589934592)), (11/2147483648), by norm_num⟩
  | 3 => ⟨((-4486121345/17179869184), (-1977058103/17179869184)), (59/17179869184), by norm_num⟩
  | 4 => ⟨((4364794527/34359738368), (961794357/17179869184)), (59/34359738368), by norm_num⟩
  | 5 => ⟨((-3397399187/68719476736), (-46789135/2147483648)), (3/4294967296), by norm_num⟩
  | 6 => ⟨((2203677853/137438953472), (1942345657/274877906944)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((-612594157/137438953472), (-539947161/274877906944)), (73/1099511627776), by norm_num⟩
  | 8 => ⟨((4768212749/4398046511104), (2101377321/4398046511104)), (73/4398046511104), by norm_num⟩
  | 9 => ⟨((-2061891907/8796093022208), (-454343495/4398046511104)), (65/17592186044416), by norm_num⟩
  | 10 => ⟨((1604902555/35184372088832), (1414578589/70368744177664)), (13/17592186044416), by norm_num⟩
  | 11 => ⟨((-1135634971/140737488355328), (-500480515/140737488355328)), (19/140737488355328), by norm_num⟩
  | 12 => ⟨((1473229077/1125899906842624), (2597040303/4503599627370496)), (101/4503599627370496), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693180315/10141204801825835211973625643008), (540711157467/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889858851491125/316912650057057350374175801344), (160138306759/158456325028528675187087900672)), (5767/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472702318112045/9903520314283042199192993792), (360264628515/19807040628566084398385987584)), (811/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((945325454653099/1237940039285380274899124224), (191362084823/618970019642690137449562112)), (13787/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886158494834233/77371252455336267181195264), (765320123905/154742504910672534362390528)), (3447/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550609154063583/9671406556917033397649408), (358675708457/4835703278458516698824704)), (12927/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259712266547915/604462909807314587353088), (627546323855/604462909807314587353088)), (707/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1889292530383277/75557863725914323419136), (254876883967/18889465931478580854784)), (18383/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324666130576111/1180591620717411303424), (47775461705/295147905179352825856)), (3447/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622994604628639/590295810358705651712), (1050697485065/590295810358705651712)), (18961/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912703505235163/36893488147419103232), (328207019889/18446744073709551616)), (23703/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456207457658499/2305843009213693952), (184523034135/1152921504606846976)), (13335/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596077076632645/1152921504606846976), (368812673053/288230376151711744)), (26675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196409159788577/144115188075855872), (1289794853107/144115188075855872)), (11673/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494377165097407/36028797018963968), (966297606365/18014398509481984)), (17515/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492677434434951/9007199254740992), (603019626405/2251799813685248)), (21903/4503599627370496), by norm_num⟩
  | 2 => ⟨((2234772756052391/4503599627370496), (4813177886877/4503599627370496)), (21917/1125899906842624), by norm_num⟩
  | 1 => ⟨((2226303734135695/2251799813685248), (7192379848545/2251799813685248)), (65823/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100492673897911/1125899906842624), (3568893999165/562949953421312)), (131935/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1100492673897911/1125899906842624), (3568893999165/562949953421312)), (503292088035201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2151227067211651/2251799813685248), (13953431121647/1125899906842624)), (259589/1125899906842624), by norm_num⟩
  | 2 => ⟨((2054800375070343/2251799813685248), (53320900955641/2251799813685248)), (1004849/2251799813685248), by norm_num⟩
  | 3 => ⟨((1873772898135729/2251799813685248), (97312209208713/2251799813685248)), (470367/562949953421312), by norm_num⟩
  | 4 => ⟨((777501442722903/1125899906842624), (161951323705445/2251799813685248)), (205865/140737488355328), by norm_num⟩
  | 5 => ⟨((531087561149687/1125899906842624), (223674213074551/2251799813685248)), (5022981/2251799813685248), by norm_num⟩
  | 6 => ⟨((957621392705095/4503599627370496), (105507240556547/1125899906842624)), (11473129/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-391763459/268435456), (-4948462187/268435456)), (1/134217728), by norm_num⟩, -3, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-418646879/268435456), (-5288033389/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((39057354066745/281474976710656), (-355612937924911/2251799813685248)), (3465247/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1239280465/4294967296), (352609785/1073741824)), (57/8589934592), by norm_num⟩
  | 2 => ⟨((2577011281/8589934592), (-733231435/2147483648)), (61/8589934592), by norm_num⟩
  | 3 => ⟨((-223281013/1073741824), (4065898415/17179869184)), (87/17179869184), by norm_num⟩
  | 4 => ⟨((3714398511/34359738368), (-2113699517/17179869184)), (47/17179869184), by norm_num⟩
  | 5 => ⟨((-3089549827/68719476736), (1758125833/34359738368)), (81/68719476736), by norm_num⟩
  | 6 => ⟨((133844547/8589934592), (-2437279929/137438953472)), (29/68719476736), by norm_num⟩
  | 7 => ⟨((-1272328737/274877906944), (2896103505/549755813888)), (71/549755813888), by norm_num⟩
  | 8 => ⟨((2645733231/2199023255552), (-3011138969/2199023255552)), (19/549755813888), by norm_num⟩
  | 9 => ⟨((-1222588353/4398046511104), (695720829/2199023255552)), (9/1099511627776), by norm_num⟩
  | 10 => ⟨((254230101/4398046511104), (-2314737269/35184372088832)), (31/17592186044416), by norm_num⟩
  | 11 => ⟨((-3075820411/281474976710656), (1750313031/140737488355328)), (3/8796093022208), by norm_num⟩
  | 12 => ⟨((1065998123/562949953421312), (-2426449085/1125899906842624)), (17/281474976710656), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238520483/10141204801825835211973625643008), (-553547139853/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444890618251097/158456325028528675187087900672), (-1311302184929/633825300114114700748351602688)), (5771/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890634621441709/39614081257132168796771975168), (-368752783121/9903520314283042199192993792)), (6493/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890465319521233/2475880078570760549798248448), (-783474949559/1237940039285380274899124224)), (13799/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772131373932793/154742504910672534362390528), (-1566669355883/154742504910672534362390528)), (1725/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775217555880463/4835703278458516698824704), (-734227254041/4835703278458516698824704)), (12939/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78722497000473/37778931862957161709568), (-1284599753657/604462909807314587353088)), (11323/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889044967697829/75557863725914323419136), (-1043458056871/37778931862957161709568)), (9201/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324619701307647/1180591620717411303424), (-782349281661/2361183241434822606848)), (3451/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202842396316145/73786976294838206464), (-2150666963541/590295810358705651712)), (2373/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912543804167529/36893488147419103232), (-2687143865305/73786976294838206464)), (2967/9223372036854775808), by norm_num⟩
  | 7 => ⟨((912235176467975/4611686018427387904), (-755350408941/2305843009213693952)), (13355/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595717411486807/1152921504606846976), (-3019358843417/1152921504606846976)), (835/36028797018963968), by norm_num⟩
  | 5 => ⟨((299023560621707/36028797018963968), (-659910631997/36028797018963968)), (23391/144115188075855872), by norm_num⟩
  | 4 => ⟨((373476092498375/9007199254740992), (-1977437536271/18014398509481984)), (35109/36028797018963968), by norm_num⟩
  | 3 => ⟨((746042855145203/4503599627370496), (-2467786512465/4503599627370496)), (43925/9007199254740992), by norm_num⟩
  | 2 => ⟨((558396782485343/1125899906842624), (-4923560667883/2251799813685248)), (43983/2251799813685248), by norm_num⟩
  | 1 => ⟨((556129973922375/562949953421312), (-114927750819/17592186044416)), (66121/1125899906842624), by norm_num⟩
  | 0 => ⟨((2197396344421507/2251799813685248), (-29182574497551/2251799813685248)), (66415/562949953421312), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2197396344421507/2251799813685248), (-29182574497551/2251799813685248)), (253353121043968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1071964533099811/1125899906842624), (-56955047364339/2251799813685248)), (262685/1125899906842624), by norm_num⟩
  | 2 => ⟨((254973151674071/281474976710656), (-54226659390003/1125899906842624)), (1026983/2251799813685248), by norm_num⟩
  | 3 => ⟨((1842509076164485/2251799813685248), (-49121035237311/562949953421312)), (122469/140737488355328), by norm_num⟩
  | 4 => ⟨((1490467162181349/2251799813685248), (-321541738143129/2251799813685248)), (3548643/2251799813685248), by norm_num⟩
  | 5 => ⟨((940626808520059/2251799813685248), (-106414300032453/562949953421312)), (2855571/1125899906842624), by norm_num⟩
  | 6 => ⟨((39057354066745/281474976710656), (-355612937924911/2251799813685248)), (3465247/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-418646879/268435456), (-5288033389/268435456)), (1/134217728), by norm_num⟩, -3, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile021Terms0
