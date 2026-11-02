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
namespace Reinmann.XiRectangle.Tile026Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7191/640))
  have he : value ((7/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-325614239/536870912), (-4181235703/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((80759587551247/2251799813685248), (-1225143666162697/2251799813685248)), (5909583/1125899906842624), by norm_num⟩
  | 1 => ⟨((-213540193/8589934592), (1619729763/4294967296)), (65/17179869184), by norm_num⟩
  | 2 => ⟨((296029565/34359738368), (-2245422237/17179869184)), (47/34359738368), by norm_num⟩
  | 3 => ⟨((-273589411/137438953472), (4150421581/137438953472)), (45/137438953472), by norm_num⟩
  | 4 => ⟨((189637729/549755813888), (-2876853017/549755813888)), (65/1099511627776), by norm_num⟩
  | 5 => ⟨((-420629943/8796093022208), (6381064185/8796093022208)), (37/4398046511104), by norm_num⟩
  | 6 => ⟨((97186153/17592186044416), (-1474338883/17592186044416)), (35/35184372088832), by norm_num⟩
  | 7 => ⟨((-153975561/281474976710656), (2335848777/281474976710656)), (57/562949953421312), by norm_num⟩
  | 8 => ⟨((53363863/1125899906842624), (-809543497/1125899906842624)), (81/9007199254740992), by norm_num⟩
  | 9 => ⟨((-526065937/144115188075855872), (7980555271/144115188075855872)), (51/72057594037927936), by norm_num⟩
  | 10 => ⟨((291712897/1152921504606846976), (-4425359509/1152921504606846976)), (29/576460752303423488), by norm_num⟩
  | 11 => ⟨((-147054525/9223372036854775808), (2230854885/9223372036854775808)), (15/4611686018427387904), by norm_num⟩
  | 12 => ⟨((135907239/147573952589676412928), (-4123495397/295147905179352825856)), (57/295147905179352825856), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791592864105897/5070602400912917605986812821504), (-1960395484497/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781032153544843/633825300114114700748351602688), (-290705924633/79228162514264337593543950336)), (2889/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946143865313393/19807040628566084398385987584), (-1308103005157/19807040628566084398385987584)), (6501/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((473055352038715/618970019642690137449562112), (-2779546269137/2475880078570760549798248448)), (1727/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773887080243311/154742504910672534362390528), (-2779352050367/154742504910672534362390528)), (3455/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776040340129287/4835703278458516698824704), (-325679521229/1208925819614629174706176)), (6479/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315249854582649/151115727451828646838272), (-2279550248787/604462909807314587353088)), (5671/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945691669565549/37778931862957161709568), (-1851941053497/37778931862957161709568)), (9/73786976294838206464), by norm_num⟩
  | 10 => ⟨((1300231917750741/4722366482869645213696), (-86799152071/147573952589676412928)), (3457/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625148618128761/590295810358705651712), (-3818612191739/590295810358705651712)), (4755/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828097795052251/73786976294838206464), (-2386219667337/36893488147419103232)), (2973/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456963645575707/2305843009213693952), (-5367858379023/9223372036854775808)), (6693/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399774713361269/288230376151711744), (-5366438159205/1152921504606846976)), (13395/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199049869677621/144115188075855872), (-1173508780335/36028797018963968)), (5865/72057594037927936), by norm_num⟩
  | 4 => ⟨((93645721563479/2251799813685248), (-7037854846633/36028797018963968)), (8807/18014398509481984), by norm_num⟩
  | 3 => ⟨((748804360683937/4503599627370496), (-8791719428757/9007199254740992)), (5513/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122300154280771/2251799813685248), (-8783314914521/2251799813685248)), (2763/281474976710656), by norm_num⟩
  | 1 => ⟨((1120478829173769/1125899906842624), (-822121299083/70368744177664)), (8321/281474976710656), by norm_num⟩
  | 0 => ⟨((557486117676151/562949953421312), (-26223633970607/1125899906842624)), (67085/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557486117676151/562949953421312), (-26223633970607/1125899906842624)), (255908970359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1103539843175025/1125899906842624), (-51938229339165/1125899906842624)), (67997/562949953421312), by norm_num⟩
  | 2 => ⟨((1079227912199939/1125899906842624), (-101813500669811/1125899906842624)), (139567/562949953421312), by norm_num⟩
  | 3 => ⟨((256320941705645/281474976710656), (-48796509837977/281474976710656)), (585611/1125899906842624), by norm_num⟩
  | 4 => ⟨((449910869694043/562949953421312), (-355486445005767/1125899906842624)), (39675/35184372088832), by norm_num⟩
  | 5 => ⟨((151724977047199/281474976710656), (-568211133742793/1125899906842624)), (2831051/1125899906842624), by norm_num⟩
  | 6 => ⟨((80759587551247/2251799813685248), (-1225143666162697/2251799813685248)), (5909583/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-325614239/536870912), (-4181235703/536870912)), (1/268435456), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-516086359/536870912), (-6627101795/536870912)), (3/536870912), by norm_num⟩
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
  | 0 => ⟨((839876376452493/2251799813685248), (379916419147941/4503599627370496)), (12015021/4503599627370496), by norm_num⟩
  | 1 => ⟨((-879953869/2147483648), (-796090787/8589934592)), (27/8589934592), by norm_num⟩
  | 2 => ⟨((483364067/2147483648), (437297561/8589934592)), (1/536870912), by norm_num⟩
  | 3 => ⟨((-2832158421/34359738368), (-1281121265/68719476736)), (49/68719476736), by norm_num⟩
  | 4 => ⟨((3111444045/137438953472), (1407455565/274877906944)), (7/34359738368), by norm_num⟩
  | 5 => ⟨((-2734616531/549755813888), (-77312399/68719476736)), (13/274877906944), by norm_num⟩
  | 6 => ⟨((4005711101/4398046511104), (905987751/4398046511104)), (5/549755813888), by norm_num⟩
  | 7 => ⟨((-2514699109/17592186044416), (-1137519173/35184372088832)), (53/35184372088832), by norm_num⟩
  | 8 => ⟨((5525358687/281474976710656), (624846271/140737488355328)), (15/70368744177664), by norm_num⟩
  | 9 => ⟨((-1348939323/562949953421312), (-610190037/1125899906842624)), (61/2251799813685248), by norm_num⟩
  | 10 => ⟨((2371138107/9007199254740992), (1072579637/18014398509481984)), (7/2251799813685248), by norm_num⟩
  | 11 => ⟨((-3789034855/144115188075855872), (-428490607/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 12 => ⟨((5550240339/2305843009213693952), (313830031/576460752303423488)), (71/2305843009213693952), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582723585083759/10141204801825835211973625643008), (289741996799/10141204801825835211973625643008)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780486884398503/633825300114114700748351602688), (21470289209/39614081257132168796771975168)), (1081/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891674517432193/39614081257132168796771975168), (386431958491/39614081257132168796771975168)), (9729/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891570130096733/2475880078570760549798248448), (51317959311/309485009821345068724781056)), (10337/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773236095721039/154742504910672534362390528), (205249182317/77371252455336267181195264)), (5169/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551470694097271/9671406556917033397649408), (384794082081/9671406556917033397649408)), (2423/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260465992207587/604462909807314587353088), (336646694885/604462909807314587353088)), (8481/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945258553059271/37778931862957161709568), (136740164453/18889465931478580854784)), (13781/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299582754246077/4722366482869645213696), (410141566281/4722366482869645213696)), (10337/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812128424429495/295147905179352825856), (563816428299/590295810358705651712)), (14213/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228373041108631/9223372036854775808), (704578251895/73786976294838206464)), (17767/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913301822297621/4611686018427387904), (792386232173/9223372036854775808)), (9995/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597850054400159/1152921504606846976), (396027994237/576460752303423488)), (19991/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18718118360973/2251799813685248), (692677648293/144115188075855872)), (17495/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496700908814285/36028797018963968), (259568561325/9007199254740992)), (13123/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495578828112773/9007199254740992), (1296544934707/9007199254740992)), (32815/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120282848198939/2251799813685248), (2589200352675/4503599627370496)), (16413/1125899906842624), by norm_num⟩
  | 1 => ⟨((2234968565224429/2251799813685248), (242130691805/140737488355328)), (98535/2251799813685248), by norm_num⟩
  | 0 => ⟨((1109108460273639/1125899906842624), (7709430169075/2251799813685248)), (49325/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109108460273639/1125899906842624), (7709430169075/2251799813685248)), (188159944774436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1092554240697811/1125899906842624), (15188906531467/2251799813685248)), (390067/2251799813685248), by norm_num⟩
  | 2 => ⟨((2120289887035591/2251799813685248), (29478116379019/2251799813685248)), (190573/562949953421312), by norm_num⟩
  | 3 => ⟨((499018631496833/562949953421312), (55513062633221/2251799813685248)), (90969/140737488355328), by norm_num⟩
  | 4 => ⟨((884011045070883/1125899906842624), (3075545656531/70368744177664)), (2652185/2251799813685248), by norm_num⟩
  | 5 => ⟨((691938976026885/1125899906842624), (154546815451407/2251799813685248)), (4396611/2251799813685248), by norm_num⟩
  | 6 => ⟨((839876376452493/2251799813685248), (379916419147941/4503599627370496)), (12015021/4503599627370496), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516086359/536870912), (-6627101795/536870912)), (3/536870912), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-325614239/268435456), (-4181235703/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-1327342584073969/4503599627370496), (-175756471013169/4503599627370496)), (27679831/4503599627370496), by norm_num⟩
  | 1 => ⟨((3509688453/8589934592), (464725885/8589934592)), (149/17179869184), by norm_num⟩
  | 2 => ⟨((-76022833/268435456), (-322123437/8589934592)), (105/17179869184), by norm_num⟩
  | 3 => ⟨((2248320527/17179869184), (595410539/34359738368)), (99/34359738368), by norm_num⟩
  | 4 => ⟨((-3116834069/68719476736), (-825414273/137438953472)), (35/34359738368), by norm_num⟩
  | 5 => ⟨((6913359191/549755813888), (457706861/274877906944)), (79/274877906944), by norm_num⟩
  | 6 => ⟨((-199665643/68719476736), (-846021921/2199023255552)), (37/549755813888), by norm_num⟩
  | 7 => ⟨((5061400777/8796093022208), (167547917/2199023255552)), (119/8796093022208), by norm_num⟩
  | 8 => ⟨((-7016591357/70368744177664), (-464541465/35184372088832)), (167/70368744177664), by norm_num⟩
  | 9 => ⟨((4323138237/281474976710656), (286218317/140737488355328)), (13/35184372088832), by norm_num⟩
  | 10 => ⟨((-4794513729/2251799813685248), (-317426271/1125899906842624)), (59/1125899906842624), by norm_num⟩
  | 11 => ⟨((4833896253/18014398509481984), (80008409/2251799813685248)), (121/18014398509481984), by norm_num⟩
  | 12 => ⟨((-4467468745/144115188075855872), (-591547767/144115188075855872)), (57/72057594037927936), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689318205/10141204801825835211973625643008), (-1960395484497/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890043371285489/316912650057057350374175801344), (-2323325156289/316912650057057350374175801344)), (11583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891223724690881/39614081257132168796771975168), (-5226883670773/39614081257132168796771975168)), (6517/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945545184380933/1237940039285380274899124224), (-1388218112019/618970019642690137449562112)), (13853/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772755441388343/154742504910672534362390528), (-2776047151273/77371252455336267181195264)), (6929/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48469347881831/302231454903657293676544), (-1301065367781/2417851639229258349412352)), (12997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260069927536057/604462909807314587353088), (-4552901672159/604462909807314587353088)), (5689/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889871724355345/75557863725914323419136), (-3698456999819/37778931862957161709568)), (9249/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299097164215677/4722366482869645213696), (-5546327807979/4722366482869645213696)), (6941/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623586639441643/590295810358705651712), (-1905998445593/147573952589676412928)), (19101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456535696324129/18446744073709551616), (-9526680566905/73786976294838206464)), (2987/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1825651712792203/9223372036854775808), (-10712960108161/9223372036854775808)), (26911/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596891635530683/1152921504606846976), (-5353631354989/576460752303423488)), (13473/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197113670319877/144115188075855872), (-9362441204147/144115188075855872)), (23617/144115188075855872), by norm_num⟩
  | 4 => ⟨((747708749646729/18014398509481984), (-14030824272293/36028797018963968)), (2219/2251799813685248), by norm_num⟩
  | 3 => ⟨((1493949154046593/9007199254740992), (-17516041804289/9007199254740992)), (22259/4503599627370496), by norm_num⟩
  | 2 => ⟨((559307582386785/1125899906842624), (-17482263540973/2251799813685248)), (44725/2251799813685248), by norm_num⟩
  | 1 => ⟨((557444057599779/562949953421312), (-204209309719/8796093022208)), (33803/562949953421312), by norm_num⟩
  | 0 => ⟨((1103539843175025/1125899906842624), (-12984557334791/281474976710656)), (137295/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1103539843175025/1125899906842624), (-12984557334791/281474976710656)), (523738865378951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1079227912199939/1125899906842624), (-101813500669809/1125899906842624)), (281805/1125899906842624), by norm_num⟩
  | 2 => ⟨((1025283766822581/1125899906842624), (-195186039351905/1125899906842624)), (295607/562949953421312), by norm_num⟩
  | 3 => ⟨((899821739388089/1125899906842624), (-177743222502881/562949953421312)), (1281747/1125899906842624), by norm_num⟩
  | 4 => ⟨((151724977047201/281474976710656), (-568211133742787/1125899906842624)), (2858137/1125899906842624), by norm_num⟩
  | 5 => ⟨((20189896887819/562949953421312), (-306285916540675/562949953421312)), (5966123/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1327342584073969/4503599627370496), (-175756471013169/4503599627370496)), (27679831/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-325614239/268435456), (-4181235703/268435456)), (1/134217728), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-378026425/268435456), (-4854264325/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((793787262108353/4503599627370496), (381796032321759/2251799813685248)), (7658673/2251799813685248), by norm_num⟩
  | 1 => ⟨((-304591969/1073741824), (-2344043767/8589934592)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1960887451/8589934592), (3772592907/17179869184)), (79/17179869184), by norm_num⟩
  | 3 => ⟨((-4207902141/34359738368), (-4047836035/34359738368)), (87/34359738368), by norm_num⟩
  | 4 => ⟨((3386178619/68719476736), (3257370389/68719476736)), (9/8589934592), by norm_num⟩
  | 5 => ⟨((-2179937699/137438953472), (-4194028319/274877906944)), (95/274877906944), by norm_num⟩
  | 6 => ⟨((292372865/68719476736), (1125004697/274877906944)), (53/549755813888), by norm_num⟩
  | 7 => ⟨((-1075556511/1099511627776), (-4138571911/4398046511104)), (25/1099511627776), by norm_num⟩
  | 8 => ⟨((865520713/4398046511104), (3330387269/17592186044416)), (83/17592186044416), by norm_num⟩
  | 9 => ⟨((-619111933/17592186044416), (-1191122563/35184372088832)), (61/70368744177664), by norm_num⟩
  | 10 => ⟨((3188551095/562949953421312), (1533630249/281474976710656)), (81/562949953421312), by norm_num⟩
  | 11 => ⟨((-3732200013/4503599627370496), (-3590229333/4503599627370496)), (97/4503599627370496), by norm_num⟩
  | 12 => ⟨((1001124033/9007199254740992), (3852167469/36028797018963968)), (53/18014398509481984), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353601407/10141204801825835211973625643008), (249454079773/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779796148313455/633825300114114700748351602688), (295540595225/158456325028528675187087900672)), (11541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945448740680195/19807040628566084398385987584), (664883125291/19807040628566084398385987584)), (1623/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472686144649981/618970019642690137449562112), (353168394655/618970019642690137449562112)), (3449/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443102649931959/38685626227668133590597632), (706222589949/77371252455336267181195264)), (6899/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550696850581099/9671406556917033397649408), (82745295605/604462909807314587353088)), (12937/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157473617264235/75557863725914323419136), (579095782527/302231454903657293676544)), (11321/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944708501910467/37778931862957161709568), (940803290391/37778931862957161709568)), (9199/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298757774313585/4722366482869645213696), (1410807174907/4722366482869645213696)), (13801/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623122658758501/590295810358705651712), (969606857819/295147905179352825856)), (18979/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228195853405189/9223372036854775808), (2423048289317/73786976294838206464)), (11865/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825009279823315/9223372036854775808), (1362298874923/4611686018427387904)), (13351/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798128047709689/576460752303423488), (2722934180363/1152921504606846976)), (26711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196565317635735/144115188075855872), (2380697129089/144115188075855872)), (23383/144115188075855872), by norm_num⟩
  | 4 => ⟨((747305218106621/18014398509481984), (3567308226589/36028797018963968)), (35093/36028797018963968), by norm_num⟩
  | 3 => ⟨((373241834216561/2251799813685248), (4452601664025/9007199254740992)), (21951/4503599627370496), by norm_num⟩
  | 2 => ⟨((69854609851017/140737488355328), (1110703779539/562949953421312)), (21977/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113576653289113/1125899906842624), (13279609686303/2251799813685248)), (66063/1125899906842624), by norm_num⟩
  | 0 => ⟨((137664657115169/140737488355328), (13182229056125/1125899906842624)), (265311/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((137664657115169/140737488355328), (13182229056125/1125899906842624)), (1012081154830168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2154233998705527/2251799813685248), (51577644712355/2251799813685248)), (262625/1125899906842624), by norm_num⟩
  | 2 => ⟨((2059714118260883/2251799813685248), (98685784710737/2251799813685248)), (1029047/2251799813685248), by norm_num⟩
  | 3 => ⟨((1879689011045841/2251799813685248), (11283446623731/140737488355328)), (1972729/2251799813685248), by norm_num⟩
  | 4 => ⟨((1554595492031555/2251799813685248), (150701642278857/1125899906842624)), (56403/35184372088832), by norm_num⟩
  | 5 => ⟨((32278668681033/70368744177664), (416165046829887/2251799813685248)), (46489/17592186044416), by norm_num⟩
  | 6 => ⟨((793787262108353/4503599627370496), (381796032321759/2251799813685248)), (7658673/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-378026425/268435456), (-4854264325/268435456)), (1/134217728), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-420850299/268435456), (-5404168749/268435456)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((266945725126107/4503599627370496), (-900282760619321/4503599627370496)), (4235033/2251799813685248), by norm_num⟩
  | 1 => ⟨((-456144839/4294967296), (1538362657/4294967296)), (15/4294967296), by norm_num⟩
  | 2 => ⟨((1634603669/17179869184), (-1378187929/4294967296)), (7/2147483648), by norm_num⟩
  | 3 => ⟨((-976272201/17179869184), (3292508363/17179869184)), (69/34359738368), by norm_num⟩
  | 4 => ⟨((1749244961/68719476736), (-5899383037/68719476736)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((-1253690489/137438953472), (528513771/17179869184)), (47/137438953472), by norm_num⟩
  | 6 => ⟨((374385301/137438953472), (-5050504287/549755813888)), (29/274877906944), by norm_num⟩
  | 7 => ⟨((-766638181/1099511627776), (2585511109/1099511627776)), (61/2199023255552), by norm_num⟩
  | 8 => ⟨((343407805/2199023255552), (-4632614013/8796093022208)), (57/8796093022208), by norm_num⟩
  | 9 => ⟨((-1093874109/35184372088832), (461140557/4398046511104)), (47/35184372088832), by norm_num⟩
  | 10 => ⟨((783983717/140737488355328), (-2644009471/140737488355328)), (69/281474976710656), by norm_num⟩
  | 11 => ⟨((-510803727/562949953421312), (1722701457/562949953421312)), (47/1125899906842624), by norm_num⟩
  | 12 => ⟨((1220316553/9007199254740992), (-4115555531/9007199254740992)), (29/4503599627370496), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790966773095085/5070602400912917605986812821504), (-835326743849/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889774317462241/316912650057057350374175801344), (-989392663539/316912650057057350374175801344)), (361/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945309493815489/19807040628566084398385987584), (-2225822890115/39614081257132168796771975168)), (3249/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945224312285873/1237940039285380274899124224), (-1182279136849/1237940039285380274899124224)), (6905/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443028646127305/38685626227668133590597632), (-591033121751/38685626227668133590597632)), (3453/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550419271346789/9671406556917033397649408), (-2215921892709/9671406556917033397649408)), (1619/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259545991370985/604462909807314587353088), (-484619859327/151115727451828646838272)), (5667/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889022093766755/75557863725914323419136), (-3149181377295/75557863725914323419136)), (9211/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162307685686275/590295810358705651712), (-1180572245047/2361183241434822606848)), (3455/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405678772282907/147573952589676412928), (-1622684522611/295147905179352825856)), (297/18446744073709551616), by norm_num⟩
  | 8 => ⟨((912528553420701/36893488147419103232), (-4054905025817/73786976294838206464)), (2971/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456108872432257/2305843009213693952), (-2279642797007/4611686018427387904)), (209/144115188075855872), by norm_num⟩
  | 6 => ⟨((1595681862933749/1152921504606846976), (-2278092003731/576460752303423488)), (13383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196062367775743/144115188075855872), (-995793484873/36028797018963968)), (11719/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493855021687015/36028797018963968), (-1491948079405/9007199254740992)), (8797/18014398509481984), by norm_num⟩
  | 3 => ⟨((746010671855025/4503599627370496), (-3723778913185/4503599627370496)), (11011/4503599627370496), by norm_num⟩
  | 2 => ⟨((2233450382028795/4503599627370496), (-3714654442549/1125899906842624)), (44131/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112147418827657/1125899906842624), (-11098428109991/1125899906842624)), (33209/1125899906842624), by norm_num⟩
  | 0 => ⟨((549216771544575/562949953421312), (-11007618817101/562949953421312)), (66861/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549216771544575/562949953421312), (-11007618817101/562949953421312)), (255054478171920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((535603374050139/562949953421312), (-42956350434917/1125899906842624)), (133075/1125899906842624), by norm_num⟩
  | 2 => ⟨((127191440616779/140737488355328), (-20434823815149/281474976710656)), (16461/70368744177664), by norm_num⟩
  | 3 => ⟨((456829725978951/562949953421312), (-147743701279459/1125899906842624)), (257147/562949953421312), by norm_num⟩
  | 4 => ⟨((1444081108708879/2251799813685248), (-479571685976135/2251799813685248)), (1939333/2251799813685248), by norm_num⟩
  | 5 => ⟨((205988697936629/562949953421312), (-615099448699577/2251799813685248)), (1656721/1125899906842624), by norm_num⟩
  | 6 => ⟨((266945725126107/4503599627370496), (-900282760619321/4503599627370496)), (4235033/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-420850299/268435456), (-5404168749/268435456)), (1/268435456), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-57132171/33554432), (-5869106315/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-50870483613577/281474976710656), (-207895661189875/9007199254740992)), (17072363/4503599627370496), by norm_num⟩
  | 1 => ⟨((6041832907/17179869184), (192902697/4294967296)), (129/17179869184), by norm_num⟩
  | 2 => ⟨((-2939215993/8589934592), (-93842829/2147483648)), (127/17179869184), by norm_num⟩
  | 3 => ⟨((3812966821/17179869184), (121739809/4294967296)), (21/4294967296), by norm_num⟩
  | 4 => ⟨((-7419690835/68719476736), (-947578919/68719476736)), (83/34359738368), by norm_num⟩
  | 5 => ⟨((5775220679/137438953472), (368780687/68719476736)), (131/137438953472), by norm_num⟩
  | 6 => ⟨((-7492040355/549755813888), (-956818775/549755813888)), (43/137438953472), by norm_num⟩
  | 7 => ⟨((520672763/137438953472), (132991669/274877906944)), (97/1099511627776), by norm_num⟩
  | 8 => ⟨((-4052729655/4398046511104), (-517579677/4398046511104)), (3/137438953472), by norm_num⟩
  | 9 => ⟨((7009998015/35184372088832), (447628243/17592186044416)), (21/4398046511104), by norm_num⟩
  | 10 => ⟨((-5456330513/140737488355328), (-696835473/140737488355328)), (33/35184372088832), by norm_num⟩
  | 11 => ⟨((482614951/70368744177664), (61635419/70368744177664)), (95/562949953421312), by norm_num⟩
  | 12 => ⟨((-5008668433/4503599627370496), (-639663933/4503599627370496)), (125/4503599627370496), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847530181/10141204801825835211973625643008), (-1963406281643/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444832771543733/158456325028528675187087900672), (-2325015592887/316912650057057350374175801344)), (11583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118148358458477/2475880078570760549798248448), (-2615233725665/19807040628566084398385987584)), (6517/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890187388748065/2475880078570760549798248448), (-5556402435599/2475880078570760549798248448)), (6927/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771852611941399/154742504910672534362390528), (-5555311893807/154742504910672534362390528)), (6929/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193771611213247/1208925819614629174706176), (-5206946190243/9671406556917033397649408)), (12997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259329625562545/604462909807314587353088), (-4554919195271/604462909807314587353088)), (5689/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472167258587169/18889465931478580854784), (-7399571067257/75557863725914323419136)), (18497/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298195410101451/4722366482869645213696), (-5547777231289/4722366482869645213696)), (6941/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405586789016293/147573952589676412928), (-1906276103809/147573952589676412928)), (19101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824594074781389/73786976294838206464), (-9526746534177/73786976294838206464)), (2987/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823910300033071/9223372036854775808), (-10711218015693/9223372036854775808)), (26911/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595151333192891/1152921504606846976), (-5351626535407/576460752303423488)), (13473/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195592158027173/144115188075855872), (-9356385680069/144115188075855872)), (11809/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493137742909359/36028797018963968), (-1752082070233/4503599627370496)), (35505/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491103871585445/9007199254740992), (-17489456386065/9007199254740992)), (44519/9007199254740992), by norm_num⟩
  | 2 => ⟨((557888267764587/1125899906842624), (-8721204204569/1125899906842624)), (44727/2251799813685248), by norm_num⟩
  | 1 => ⟨((277661730394109/281474976710656), (-13022994326173/562949953421312)), (67611/1125899906842624), by norm_num⟩
  | 0 => ⟨((273781288614595/281474976710656), (-51621467234413/1125899906842624)), (137313/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((273781288614595/281474976710656), (-51621467234413/1125899906842624)), (523807529929732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1062824786444645/1125899906842624), (-50210473359917/562949953421312)), (8741/35184372088832), by norm_num⟩
  | 2 => ⟨((994326541229105/1125899906842624), (-189590336766935/1125899906842624)), (577981/1125899906842624), by norm_num⟩
  | 3 => ⟨((846203795743281/1125899906842624), (-334869383436725/1125899906842624)), (1215529/1125899906842624), by norm_num⟩
  | 4 => ⟨((536391695475519/1125899906842624), (-31460139309477/70368744177664)), (5100379/2251799813685248), by norm_num⟩
  | 5 => ⟨((122009131473343/4503599627370496), (-479615137695259/1125899906842624)), (2355067/562949953421312), by norm_num⟩
  | 6 => ⟨((-50870483613577/281474976710656), (-207895661189875/9007199254740992)), (17072363/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57132171/33554432), (-5869106315/268435456)), (1/134217728), by norm_num⟩, -3, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-488421359/268435456), (-3135926777/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-71614396475129/2251799813685248), (357933979343463/2251799813685248)), (30792227/9007199254740992), by norm_num⟩
  | 1 => ⟨((1136153801/17179869184), (-1419644901/4294967296)), (31/4294967296), by norm_num⟩
  | 2 => ⟨((-590641353/8589934592), (1476034291/4294967296)), (33/4294967296), by norm_num⟩
  | 3 => ⟨((818802777/17179869184), (-4092436029/17179869184)), (93/17179869184), by norm_num⟩
  | 4 => ⟨((-851326255/34359738368), (4254990743/34359738368)), (99/34359738368), by norm_num⟩
  | 5 => ⟨((88514159/8589934592), (-7078403609/137438953472)), (21/17179869184), by norm_num⟩
  | 6 => ⟨((-245413359/68719476736), (4906375505/274877906944)), (119/274877906944), by norm_num⟩
  | 7 => ⟨((1166451963/1099511627776), (-2915006013/549755813888)), (9/68719476736), by norm_num⟩
  | 8 => ⟨((-606392167/2199023255552), (3030792299/2199023255552)), (19/549755813888), by norm_num⟩
  | 9 => ⟨((560425361/8796093022208), (-5602093699/17592186044416)), (143/17592186044416), by norm_num⟩
  | 10 => ⟨((-932297421/70368744177664), (291230659/4398046511104)), (61/35184372088832), by norm_num⟩
  | 11 => ⟨((1409933081/562949953421312), (-1761737107/140737488355328)), (187/562949953421312), by norm_num⟩
  | 12 => ⟨((-244322785/562949953421312), (4884572435/2251799813685248)), (33/562949953421312), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581605650422191/10141204801825835211973625643008), (2303363932821/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444789614578283/158456325028528675187087900672), (1363529564781/316912650057057350374175801344)), (1445/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945089998907315/19807040628566084398385987584), (1533722436475/19807040628566084398385987584)), (6503/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472495534892185/618970019642690137449562112), (814638630651/618970019642690137449562112)), (6911/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771648033991651/154742504910672534362390528), (3257873280229/154742504910672534362390528)), (13825/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774990905354545/4835703278458516698824704), (3053532518873/9671406556917033397649408)), (12963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259163143877495/604462909807314587353088), (1335558714303/302231454903657293676544)), (5673/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888399836593597/75557863725914323419136), (1084802385673/18889465931478580854784)), (18443/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297994679058837/4722366482869645213696), (3253220744413/4722366482869645213696)), (13837/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50689782691659/18446744073709551616), (2235625612155/295147905179352825856)), (9517/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824254277499671/73786976294838206464), (5586174168599/73786976294838206464)), (5951/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911765964408383/4611686018427387904), (3140237073073/4611686018427387904)), (26795/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199347228899845/144115188075855872), (6275512053709/1152921504606846976)), (419/18014398509481984), by norm_num⟩
  | 5 => ⟨((37352212889641/4503599627370496), (5485494335737/144115188075855872)), (23487/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492666638980801/36028797018963968), (8217093187047/36028797018963968)), (35277/36028797018963968), by norm_num⟩
  | 3 => ⟨((186316755031139/1125899906842624), (10251877415789/9007199254740992)), (44177/9007199254740992), by norm_num⟩
  | 2 => ⟨((278808793457977/562949953421312), (20445369558971/4503599627370496)), (88597/4503599627370496), by norm_num⟩
  | 1 => ⟨((2219811384259995/2251799813685248), (119228038517/8796093022208)), (133505/2251799813685248), by norm_num⟩
  | 0 => ⟨((1093923784241007/1125899906842624), (15115942391545/562949953421312)), (134729/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1093923784241007/1125899906842624), (15115942391545/562949953421312)), (513950352195357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((265511008483849/281474976710656), (58746568155243/1125899906842624)), (269041/1125899906842624), by norm_num⟩
  | 2 => ⟨((1997489055490131/2251799813685248), (6926841569605/70368744177664)), (535641/1125899906842624), by norm_num⟩
  | 3 => ⟨((437520003055227/562949953421312), (196625510176319/1125899906842624)), (2111497/2251799813685248), by norm_num⟩
  | 4 => ⟨((161433848742495/281474976710656), (152815704647009/562949953421312)), (2009787/1125899906842624), by norm_num⟩
  | 5 => ⟨((574764488394643/2251799813685248), (350576490141393/1125899906842624)), (1698237/562949953421312), by norm_num⟩
  | 6 => ⟨((-71614396475129/2251799813685248), (357933979343463/2251799813685248)), (30792227/9007199254740992), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-488421359/268435456), (-3135926777/134217728)), (1/134217728), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile026Terms0
