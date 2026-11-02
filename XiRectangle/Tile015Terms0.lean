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
namespace Reinmann.XiRectangle.Tile015Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4371/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4371/640))
  have he : value ((3/4), (4371/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-8931133415/17179869184), (-2541535427/536870912)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((14452375478589/1125899906842624), (669308073061455/1125899906842624)), (25511/140737488355328), by norm_num⟩
  | 1 => ⟨((-2445708817/274877906944), (-113263916935/274877906944)), (37/274877906944), by norm_num⟩
  | 2 => ⟨((1695236171/549755813888), (39254282341/274877906944)), (7/137438953472), by norm_num⟩
  | 3 => ⟨((-97920681/137438953472), (-72557320345/2199023255552)), (7/549755813888), by norm_num⟩
  | 4 => ⟨((2171950207/17592186044416), (25146451013/4398046511104)), (41/17592186044416), by norm_num⟩
  | 5 => ⟨((-602192465/35184372088832), (-111553226373/140737488355328)), (3/8796093022208), by norm_num⟩
  | 6 => ⟨((2226176049/1125899906842624), (103097072457/1125899906842624)), (47/1125899906842624), by norm_num⟩
  | 7 => ⟨((-55109559/281474976710656), (-10208777871/1125899906842624)), (39/9007199254740992), by norm_num⟩
  | 8 => ⟨((611184567/36028797018963968), (28304742393/36028797018963968)), (7/18014398509481984), by norm_num⟩
  | 9 => ⟨((-1506278611/1152921504606846976), (-69757697373/1152921504606846976)), (9/288230376151711744), by norm_num⟩
  | 10 => ⟨((417629109/4611686018427387904), (38681881005/9223372036854775808)), (21/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-1684238193/295147905179352825856), (-77999234203/295147905179352825856)), (11/73786976294838206464), by norm_num⟩
  | 12 => ⟨((778283303/2361183241434822606848), (72086599031/4722366482869645213696)), (43/4722366482869645213696), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455347/5070602400912917605986812821504), (252251832591/1267650600228229401496703205376)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222645735249995/79228162514264337593543950336), (2394343413757/633825300114114700748351602688)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892438156271805/39614081257132168796771975168), (1346752609813/19807040628566084398385987584)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946190606695057/1237940039285380274899124224), (2861696847939/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774046860709639/154742504910672534362390528), (178845332021/9671406556917033397649408)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((194028806015677/1208925819614629174706176), (2682497695557/9671406556917033397649408)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261130438889969/604462909807314587353088), (586750791791/151115727451828646838272)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891596198174355/75557863725914323419136), (3813538235985/75557863725914323419136)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162548939853771/590295810358705651712), (1429927218941/2361183241434822606848)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625367999393085/590295810358705651712), (3931813462455/590295810358705651712)), (149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828371916276619/73786976294838206464), (2457018511555/36893488147419103232)), (93/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828162823773179/9223372036854775808), (5527287811111/9223372036854775808)), (105/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599406913717935/1152921504606846976), (5526032474603/1152921504606846976)), (105/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199319218481843/144115188075855872), (2416932712275/72057594037927936)), (367/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498735160135091/36028797018963968), (7247970314697/36028797018963968)), (69/4503599627370496), by norm_num⟩
  | 3 => ⟨((1498112525626401/9007199254740992), (9055010069217/9007199254740992)), (345/4503599627370496), by norm_num⟩
  | 2 => ⟨((561401442802263/1125899906842624), (2261893144337/562949953421312)), (173/562949953421312), by norm_num⟩
  | 1 => ⟨((1121230240431393/1125899906842624), (3388184077521/281474976710656)), (521/562949953421312), by norm_num⟩
  | 0 => ⟨((1116464294742199/1125899906842624), (13515404993287/562949953421312)), (2099/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1116464294742199/1125899906842624), (13515404993287/562949953421312)), (8007053855514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1106458797247059/1125899906842624), (53608556186139/1125899906842624)), (533/140737488355328), by norm_num⟩
  | 2 => ⟨((67800054054881/70368744177664), (26341443959351/281474976710656)), (2197/281474976710656), by norm_num⟩
  | 3 => ⟨((517670781673395/562949953421312), (203039158387539/1125899906842624)), (4645/281474976710656), by norm_num⟩
  | 4 => ⟨((915451939102723/1125899906842624), (186708319618819/562949953421312)), (40873/1125899906842624), by norm_num⟩
  | 5 => ⟨((77561542338445/140737488355328), (75904834969291/140737488355328)), (23395/281474976710656), by norm_num⟩
  | 6 => ⟨((14452375478589/1125899906842624), (669308073061455/1125899906842624)), (25511/140737488355328), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/17179869184), (-2541535427/536870912)), (1/8589934592), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-55294967/67108864), (-64451813537/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((339474965156611/2251799813685248), (-927682399920397/2251799813685248)), (536611/2251799813685248), by norm_num⟩
  | 1 => ⟨((-22763145045/137438953472), (15551197579/34359738368)), (19/68719476736), by norm_num⟩
  | 2 => ⟨((25007870875/274877906944), (-68338947055/274877906944)), (11/68719476736), by norm_num⟩
  | 3 => ⟨((-36631939009/1099511627776), (25026002343/274877906944)), (67/1099511627776), by norm_num⟩
  | 4 => ⟨((20122149177/2199023255552), (-54987747421/2199023255552)), (39/2199023255552), by norm_num⟩
  | 5 => ⟨((-552661009/274877906944), (96656344069/17592186044416)), (9/2199023255552), by norm_num⟩
  | 6 => ⟨((25905500841/70368744177664), (-8848987281/8796093022208)), (55/70368744177664), by norm_num⟩
  | 7 => ⟨((-32525830363/562949953421312), (22220814101/140737488355328)), (9/70368744177664), by norm_num⟩
  | 8 => ⟨((4466659617/562949953421312), (-48824118871/2251799813685248)), (41/2251799813685248), by norm_num⟩
  | 9 => ⟨((-34895126361/36028797018963968), (95357825733/36028797018963968)), (83/36028797018963968), by norm_num⟩
  | 10 => ⟨((7667242927/72057594037927936), (-83809023337/288230376151711744)), (75/288230376151711744), by norm_num⟩
  | 11 => ⟨((-3063028109/288230376151711744), (66962634865/2305843009213693952)), (31/1152921504606846976), by norm_num⟩
  | 12 => ⟨((8973547523/9223372036854775808), (-49043982363/18446744073709551616)), (47/18446744073709551616), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (-1589177496709/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222587145732667/79228162514264337593543950336), (-942295410697/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891910954987533/39614081257132168796771975168), (-2120005664117/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472955296649451/618970019642690137449562112), (-1126158157385/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886743487031237/77371252455336267181195264), (-2252102901279/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387926425823047/2417851639229258349412352), (-2111119725923/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260671436052945/604462909807314587353088), (-1847003024941/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890850597723077/75557863725914323419136), (-750238701407/18889465931478580854784)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((324958140685501/1180591620717411303424), (-2250344151751/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624599831652785/590295810358705651712), (-193351176311/36893488147419103232)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827412301877375/73786976294838206464), (-966529251539/18446744073709551616)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1827084076004965/9223372036854775808), (-4348135266831/9223372036854775808)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99895574304839/72057594037927936), (-2173288730333/576460752303423488)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198377359886913/144115188075855872), (-59398483641/2251799813685248)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497324673139159/36028797018963968), (-356171893603/2251799813685248)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((1496353442580335/9007199254740992), (-7117306810127/9007199254740992)), (1377/9007199254740992), by norm_num⟩
  | 2 => ⟨((1121049839355129/2251799813685248), (-1777028140525/562949953421312)), (1379/2251799813685248), by norm_num⟩
  | 1 => ⟨((279653939216469/281474976710656), (-1329898932771/140737488355328)), (2075/1125899906842624), by norm_num⟩
  | 0 => ⟨((1111295633327759/1125899906842624), (-2648315386339/140737488355328)), (4175/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1111295633327759/1125899906842624), (-2648315386339/140737488355328)), (15926365378951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((548241059613673/562949953421312), (-10455854225147/281474976710656)), (525/70368744177664), by norm_num⟩
  | 2 => ⟨((1066279366654089/1125899906842624), (-40730644454077/562949953421312)), (8493/562949953421312), by norm_num⟩
  | 3 => ⟨((501961026594019/562949953421312), (-77147614113759/562949953421312)), (4329/140737488355328), by norm_num⟩
  | 4 => ⟨((437007084485465/562949953421312), (-275158353558579/1125899906842624)), (71253/1125899906842624), by norm_num⟩
  | 5 => ⟨((305617152930927/562949953421312), (-427200141432335/1125899906842624)), (36363/281474976710656), by norm_num⟩
  | 6 => ⟨((339474965156611/2251799813685248), (-927682399920397/2251799813685248)), (536611/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-64451813537/8589934592)), (1/4294967296), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-8931133415/8589934592), (-2541535427/268435456)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-795389399691763/2251799813685248), (68731449564661/4503599627370496)), (249807/1125899906842624), by norm_num⟩
  | 1 => ⟨((67300039043/137438953472), (-2907776519/137438953472)), (11/34359738368), by norm_num⟩
  | 2 => ⟨((-23324416157/68719476736), (251939637/17179869184)), (63/274877906944), by norm_num⟩
  | 3 => ⟨((86225350919/549755813888), (-3725466647/549755813888)), (61/549755813888), by norm_num⟩
  | 4 => ⟨((-29883429441/549755813888), (5164593405/2199023255552)), (87/2199023255552), by norm_num⟩
  | 5 => ⟨((8285445945/549755813888), (-1431929343/2199023255552)), (25/2199023255552), by norm_num⟩
  | 6 => ⟨((-30629511981/8796093022208), (5293534863/35184372088832)), (95/35184372088832), by norm_num⟩
  | 7 => ⟨((48527451135/70368744177664), (-2096685009/70368744177664)), (77/140737488355328), by norm_num⟩
  | 8 => ⟨((-16818332967/140737488355328), (2906622605/562949953421312)), (55/562949953421312), by norm_num⟩
  | 9 => ⟨((20724586805/1125899906842624), (-895429895/1125899906842624)), (35/2251799813685248), by norm_num⟩
  | 10 => ⟨((-45968604519/18014398509481984), (3972254125/36028797018963968)), (5/2251799813685248), by norm_num⟩
  | 11 => ⟨((92692388703/288230376151711744), (-4004882541/288230376151711744)), (83/288230376151711744), by norm_num⟩
  | 12 => ⟨((-85665957185/2305843009213693952), (3701297389/2305843009213693952)), (39/1152921504606846976), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414716005/10141204801825835211973625643008), (252251832591/633825300114114700748351602688)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222544200935195/79228162514264337593543950336), (2392294417899/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891523870779341/39614081257132168796771975168), (1345531430609/9903520314283042199192993792)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891409185771423/2475880078570760549798248448), (2858948679505/1237940039285380274899124224)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773074159108829/154742504910672534362390528), (1429302354815/38685626227668133590597632)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551317824560465/9671406556917033397649408), (5359152670703/9671406556917033397649408)), (51/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((630165588892187/302231454903657293676544), (4688527175337/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890296058037985/75557863725914323419136), (7617484728957/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299415241190183/4722366482869645213696), (5711912573295/4722366482869645213696)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624023713571667/590295810358705651712), (7851927206647/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((114168044074287/4611686018427387904), (306624324637/2305843009213693952)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((913132645514185/4611686018427387904), (11034443249041/9223372036854775808)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798752243108011/576460752303423488), (5514699227849/576460752303423488)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598824547746627/72057594037927936), (2411260607451/36028797018963968)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496218997005497/36028797018963968), (7228093338095/18014398509481984)), (1111/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494948152311467/9007199254740992), (4512572763427/2251799813685248)), (1393/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119609844702435/2251799813685248), (18020312666469/2251799813685248)), (1399/2251799813685248), by norm_num⟩
  | 1 => ⟨((279092328296671/281474976710656), (13477648400773/562949953421312)), (2115/1125899906842624), by norm_num⟩
  | 0 => ⟨((276614699311765/281474976710656), (26804278093069/562949953421312)), (4297/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276614699311765/281474976710656), (26804278093069/562949953421312)), (16391758445357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((542400432439049/562949953421312), (52682887918701/562949953421312)), (1107/140737488355328), by norm_num⟩
  | 2 => ⟨((517670781673397/562949953421312), (203039158387535/1125899906842624)), (4681/281474976710656), by norm_num⟩
  | 3 => ⟨((228862984775683/281474976710656), (729329373511/2199023255552)), (20595/562949953421312), by norm_num⟩
  | 4 => ⟨((310246169353789/562949953421312), (151809669938581/281474976710656)), (94305/1125899906842624), by norm_num⟩
  | 5 => ⟨((14452375478613/1125899906842624), (334654036530735/562949953421312)), (411339/2251799813685248), by norm_num⟩
  | 6 => ⟨((-795389399691763/2251799813685248), (68731449564661/4503599627370496)), (249807/1125899906842624), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/8589934592), (-2541535427/268435456)), (1/4294967296), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-5184362399/4294967296), (-94420200195/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-2435371211273/2251799813685248), (673440817895849/2251799813685248)), (836237/4503599627370496), by norm_num⟩
  | 1 => ⟨((119616051/68719476736), (-132307273451/274877906944)), (21/68719476736), by norm_num⟩
  | 2 => ⟨((-385029215/274877906944), (6654385687/17179869184)), (69/274877906944), by norm_num⟩
  | 3 => ⟨((413120411/549755813888), (-28559521623/137438953472)), (19/137438953472), by norm_num⟩
  | 4 => ⟨((-166222913/549755813888), (45964776861/549755813888)), (63/1099511627776), by norm_num⟩
  | 5 => ⟨((428040733/4398046511104), (-118363927227/4398046511104)), (83/4398046511104), by norm_num⟩
  | 6 => ⟨((-459269989/17592186044416), (63499797315/8796093022208)), (91/17592186044416), by norm_num⟩
  | 7 => ⟨((105595219/17592186044416), (-116798835693/70368744177664)), (43/35184372088832), by norm_num⟩
  | 8 => ⟨((-169948949/140737488355328), (93990237147/281474976710656)), (71/281474976710656), by norm_num⟩
  | 9 => ⟨((243130917/1125899906842624), (-134463512057/2251799813685248)), (13/281474976710656), by norm_num⟩
  | 10 => ⟨((-78260823/2251799813685248), (43282134829/4503599627370496)), (69/9007199254740992), by norm_num⟩
  | 11 => ⟨((366417267/72057594037927936), (-6332718975/4503599627370496)), (83/72057594037927936), by norm_num⟩
  | 12 => ⟨((-393150561/576460752303423488), (54357962705/288230376151711744)), (91/576460752303423488), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791201706336853/5070602400912917605986812821504), (64089006995/316912650057057350374175801344)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222513033421665/79228162514264337593543950336), (2430547237171/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891243932403123/39614081257132168796771975168), (683516788411/9903520314283042199192993792)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891112455685897/2475880078570760549798248448), (2904587973027/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886389110679383/77371252455336267181195264), (1452092409069/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551041224525611/9671406556917033397649408), (2722244949521/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630044997039065/302231454903657293676544), (2381536052237/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889905711399781/75557863725914323419136), (3869193145193/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299123860386681/4722366482869645213696), (725298092343/1180591620717411303424)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811812652501703/295147905179352825856), (62312470587/9223372036854775808)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826194052566865/73786976294838206464), (4983285833157/73786976294838206464)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1825713421003999/9223372036854775808), (2801921630043/4611686018427387904)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596958379112529/1152921504606846976), (700112786933/144115188075855872)), (419/576460752303423488), by norm_num⟩
  | 5 => ⟨((299294432115475/36028797018963968), (4897481835981/144115188075855872)), (367/72057594037927936), by norm_num⟩
  | 4 => ⟨((747762441654339/18014398509481984), (7339609692951/36028797018963968)), (1103/36028797018963968), by norm_num⟩
  | 3 => ⟨((747051556237405/4503599627370496), (9162944405325/9007199254740992)), (345/2251799813685248), by norm_num⟩
  | 2 => ⟨((279699658447957/562949953421312), (9145603147685/2251799813685248)), (173/281474976710656), by norm_num⟩
  | 1 => ⟨((1115236807966089/1125899906842624), (13675087733191/1125899906842624)), (2083/1125899906842624), by norm_num⟩
  | 0 => ⟨((552264730524775/562949953421312), (27177125049225/1125899906842624)), (4199/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((552264730524775/562949953421312), (27177125049225/1125899906842624)), (16017918113326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((541454318803355/562949953421312), (53322564645513/1125899906842624)), (8443/1125899906842624), by norm_num⟩
  | 2 => ⟨((32469799668501/35184372088832), (25643250116211/281474976710656)), (8521/562949953421312), by norm_num⟩
  | 3 => ⟨((474762264817365/562949953421312), (189318414896351/1125899906842624)), (135/4398046511104), by norm_num⟩
  | 4 => ⟨((768945236514885/1125899906842624), (638644617565555/2251799813685248)), (69915/1125899906842624), by norm_num⟩
  | 5 => ⟨((869189235914847/2251799813685248), (872338177698325/2251799813685248)), (135157/1125899906842624), by norm_num⟩
  | 6 => ⟨((-2435371211273/2251799813685248), (673440817895849/2251799813685248)), (836237/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/4294967296), (-94420200195/8589934592)), (1/4294967296), by norm_num⟩, -2, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-2885830621/2147483648), (-105116380369/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((1111664607708069/4503599627370496), (379795964279187/4503599627370496)), (375701/4503599627370496), by norm_num⟩
  | 1 => ⟨((-60785998153/137438953472), (-81122281/536870912)), (11/68719476736), by norm_num⟩
  | 2 => ⟨((27228471947/68719476736), (18605006739/137438953472)), (21/137438953472), by norm_num⟩
  | 3 => ⟨((-32524581629/137438953472), (-1388987375/17179869184)), (27/274877906944), by norm_num⟩
  | 4 => ⟨((14569056779/137438953472), (9954925127/274877906944)), (13/274877906944), by norm_num⟩
  | 5 => ⟨((-83533585413/2199023255552), (-28538930179/2199023255552)), (39/2199023255552), by norm_num⟩
  | 6 => ⟨((24945348777/2199023255552), (8522483065/2199023255552)), (3/549755813888), by norm_num⟩
  | 7 => ⟨((-102162434021/35184372088832), (-2181462819/2199023255552)), (51/35184372088832), by norm_num⟩
  | 8 => ⟨((45762627139/70368744177664), (15634626651/70368744177664)), (3/8796093022208), by norm_num⟩
  | 9 => ⟨((-18221249003/140737488355328), (-24900880311/562949953421312)), (5/70368744177664), by norm_num⟩
  | 10 => ⟨((13059238177/562949953421312), (4461638809/562949953421312)), (15/1125899906842624), by norm_num⟩
  | 11 => ⟨((-68069857933/18014398509481984), (-23255806791/18014398509481984)), (41/18014398509481984), by norm_num⟩
  | 12 => ⟨((40654937507/72057594037927936), (13889604011/72057594037927936)), (51/144115188075855872), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (107209291005/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444974052042083/158456325028528675187087900672), (254059292907/316912650057057350374175801344)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118188129409401/2475880078570760549798248448), (571565233685/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945432116391517/1237940039285380274899124224), (607204791907/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772530285579001/154742504910672534362390528), (303555567399/77371252455336267181195264)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550809089694705/9671406556917033397649408), (284533599125/4835703278458516698824704)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259887180944857/604462909807314587353088), (497834330405/604462909807314587353088)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889576711387781/75557863725914323419136), (808794332219/75557863725914323419136)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298877610038627/4722366482869645213696), (303216324613/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1623287522250725/590295810358705651712), (833579945095/590295810358705651712)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456443260128041/18446744073709551616), (1041577667091/73786976294838206464)), (741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114077590851813/576460752303423488), (146403611535/1152921504606846976)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798244249352567/576460752303423488), (585273397933/576460752303423488)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196768928174203/144115188075855872), (511730806823/72057594037927936)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((93432272880953/2251799813685248), (1533660068355/36028797018963968)), (1095/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493350646034731/9007199254740992), (957198210831/4503599627370496)), (1369/9007199254740992), by norm_num⟩
  | 2 => ⟨((2236116812782291/4503599627370496), (955192162113/1125899906842624)), (2739/4503599627370496), by norm_num⟩
  | 1 => ⟨((2228313911706211/2251799813685248), (1427783428451/562949953421312)), (4111/2251799813685248), by norm_num⟩
  | 0 => ⟨((2204982124695531/2251799813685248), (11342437287841/2251799813685248)), (2059/562949953421312), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2204982124695531/2251799813685248), (11342437287841/2251799813685248)), (7854463817405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2159080700600309/2251799813685248), (11106614059639/1125899906842624)), (8107/1125899906842624), by norm_num⟩
  | 2 => ⟨((129372513929561/140737488355328), (42597172127725/2251799813685248)), (15707/1125899906842624), by norm_num⟩
  | 3 => ⟨((950999458116511/1125899906842624), (78314645356471/2251799813685248)), (921/35184372088832), by norm_num⟩
  | 4 => ⟨((1603813390393629/2251799813685248), (132298057480879/2251799813685248)), (25919/562949953421312), by norm_num⟩
  | 5 => ⟨((567260597426665/1125899906842624), (188454937087545/2251799813685248)), (159867/2251799813685248), by norm_num⟩
  | 6 => ⟨((1111664607708069/4503599627370496), (379795964279187/4503599627370496)), (375701/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-105116380369/8589934592)), (1/4294967296), by norm_num⟩, -2, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-12536430677/8589934592), (-57079935925/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((392139313741539/2251799813685248), (-346429723754415/2251799813685248)), (110913/1125899906842624), by norm_num⟩
  | 1 => ⟨((-23286983351/68719476736), (41145087609/137438953472)), (7/34359738368), by norm_num⟩
  | 2 => ⟨((45314377243/137438953472), (-40032321781/137438953472)), (29/137438953472), by norm_num⟩
  | 3 => ⟨((-58785137717/274877906944), (6491608437/34359738368)), (39/274877906944), by norm_num⟩
  | 4 => ⟨((223419133/2147483648), (-50528346965/549755813888)), (5/68719476736), by norm_num⟩
  | 5 => ⟨((-11129691095/274877906944), (19664724635/549755813888)), (33/1099511627776), by norm_num⟩
  | 6 => ⟨((57753010287/4398046511104), (-51021049661/4398046511104)), (45/4398046511104), by norm_num⟩
  | 7 => ⟨((-64218382203/17592186044416), (56732787629/17592186044416)), (13/4398046511104), by norm_num⟩
  | 8 => ⟨((31240800421/35184372088832), (-3449903351/4398046511104)), (53/70368744177664), by norm_num⟩
  | 9 => ⟨((-54037147203/281474976710656), (47738324935/281474976710656)), (3/17592186044416), by norm_num⟩
  | 10 => ⟨((42060573267/1125899906842624), (-9289449099/281474976710656)), (39/1125899906842624), by norm_num⟩
  | 11 => ⟨((-29762216871/4503599627370496), (26292993863/4503599627370496)), (57/9007199254740992), by norm_num⟩
  | 12 => ⟨((38609733245/36028797018963968), (-34109202405/36028797018963968)), (19/18014398509481984), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693181983/10141204801825835211973625643008), (-942553646807/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779717256136417/633825300114114700748351602688), (-1116595749469/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890808743729209/39614081257132168796771975168), (-1256007572131/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945325157305739/1237940039285380274899124224), (-1334309292327/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772316357946347/154742504910672534362390528), (-1334085744055/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550608522500079/9671406556917033397649408), (-312616978433/2417851639229258349412352)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629855837312815/302231454903657293676544), (-1093922008003/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889291494856205/75557863725914323419136), (-1777178223481/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1298663681254485/4722366482869645213696), (-1332494374431/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1622993343606149/590295810358705651712), (-915773690807/295147905179352825856)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456351319365445/18446744073709551616), (-1144243016935/36893488147419103232)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824827665718739/9223372036854775808), (-2573243642525/9223372036854775808)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798037321475929/576460752303423488), (-2571615640105/1152921504606846976)), (835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598203364208609/72057594037927936), (-2248333459777/144115188075855872)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1494372915389051/36028797018963968), (-1684421465191/18014398509481984)), (549/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492671070243529/9007199254740992), (-4204660633777/9007199254740992)), (343/2251799813685248), by norm_num⟩
  | 2 => ⟨((1117378440909167/2251799813685248), (-4195085424129/2251799813685248)), (2747/4503599627370496), by norm_num⟩
  | 1 => ⟨((2226272094181589/2251799813685248), (-6268740214437/1125899906842624)), (129/70368744177664), by norm_num⟩
  | 0 => ⟨((2200890968958671/2251799813685248), (-24884457638475/2251799813685248)), (8287/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2200890968958671/2251799813685248), (-24884457638475/2251799813685248)), (31612404830168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1075429039379267/1125899906842624), (-24321868112389/1125899906842624)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((2053390462946923/2251799813685248), (-92926353758627/2251799813685248)), (4001/281474976710656), by norm_num⟩
  | 3 => ⟨((467157100347671/562949953421312), (-84738477818823/1125899906842624)), (30509/1125899906842624), by norm_num⟩
  | 4 => ⟨((768951494476799/1125899906842624), (-281276737622113/2251799813685248)), (13807/281474976710656), by norm_num⟩
  | 5 => ⟨((3965628173593/8796093022208), (-384204966074865/2251799813685248)), (178471/2251799813685248), by norm_num⟩
  | 6 => ⟨((392139313741539/2251799813685248), (-346429723754415/2251799813685248)), (110913/1125899906842624), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12536430677/8589934592), (-57079935925/4294967296)), (1/4294967296), by norm_num⟩, -2, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-13396700123/8589934592), (-121993700497/8589934592)), (3/8589934592), by norm_num⟩
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
  | 0 => ⟨((-122556270374387/9007199254740992), (-1889560081906683/9007199254740992)), (901775/4503599627370496), by norm_num⟩
  | 1 => ⟨((7777362055/274877906944), (119910575251/274877906944)), (117/274877906944), by norm_num⟩
  | 2 => ⟨((-8086284871/274877906944), (-31168378933/68719476736)), (31/68719476736), by norm_num⟩
  | 3 => ⟨((700623195/34359738368), (86417095921/274877906944)), (89/274877906944), by norm_num⟩
  | 4 => ⟨((-5827619907/549755813888), (-89849649585/549755813888)), (95/549755813888), by norm_num⟩
  | 5 => ⟨((2423638985/549755813888), (74734837541/1099511627776)), (81/1099511627776), by norm_num⟩
  | 6 => ⟨((-6719754117/4398046511104), (-103604483863/4398046511104)), (115/4398046511104), by norm_num⟩
  | 7 => ⟨((7984763349/17592186044416), (123108267229/17592186044416)), (139/17592186044416), by norm_num⟩
  | 8 => ⟨((-518870269/4398046511104), (-127998222501/70368744177664)), (147/70368744177664), by norm_num⟩
  | 9 => ⟨((7672607233/281474976710656), (59147738029/140737488355328)), (139/281474976710656), by norm_num⟩
  | 10 => ⟨((-6381895285/1125899906842624), (-24598852711/281474976710656)), (59/562949953421312), by norm_num⟩
  | 11 => ⟨((1206434379/1125899906842624), (37201364513/2251799813685248)), (23/1125899906842624), by norm_num⟩
  | 12 => ⟨((-6689892707/36028797018963968), (-103144083701/36028797018963968)), (65/18014398509481984), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521241/10141204801825835211973625643008), (-2130506401853/10141204801825835211973625643008)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((889779994481671/316912650057057350374175801344), (-2523486708377/633825300114114700748351602688)), (271/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945315841496355/19807040628566084398385987584), (-1419263167407/19807040628566084398385987584)), (611/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890462014448885/2475880078570760549798248448), (-3015453754321/2475880078570760549798248448)), (649/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772127863132435/154742504910672534362390528), (-1507456644421/77371252455336267181195264)), (649/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550431601904233/9671406556917033397649408), (-2825907050953/9671406556917033397649408)), (19/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((314889165629831/151115727451828646838272), (-2472094610339/604462909807314587353088)), (133/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889039213097679/75557863725914323419136), (-2008038794585/37778931862957161709568)), (865/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298474131496403/4722366482869645213696), (-1505558383395/2361183241434822606848)), (649/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622732163213997/590295810358705651712), (-4138756129463/590295810358705651712)), (893/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456269494653619/18446744073709551616), (-5171151708631/73786976294838206464)), (279/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456114580947019/2305843009213693952), (-2907196642915/4611686018427387904)), (157/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595703889693179/1152921504606846976), (-5810454470657/1152921504606846976)), (1257/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196080734431055/144115188075855872), (-2539859394113/72057594037927936)), (1101/144115188075855872), by norm_num⟩
  | 4 => ⟨((746940380890219/18014398509481984), (-7610726169539/36028797018963968)), (1653/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492050359675741/9007199254740992), (-9497929593887/9007199254740992)), (1035/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116749484541539/2251799813685248), (-2368684557605/562949953421312)), (2075/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112172109926143/1125899906842624), (-442319353315/35184372088832)), (1563/562949953421312), by norm_num⟩
  | 0 => ⟨((274609067277311/281474976710656), (-28077428838001/1125899906842624)), (6303/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((274609067277311/281474976710656), (-28077428838001/1125899906842624)), (24044041160201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((267735588207359/281474976710656), (-13696273528205/281474976710656)), (25227/2251799813685248), by norm_num⟩
  | 2 => ⟨((15875025135377/17592186044416), (-208443671529201/2251799813685248)), (50447/2251799813685248), by norm_num⟩
  | 3 => ⟨((113397855301173/140737488355328), (-376195262656021/2251799813685248)), (50193/1125899906842624), by norm_num⟩
  | 4 => ⟨((1399058630104053/2251799813685248), (-606231309911525/2251799813685248)), (195313/2251799813685248), by norm_num⟩
  | 5 => ⟨((706034630471735/2251799813685248), (-94163915106527/281474976710656)), (43483/281474976710656), by norm_num⟩
  | 6 => ⟨((-122556270374387/9007199254740992), (-1889560081906683/9007199254740992)), (901775/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13396700123/8589934592), (-121993700497/8589934592)), (3/8589934592), by norm_num⟩, -2, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile015Terms0
