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
namespace Reinmann.XiRectangle.Tile014Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4089/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4089/640))
  have he : value ((3/4), (4089/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-8931133415/17179869184), (-76082092783/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-374943866431153/2251799813685248), (1285358225676577/2251799813685248)), (220405/1125899906842624), by norm_num⟩
  | 1 => ⟨((495703285/4294967296), (-54378810433/137438953472)), (5/34359738368), by norm_num⟩
  | 2 => ⟨((-21990101401/549755813888), (75385038267/549755813888)), (15/274877906944), by norm_num⟩
  | 3 => ⟨((2540396131/274877906944), (-69670568975/2199023255552)), (15/1099511627776), by norm_num⟩
  | 4 => ⟨((-28173894651/17592186044416), (48291958453/8796093022208)), (11/4398046511104), by norm_num⟩
  | 5 => ⟨((7811462257/35184372088832), (-53557495753/70368744177664)), (13/35184372088832), by norm_num⟩
  | 6 => ⟨((-28877296211/1125899906842624), (98995272477/1125899906842624)), (51/1125899906842624), by norm_num⟩
  | 7 => ⟨((2859459493/1125899906842624), (-78420907435/9007199254740992)), (43/9007199254740992), by norm_num⟩
  | 8 => ⟨((-3964052571/18014398509481984), (54357230885/72057594037927936)), (31/72057594037927936), by norm_num⟩
  | 9 => ⟨((4884749979/288230376151711744), (-66982331255/1152921504606846976)), (5/144115188075855872), by norm_num⟩
  | 10 => ⟨((-5417361081/4611686018427387904), (74285782491/18446744073709551616)), (47/18446744073709551616), by norm_num⟩
  | 11 => ⟨((21847438891/295147905179352825856), (-9361996489/36893488147419103232)), (25/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-20191320893/4722366482869645213696), (8652321961/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455347/5070602400912917605986812821504), (603963918771/2535301200456458802993406410752)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781164559554935/633825300114114700748351602688), (2866375669509/633825300114114700748351602688)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473109146970615/9903520314283042199192993792), (806128315601/9903520314283042199192993792)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946189724541651/1237940039285380274899124224), (428232818069/309485009821345068724781056)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774044986283785/154742504910672534362390528), (3425656836993/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((194028571733565/1208925819614629174706176), (3211334664551/9671406556917033397649408)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261128681953695/604462909807314587353088), (1404849574275/302231454903657293676544)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891593123895119/75557863725914323419136), (4565350952497/75557863725914323419136)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300389021315197/4722366482869645213696), (3423654187619/4722366482869645213696)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812682126855225/295147905179352825856), (2353470419803/295147905179352825856)), (149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914183383460947/36893488147419103232), (1470700027471/18446744073709551616)), (373/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914078194259443/4611686018427387904), (6616944996863/9223372036854775808)), (105/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599399676036881/1152921504606846976), (3307718762283/576460752303423488)), (105/288230376151711744), by norm_num⟩
  | 5 => ⟨((599655991638841/72057594037927936), (2893405233093/72057594037927936)), (23/9007199254740992), by norm_num⟩
  | 4 => ⟨((1498722504105937/36028797018963968), (2169204328481/9007199254740992)), (69/4503599627370496), by norm_num⟩
  | 3 => ⟨((1498093552751703/9007199254740992), (10840066267003/9007199254740992)), (173/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122779189085659/2251799813685248), (10831116829039/2251799813685248)), (347/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121182906231721/1125899906842624), (16224244459051/1125899906842624)), (1045/1125899906842624), by norm_num⟩
  | 0 => ⟨((1116322587133043/1125899906842624), (32358423622231/1125899906842624)), (2109/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1116322587133043/1125899906842624), (32358423622231/1125899906842624)), (8045200828170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((552948376404003/562949953421312), (32083170940847/562949953421312)), (4305/1125899906842624), by norm_num⟩
  | 2 => ⟨((135324008492345/140737488355328), (126052677853987/1125899906842624)), (8949/1125899906842624), by norm_num⟩
  | 3 => ⟨((256709388850531/281474976710656), (121204050518001/562949953421312)), (19215/1125899906842624), by norm_num⟩
  | 4 => ⟨((884300346492077/1125899906842624), (442159627804769/1125899906842624)), (43323/1125899906842624), by norm_num⟩
  | 5 => ⟨((260450313025709/562949953421312), (173639730182169/281474976710656)), (51041/562949953421312), by norm_num⟩
  | 6 => ⟨((-374943866431153/2251799813685248), (1285358225676577/2251799813685248)), (220405/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/17179869184), (-76082092783/17179869184)), (1/8589934592), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-55294967/67108864), (-120587264037/17179869184)), (3/17179869184), by norm_num⟩
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
  | 0 => ⟨((732205914321481/2251799813685248), (-331554062757035/1125899906842624)), (313337/2251799813685248), by norm_num⟩
  | 1 => ⟨((-12274328847/34359738368), (44464034143/137438953472)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((26969457013/137438953472), (-48848734313/274877906944)), (29/274877906944), by norm_num⟩
  | 3 => ⟨((-9876325631/137438953472), (35777213201/549755813888)), (23/549755813888), by norm_num⟩
  | 4 => ⟨((10850252705/549755813888), (-39305286077/2199023255552)), (27/2199023255552), by norm_num⟩
  | 5 => ⟨((-19072353531/4398046511104), (34545016235/8796093022208)), (25/8796093022208), by norm_num⟩
  | 6 => ⟨((55874991901/70368744177664), (-50602105797/70368744177664)), (39/70368744177664), by norm_num⟩
  | 7 => ⟨((-70154231693/562949953421312), (63533823155/562949953421312)), (13/140737488355328), by norm_num⟩
  | 8 => ⟨((4817018815/281474976710656), (-4362439929/281474976710656)), (15/1125899906842624), by norm_num⟩
  | 9 => ⟨((-18816128231/9007199254740992), (34080925259/18014398509481984)), (31/18014398509481984), by norm_num⟩
  | 10 => ⟨((66149215039/288230376151711744), (-29953378639/144115188075855872)), (57/288230376151711744), by norm_num⟩
  | 11 => ⟨((-52852611293/2305843009213693952), (47864945251/2305843009213693952)), (3/144115188075855872), by norm_num⟩
  | 12 => ⟨((38709685503/18446744073709551616), (-35056678033/18446744073709551616)), (37/18446744073709551616), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (-119826800955/1267650600228229401496703205376)), (57/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222587296285037/79228162514264337593543950336), (-1136811915369/633825300114114700748351602688)), (17/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1891912382327649/39614081257132168796771975168), (-1278818353311/39614081257132168796771975168)), (305/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891822792176069/2475880078570760549798248448), (-679315087025/1237940039285380274899124224)), (81/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886744339886947/77371252455336267181195264), (-1358501567971/154742504910672534362390528)), (81/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551707408761201/9671406556917033397649408), (-636729294343/4835703278458516698824704)), (19/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((39396032333519/18889465931478580854784), (-1114139648069/604462909807314587353088)), (133/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890853394792465/75557863725914323419136), (-1810220801467/75557863725914323419136)), (27/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((324958708719525/1180591620717411303424), (-1357441520575/4722366482869645213696)), (81/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1624603239012165/590295810358705651712), (-466529504181/147573952589676412928)), (223/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913708492811989/36893488147419103232), (-291512688647/9223372036854775808)), (557/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827089928629745/9223372036854775808), (-1311431796581/4611686018427387904)), (627/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598335770250457/1152921504606846976), (-327740697439/144115188075855872)), (627/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198383937723479/144115188075855872), (-2293129949673/144115188075855872)), (549/144115188075855872), by norm_num⟩
  | 4 => ⟨((23395877756225/562949953421312), (-429698236499/4503599627370496)), (823/36028797018963968), by norm_num⟩
  | 3 => ⟨((748185340782729/4503599627370496), (-4293293430417/9007199254740992)), (515/4503599627370496), by norm_num⟩
  | 2 => ⟨((1121071360267963/2251799813685248), (-1071940943119/562949953421312)), (2061/4503599627370496), by norm_num⟩
  | 1 => ⟨((559329357643881/562949953421312), (-401114663387/70368744177664)), (387/281474976710656), by norm_num⟩
  | 0 => ⟨((2222848183876807/2251799813685248), (-25561007250357/2251799813685248)), (777/281474976710656), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2222848183876807/2251799813685248), (-25561007250357/2251799813685248)), (2964020849132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1096989317933065/1125899906842624), (-50464733320615/2251799813685248)), (6207/1125899906842624), by norm_num⟩
  | 2 => ⟨((2136511219198615/2251799813685248), (-24584455975443/562949953421312)), (6187/562949953421312), by norm_num⟩
  | 3 => ⟨((2022830730542243/2251799813685248), (-46651541305057/562949953421312)), (12281/562949953421312), by norm_num⟩
  | 4 => ⟨((1801679829117771/2251799813685248), (-167631546650835/1125899906842624)), (96401/2251799813685248), by norm_num⟩
  | 5 => ⟨((1391619648369707/2251799813685248), (-536492408408805/2251799813685248)), (182969/2251799813685248), by norm_num⟩
  | 6 => ⟨((732205914321481/2251799813685248), (-331554062757035/1125899906842624)), (313337/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-120587264037/17179869184)), (3/17179869184), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-8931133415/8589934592), (-76082092783/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-1342537517015193/4503599627370496), (-428046205488919/2251799813685248)), (276589/1125899906842624), by norm_num⟩
  | 1 => ⟨((56797857343/137438953472), (36218142149/137438953472)), (49/137438953472), by norm_num⟩
  | 2 => ⟨((-39369274679/137438953472), (-50209006231/274877906944)), (35/137438953472), by norm_num⟩
  | 3 => ⟨((36384935659/274877906944), (23201487405/274877906944)), (67/549755813888), by norm_num⟩
  | 4 => ⟨((-25220115567/549755813888), (-32164091159/1099511627776)), (3/68719476736), by norm_num⟩
  | 5 => ⟨((13985001599/1099511627776), (35671118563/4398046511104)), (55/4398046511104), by norm_num⟩
  | 6 => ⟨((-25849771809/8796093022208), (-32967113679/17592186044416)), (53/17592186044416), by norm_num⟩
  | 7 => ⟨((40954734737/70368744177664), (52230998623/140737488355328)), (87/140737488355328), by norm_num⟩
  | 8 => ⟨((-56775317827/562949953421312), (-36203769433/562949953421312)), (31/281474976710656), by norm_num⟩
  | 9 => ⟨((34981023535/2251799813685248), (22306258407/2251799813685248)), (79/4503599627370496), by norm_num⟩
  | 10 => ⟨((-19397598269/9007199254740992), (-12369216099/9007199254740992)), (45/18014398509481984), by norm_num⟩
  | 11 => ⟨((78227726835/288230376151711744), (24941635679/144115188075855872)), (93/288230376151711744), by norm_num⟩
  | 12 => ⟨((-72297771063/2305843009213693952), (-46101931865/2305843009213693952)), (11/288230376151711744), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414716005/10141204801825835211973625643008), (-1676419516859/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780357391948345/633825300114114700748351602688), (-3974687726789/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891528353305947/39614081257132168796771975168), (-1117771834811/9903520314283042199192993792)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891414227858223/2475880078570760549798248448), (-4750023690467/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886539757733173/77371252455336267181195264), (-4749453605001/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551323179950295/9671406556917033397649408), (-2226003470147/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260336197433851/604462909807314587353088), (-3894900147495/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890304840366875/75557863725914323419136), (-6328076394467/75557863725914323419136)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649711187451277/2361183241434822606848), (-4745062758725/4722366482869645213696)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101502150672591/36893488147419103232), (-6522844730271/590295810358705651712)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((28542240755175/1152921504606846976), (-2037782574827/18446744073709551616)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826283661711615/9223372036854775808), (-4583342560309/4611686018427387904)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199690642736211/144115188075855872), (-143164260479/18014398509481984)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197669736973585/144115188075855872), (-4006251009695/72057594037927936)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((46757971488371/1125899906842624), (-12009353510209/36028797018963968)), (277/9007199254740992), by norm_num⟩
  | 3 => ⟨((747501112112951/4503599627370496), (-7497614209053/4503599627370496)), (347/2251799813685248), by norm_num⟩
  | 2 => ⟨((559838661188315/1125899906842624), (-7485252360643/1125899906842624)), (697/1125899906842624), by norm_num⟩
  | 1 => ⟨((1116503931140789/1125899906842624), (-11196924352689/562949953421312)), (263/140737488355328), by norm_num⟩
  | 0 => ⟨((1106860959007559/1125899906842624), (-44539473802899/1125899906842624)), (4263/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1106860959007559/1125899906842624), (-44539473802899/1125899906842624)), (16262058738326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1086382022429161/1125899906842624), (-87572624151677/1125899906842624)), (545/70368744177664), by norm_num⟩
  | 2 => ⟨((1041439764787511/1125899906842624), (-168997837120571/1125899906842624)), (9093/562949953421312), by norm_num⟩
  | 3 => ⟨((58621802674865/70368744177664), (-312640700422487/1125899906842624)), (611/17592186044416), by norm_num⟩
  | 4 => ⟨((694558920728689/1125899906842624), (-260450313025709/562949953421312)), (86871/1125899906842624), by norm_num⟩
  | 5 => ⟨((374943866431185/2251799813685248), (-1285358225676601/2251799813685248)), (187563/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1342537517015193/4503599627370496), (-428046205488919/2251799813685248)), (276589/1125899906842624), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/8589934592), (-76082092783/8589934592)), (1/4294967296), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-5184362399/4294967296), (-11041071797/1073741824)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-55048727152345/281474976710656), (1018990235735687/4503599627370496)), (942699/4503599627370496), by norm_num⟩
  | 1 => ⟨((21630251101/68719476736), (-50048874445/137438953472)), (49/137438953472), by norm_num⟩
  | 2 => ⟨((-17406273089/68719476736), (40275278003/137438953472)), (41/137438953472), by norm_num⟩
  | 3 => ⟨((18676210549/137438953472), (-43213706235/274877906944)), (23/137438953472), by norm_num⟩
  | 4 => ⟨((-60116402637/1099511627776), (271678817/4294967296)), (19/274877906944), by norm_num⟩
  | 5 => ⟨((38701447025/2199023255552), (-11193604815/549755813888)), (51/2199023255552), by norm_num⟩
  | 6 => ⟨((-41525050739/8796093022208), (3002568661/549755813888)), (57/8796093022208), by norm_num⟩
  | 7 => ⟨((38189709129/35184372088832), (-44182380231/35184372088832)), (27/17592186044416), by norm_num⟩
  | 8 => ⟨((-61463965737/281474976710656), (35554398903/140737488355328)), (89/281474976710656), by norm_num⟩
  | 9 => ⟨((43965527425/1125899906842624), (-25432265577/562949953421312)), (65/1125899906842624), by norm_num⟩
  | 10 => ⟨((-56607829343/9007199254740992), (32745321935/4503599627370496)), (43/4503599627370496), by norm_num⟩
  | 11 => ⟨((33129740613/36028797018963968), (-38328409147/36028797018963968)), (13/9007199254740992), by norm_num⟩
  | 12 => ⟨((-35546840381/288230376151711744), (5140599567/36028797018963968)), (29/144115188075855872), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791201706336853/5070602400912917605986812821504), (743651613119/2535301200456458802993406410752)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890050393528309/316912650057057350374175801344), (881333076077/158456325028528675187087900672)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891239811834701/39614081257132168796771975168), (1982779072821/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891107820812171/2475880078570760549798248448), (4212884795317/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886386648859181/77371252455336267181195264), (2106149451583/77371252455336267181195264)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551036301912315/9671406556917033397649408), (3948407690367/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157510672527429/75557863725914323419136), (3454234174139/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472474409832379/18889465931478580854784), (5611963192537/75557863725914323419136)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299117303875561/4722366482869645213696), (4207950921775/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623615473817007/590295810358705651712), (2892136265783/295147905179352825856)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228272567562901/9223372036854775808), (7227850523977/73786976294838206464)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825696539650339/9223372036854775808), (8127907635159/9223372036854775808)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((399234849896721/288230376151711744), (8123626990749/1152921504606846976)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149644845491427/18014398509481984), (7103357361461/144115188075855872)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((747745864557827/18014398509481984), (5322701109159/18014398509481984)), (553/18014398509481984), by norm_num⟩
  | 3 => ⟨((747026724323171/4503599627370496), (3322472665811/2251799813685248)), (693/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118736672041303/2251799813685248), (13264591753745/2251799813685248)), (1391/2251799813685248), by norm_num⟩
  | 1 => ⟨((557556619240811/562949953421312), (19833620656997/1125899906842624)), (1049/562949953421312), by norm_num⟩
  | 0 => ⟨((552080261023437/562949953421312), (1231689327365/35184372088832)), (1061/281474976710656), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((552080261023437/562949953421312), (1231689327365/35184372088832)), (4047394872569949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1081461134370177/1125899906842624), (38653034002405/562949953421312)), (4311/562949953421312), by norm_num⟩
  | 2 => ⟨((64591773985149/70368744177664), (37127415807605/281474976710656)), (17749/1125899906842624), by norm_num⟩
  | 3 => ⟨((929036208109243/1125899906842624), (272635321664151/1125899906842624)), (37267/1125899906842624), by norm_num⟩
  | 4 => ⟨((700575826115011/1125899906842624), (449930022901957/1125899906842624)), (79551/1125899906842624), by norm_num⟩
  | 5 => ⟨((512247067213733/2251799813685248), (559925612521689/1125899906842624)), (325159/2251799813685248), by norm_num⟩
  | 6 => ⟨((-55048727152345/281474976710656), (1018990235735687/4503599627370496)), (942699/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/4294967296), (-11041071797/1073741824)), (1/4294967296), by norm_num⟩, -2, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-2885830621/2147483648), (-49167339205/4294967296)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((513185376033741/4503599627370496), (1056732674018635/4503599627370496)), (307649/4503599627370496), by norm_num⟩
  | 1 => ⟨((-28061058257/137438953472), (-14445577813/34359738368)), (19/137438953472), by norm_num⟩
  | 2 => ⟨((1571208339/8589934592), (25883000835/68719476736)), (19/137438953472), by norm_num⟩
  | 3 => ⟨((-30029092475/274877906944), (-7729351973/34359738368)), (3/34359738368), by norm_num⟩
  | 4 => ⟨((26902455397/549755813888), (27698279177/274877906944)), (23/549755813888), by norm_num⟩
  | 5 => ⟨((-19281091681/1099511627776), (-79405846395/2199023255552)), (35/2199023255552), by norm_num⟩
  | 6 => ⟨((23031385731/4398046511104), (47425392397/4398046511104)), (11/2199023255552), by norm_num⟩
  | 7 => ⟨((-23580973413/17592186044416), (-48557083377/17592186044416)), (3/2199023255552), by norm_num⟩
  | 8 => ⟨((21125716203/70368744177664), (87002613939/140737488355328)), (45/140737488355328), by norm_num⟩
  | 9 => ⟨((-33646401823/562949953421312), (-69283447721/562949953421312)), (37/562949953421312), by norm_num⟩
  | 10 => ⟨((24114503629/2251799813685248), (24827854703/1125899906842624)), (7/562949953421312), by norm_num⟩
  | 11 => ⟨((-15711778263/9007199254740992), (-16176561369/4503599627370496)), (19/9007199254740992), by norm_num⟩
  | 12 => ⟨((37535636641/144115188075855872), (19323004675/36028797018963968)), (3/9007199254740992), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (1457241267443/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779894754020251/633825300114114700748351602688), (863324630103/316912650057057350374175801344)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891008349474509/39614081257132168796771975168), (1942247160873/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890862296917307/2475880078570760549798248448), (2063354460311/2475880078570760549798248448)), (27/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886264114572471/77371252455336267181195264), (2063035967697/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550807033736709/9671406556917033397649408), (1933757874937/9671406556917033397649408)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314971313497483/151115727451828646838272), (1691699856105/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889573340227781/75557863725914323419136), (2748378110953/75557863725914323419136)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298874871918761/4722366482869645213696), (1030364412769/2361183241434822606848)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623283416728705/590295810358705651712), (2832600894113/590295810358705651712)), (149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825767398112189/73786976294838206464), (221212479779/4611686018427387904)), (93/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912617202333171/4611686018427387904), (3979967087305/9223372036854775808)), (419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49890017942823/36028797018963968), (1988823087769/576460752303423488)), (419/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149595126321253/18014398509481984), (3477830785677/144115188075855872)), (367/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494902525869095/36028797018963968), (2605765230567/18014398509481984)), (275/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493329916826011/9007199254740992), (1626323371137/2251799813685248)), (689/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118032549287123/2251799813685248), (12983259832735/4503599627370496)), (1379/4503599627370496), by norm_num⟩
  | 1 => ⟨((2228210809159883/2251799813685248), (19406682578263/2251799813685248)), (2073/2251799813685248), by norm_num⟩
  | 0 => ⟨((2204674442410153/2251799813685248), (38541199954441/2251799813685248)), (4169/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2204674442410153/2251799813685248), (38541199954441/2251799813685248)), (15903481490325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2157875643914493/2251799813685248), (75469229549597/2251799813685248)), (2077/562949953421312), by norm_num⟩
  | 2 => ⟨((1032669880716281/1125899906842624), (144642708752645/2251799813685248)), (16481/2251799813685248), by norm_num⟩
  | 3 => ⟨((1885028496388501/2251799813685248), (66332792056511/562949953421312)), (32351/2251799813685248), by norm_num⟩
  | 4 => ⟨((1546732432517793/2251799813685248), (222114243924551/1125899906842624)), (61789/2251799813685248), by norm_num⟩
  | 5 => ⟨((974794586554899/2251799813685248), (610269709970395/2251799813685248)), (6829/140737488355328), by norm_num⟩
  | 6 => ⟨((513185376033741/4503599627370496), (1056732674018635/4503599627370496)), (307649/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-49167339205/4294967296)), (1/8589934592), by norm_num⟩, -2, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-12536430677/8589934592), (-106794718827/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((1037135322578205/4503599627370496), (2181772758675/70368744177664)), (283431/4503599627370496), by norm_num⟩
  | 1 => ⟨((-30794863131/68719476736), (-8292058113/137438953472)), (9/68719476736), by norm_num⟩
  | 2 => ⟨((59924036705/137438953472), (16135600039/274877906944)), (37/274877906944), by norm_num⟩
  | 3 => ⟨((-38868930399/137438953472), (-5233071313/137438953472)), (13/137438953472), by norm_num⟩
  | 4 => ⟨((37817723073/274877906944), (10183086579/549755813888)), (27/549755813888), by norm_num⟩
  | 5 => ⟨((-117743825827/2199023255552), (-7926148609/1099511627776)), (11/549755813888), by norm_num⟩
  | 6 => ⟨((76372968555/4398046511104), (5141191007/2199023255552)), (15/2199023255552), by norm_num⟩
  | 7 => ⟨((-84922819785/17592186044416), (-11433480867/17592186044416)), (35/17592186044416), by norm_num⟩
  | 8 => ⟨((82626088453/70368744177664), (11124263229/70368744177664)), (35/70368744177664), by norm_num⟩
  | 9 => ⟨((-71459086265/281474976710656), (-4810403715/140737488355328)), (1/8796093022208), by norm_num⟩
  | 10 => ⟨((27810592241/562949953421312), (936061341/140737488355328)), (51/2251799813685248), by norm_num⟩
  | 11 => ⟨((-39357755413/4503599627370496), (-1324720919/1125899906842624)), (19/4503599627370496), by norm_num⟩
  | 12 => ⟨((12764442617/9007199254740992), (859262627/4503599627370496)), (51/72057594037927936), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693181983/10141204801825835211973625643008), (174327283229/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779717899388451/633825300114114700748351602688), (206516736877/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945404752420329/19807040628566084398385987584), (116150665665/19807040628566084398385987584)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945325585348735/1237940039285380274899124224), (123391707385/1237940039285380274899124224)), (431/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443079316833627/38685626227668133590597632), (246742081437/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550609431659709/9671406556917033397649408), (115638397229/4835703278458516698824704)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259712526720037/604462909807314587353088), (202323299263/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472323246384021/18889465931478580854784), (82173269971/18889465931478580854784)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649332445988525/2361183241434822606848), (30805979629/590295810358705651712)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((811497579447183/295147905179352825856), (338748863777/590295810358705651712)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456351943047699/18446744073709551616), (423260788101/73786976294838206464)), (741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824830782192671/9223372036854775808), (29745467815/576460752303423488)), (833/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596078146322953/1152921504606846976), (475626544571/1152921504606846976)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((299102557115839/36028797018963968), (415834924731/144115188075855872)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494379032995895/36028797018963968), (623076423679/36028797018963968)), (547/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492680231724119/9007199254740992), (194416008109/2251799813685248)), (1367/9007199254740992), by norm_num⟩
  | 2 => ⟨((558694933336851/1125899906842624), (1551789321415/4503599627370496)), (2735/4503599627370496), by norm_num⟩
  | 1 => ⟨((1113158820523931/1125899906842624), (1159428604523/1125899906842624)), (4103/2251799813685248), by norm_num⟩
  | 0 => ⟨((2201026830871373/2251799813685248), (4602527579233/2251799813685248)), (8211/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2201026830871373/2251799813685248), (4602527579233/2251799813685248)), (31322487837981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1075694628250981/1125899906842624), (8997502024959/2251799813685248)), (8043/1125899906842624), by norm_num⟩
  | 2 => ⟨((1027710089906847/1125899906842624), (8596292207775/1125899906842624)), (30867/2251799813685248), by norm_num⟩
  | 3 => ⟨((1876035562731847/2251799813685248), (7846608907263/562949953421312)), (28411/1125899906842624), by norm_num⟩
  | 4 => ⟨((1562538687013549/2251799813685248), (26148891686393/1125899906842624)), (96265/2251799813685248), by norm_num⟩
  | 5 => ⟨((4230629892015/8796093022208), (18144887762313/562949953421312)), (69035/1125899906842624), by norm_num⟩
  | 6 => ⟨((1037135322578205/4503599627370496), (2181772758675/70368744177664)), (283431/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12536430677/8589934592), (-106794718827/8589934592)), (1/4294967296), by norm_num⟩, -2, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-13396700123/8589934592), (-114123139175/8589934592)), (3/8589934592), by norm_num⟩
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
  | 0 => ⟨((178053308727361/1125899906842624), (-623792147798983/4503599627370496)), (601335/4503599627370496), by norm_num⟩
  | 1 => ⟨((-45196709815/137438953472), (39585550095/137438953472)), (5/17179869184), by norm_num⟩
  | 2 => ⟨((2936997373/8589934592), (-41157918659/137438953472)), (11/34359738368), by norm_num⟩
  | 3 => ⟨((-65144686349/274877906944), (57056990553/274877906944)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((67732283507/549755813888), (-7415417275/68719476736)), (69/549755813888), by norm_num⟩
  | 5 => ⟨((-56338129615/1099511627776), (24671882769/549755813888)), (15/274877906944), by norm_num⟩
  | 6 => ⟨((39050615701/2199023255552), (-34202491961/2199023255552)), (43/2199023255552), by norm_num⟩
  | 7 => ⟨((-5800248037/1099511627776), (40641190065/8796093022208)), (27/4398046511104), by norm_num⟩
  | 8 => ⟨((48245106881/35184372088832), (-21127744731/17592186044416)), (29/17592186044416), by norm_num⟩
  | 9 => ⟨((-22293973207/70368744177664), (1220386391/4398046511104)), (55/140737488355328), by norm_num⟩
  | 10 => ⟨((37087211213/562949953421312), (-32482843627/562949953421312)), (47/562949953421312), by norm_num⟩
  | 11 => ⟨((-56087772845/4503599627370496), (49124490495/4503599627370496)), (73/4503599627370496), by norm_num⟩
  | 12 => ⟨((9719270403/4503599627370496), (-34050502083/18014398509481984)), (53/18014398509481984), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521241/10141204801825835211973625643008), (-468491679355/5070602400912917605986812821504)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779562733689461/633825300114114700748351602688), (-1109813633801/633825300114114700748351602688)), (271/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890634929814089/39614081257132168796771975168), (-1248368014463/39614081257132168796771975168)), (609/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945232833184487/1237940039285380274899124224), (-663089967055/1237940039285380274899124224)), (81/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886065871185229/77371252455336267181195264), (-662971262405/77371252455336267181195264)), (647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387608870024891/2417851639229258349412352), (-1242818925575/9671406556917033397649408)), (607/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259560297219863/604462909807314587353088), (-1087214431381/604462909807314587353088)), (133/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889045571609077/75557863725914323419136), (-220781355471/9444732965739290427392)), (863/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324619823927859/1180591620717411303424), (-662137367585/2361183241434822606848)), (81/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622739905905781/590295810358705651712), (-455051560051/147573952589676412928)), (891/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912544309459079/36893488147419103232), (-2274250957543/73786976294838206464)), (1113/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456117903831431/2305843009213693952), (-2557148630369/9223372036854775808)), (313/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797859415261187/576460752303423488), (-2555420076515/1152921504606846976)), (1253/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598047830041233/72057594037927936), (-2234049410387/144115188075855872)), (1097/144115188075855872), by norm_num⟩
  | 4 => ⟨((746953423774685/18014398509481984), (-3347191466005/36028797018963968)), (823/18014398509481984), by norm_num⟩
  | 3 => ⟨((373022355039865/2251799813685248), (-2088601465589/4503599627370496)), (1029/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116798191012051/2251799813685248), (-2083519890571/1125899906842624)), (515/562949953421312), by norm_num⟩
  | 1 => ⟨((2224538332230909/2251799813685248), (-12450418587045/2251799813685248)), (6191/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197451316938213/2251799813685248), (-24698722753827/2251799813685248)), (12429/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2197451316938213/2251799813685248), (-24698722753827/2251799813685248)), (47412880904387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((67004488949027/70368744177664), (-48205209461551/2251799813685248)), (6133/562949953421312), by norm_num⟩
  | 2 => ⟨((2040602457695655/2251799813685248), (-91801138769711/2251799813685248)), (23885/1125899906842624), by norm_num⟩
  | 3 => ⟨((1845470861138901/2251799813685248), (-166382134197047/2251799813685248)), (90475/2251799813685248), by norm_num⟩
  | 4 => ⟨((1500168738003535/2251799813685248), (-272718186233647/2251799813685248)), (161669/2251799813685248), by norm_num⟩
  | 5 => ⟨((120799538893021/281474976710656), (-181687241817105/1125899906842624)), (254571/2251799813685248), by norm_num⟩
  | 6 => ⟨((178053308727361/1125899906842624), (-623792147798983/4503599627370496)), (601335/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13396700123/8589934592), (-114123139175/8589934592)), (3/8589934592), by norm_num⟩, -2, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile014Terms0
