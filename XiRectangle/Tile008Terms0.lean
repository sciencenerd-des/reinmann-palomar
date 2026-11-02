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
namespace Reinmann.XiRectangle.Tile008Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨8,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2397/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2397/640))
  have he : value ((3/4), (2397/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-17862266831/34359738368), (-89199694987/34359738368)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1144579134418739/2251799813685248), (-694742597109051/2251799813685248)), (14409/140737488355328), by norm_num⟩
  | 1 => ⟨((48422961423/137438953472), (29392021021/137438953472)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((-67128478369/549755813888), (-40745993003/549755813888)), (19/549755813888), by norm_num⟩
  | 3 => ⟨((15509971839/549755813888), (37657293559/2199023255552)), (5/549755813888), by norm_num⟩
  | 4 => ⟨((-43002773003/8796093022208), (-13051023429/4398046511104)), (15/8796093022208), by norm_num⟩
  | 5 => ⟨((47691601381/70368744177664), (14474048149/35184372088832)), (9/35184372088832), by norm_num⟩
  | 6 => ⟨((-44076398711/562949953421312), (-26753721775/562949953421312)), (19/562949953421312), by norm_num⟩
  | 7 => ⟨((69831843419/9007199254740992), (1324590487/281474976710656)), (33/9007199254740992), by norm_num⟩
  | 8 => ⟨((-48403745379/72057594037927936), (-29380357167/72057594037927936)), (25/72057594037927936), by norm_num⟩
  | 9 => ⟨((14911519839/288230376151711744), (36204287527/1152921504606846976)), (33/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-66149618779/18446744073709551616), (-20075919859/9223372036854775808)), (39/18446744073709551616), by norm_num⟩
  | 11 => ⟨((66692977093/295147905179352825856), (20240825087/147573952589676412928)), (41/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-61637398713/4722366482869645213696), (-18706494455/2361183241434822606848)), (5/590295810358705651712), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24739040482979/158456325028528675187087900672), (-1690824311201/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222645045233315/79228162514264337593543950336), (-4012274174345/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892431609520669/39614081257132168796771975168), (-4513574728251/39614081257132168796771975168)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((473093462215031/618970019642690137449562112), (-2397707983119/1237940039285380274899124224)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774039036525341/154742504910672534362390528), (-4795126446883/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552222624648953/9671406556917033397649408), (-4495123253179/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157640388141653/75557863725914323419136), (-491615607173/75557863725914323419136)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891583365605747/75557863725914323419136), (-6390424992203/75557863725914323419136)), (73/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300381093780635/4722366482869645213696), (-1198078164877/1180591620717411303424)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625352364292329/590295810358705651712), (-1647151682457/147573952589676412928)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914175211017925/36893488147419103232), (-4117261132985/36893488147419103232)), (47/18446744073709551616), by norm_num⟩
  | 7 => ⟨((228516995251509/1152921504606846976), (-9262135605525/9223372036854775808)), (211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399844175637687/288230376151711744), (-4630002407243/576460752303423488)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599644508860551/72057594037927936), (-8100102454591/144115188075855872)), (185/144115188075855872), by norm_num⟩
  | 4 => ⟨((749341166128207/18014398509481984), (-3036334657923/9007199254740992)), (277/36028797018963968), by norm_num⟩
  | 3 => ⟨((374508332702199/2251799813685248), (-7586610515789/4503599627370496)), (87/2251799813685248), by norm_num⟩
  | 2 => ⟨((1122703974547041/2251799813685248), (-947530680163/140737488355328)), (349/2251799813685248), by norm_num⟩
  | 1 => ⟨((280258166640883/281474976710656), (-11354365069207/562949953421312)), (527/1125899906842624), by norm_num⟩
  | 0 => ⟨((557936410166905/562949953421312), (-45288353490289/1125899906842624)), (1067/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557936410166905/562949953421312), (-45288353490289/1125899906842624)), (4070286277389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((34503542140015/35184372088832), (-11221255644119/140737488355328)), (2201/1125899906842624), by norm_num⟩
  | 2 => ⟨((537795419435667/562949953421312), (-11004120409005/70368744177664)), (4669/1125899906842624), by norm_num⟩
  | 3 => ⟨((999996922756199/1125899906842624), (-336397394612585/1125899906842624)), (5191/562949953421312), by norm_num⟩
  | 4 => ⟨((787663834973291/1125899906842624), (-597559973833107/1125899906842624)), (24647/1125899906842624), by norm_num⟩
  | 5 => ⟨((467779405606109/2251799813685248), (-836089207851253/1125899906842624)), (7581/140737488355328), by norm_num⟩
  | 6 => ⟨((-1144579134418739/2251799813685248), (-694742597109051/2251799813685248)), (14409/140737488355328), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/34359738368), (-89199694987/34359738368)), (1/17179869184), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-55294967/67108864), (-70689085815/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-555937433880259/2251799813685248), (816560748934731/2251799813685248)), (170677/1125899906842624), by norm_num⟩
  | 1 => ⟨((37277813513/137438953472), (-54753642165/137438953472)), (25/137438953472), by norm_num⟩
  | 2 => ⟨((-10238466005/68719476736), (15038256033/68719476736)), (15/137438953472), by norm_num⟩
  | 3 => ⟨((29994945521/549755813888), (-44056567675/549755813888)), (3/68719476736), by norm_num⟩
  | 4 => ⟨((-32952815747/2199023255552), (12100271661/549755813888)), (29/2199023255552), by norm_num⟩
  | 5 => ⟨((28961894661/8796093022208), (-21269611429/4398046511104)), (7/2199023255552), by norm_num⟩
  | 6 => ⟨((-42423857837/70368744177664), (62312150643/70368744177664)), (43/70368744177664), by norm_num⟩
  | 7 => ⟨((208068623/2199023255552), (-78236450777/562949953421312)), (57/562949953421312), by norm_num⟩
  | 8 => ⟨((-29259103503/2251799813685248), (42975763123/2251799813685248)), (33/2251799813685248), by norm_num⟩
  | 9 => ⟨((28572809479/18014398509481984), (-20983867325/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 10 => ⟨((-50224703385/288230376151711744), (36885015211/144115188075855872)), (63/288230376151711744), by norm_num⟩
  | 11 => ⟨((40129073697/2305843009213693952), (-14735393083/576460752303423488)), (53/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-29390862331/18446744073709551616), (10792322613/4611686018427387904)), (41/18446744073709551616), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (2824764126769/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780693077164873/633825300114114700748351602688), (3349861520779/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891906109530363/39614081257132168796771975168), (3768302911885/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891815736083613/2475880078570760549798248448), (1000870897891/618970019642690137449562112)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221685147953079/19342813113834066795298816), (2001551484439/77371252455336267181195264)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775849956839827/4835703278458516698824704), (469063069491/1208925819614629174706176)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630333004584079/302231454903657293676544), (3283036935059/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945420551214399/37778931862957161709568), (5334176328543/75557863725914323419136)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299824849460047/4722366482869645213696), (499996029361/590295810358705651712)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624588264608333/590295810358705651712), (2749438505123/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114212275116841/4611686018427387904), (6871976779791/73786976294838206464)), (373/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913532104006767/4611686018427387904), (7728746254065/9223372036854775808)), (105/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99894177939959/72057594037927936), (7725960475887/1152921504606846976)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599177515058503/72057594037927936), (3378539850709/72057594037927936)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((748642811601471/18014398509481984), (10129343845081/36028797018963968)), (277/18014398509481984), by norm_num⟩
  | 3 => ⟨((1496294922017507/9007199254740992), (12650687721033/9007199254740992)), (693/9007199254740992), by norm_num⟩
  | 2 => ⟨((560488391896157/1125899906842624), (98704534849/17592186044416)), (695/2251799813685248), by norm_num⟩
  | 1 => ⟨((1118469931333711/1125899906842624), (4727483965695/281474976710656)), (131/140737488355328), by norm_num⟩
  | 0 => ⟨((1110859585887819/1125899906842624), (18827067317843/562949953421312)), (2119/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1110859585887819/1125899906842624), (18827067317843/562949953421312)), (8083347800826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1094760891454611/1125899906842624), (37151132311275/562949953421312)), (1081/281474976710656), by norm_num⟩
  | 2 => ⟨((529789804440053/562949953421312), (9030910847505/70368744177664)), (2245/281474976710656), by norm_num⟩
  | 3 => ⟨((978621864226001/1125899906842624), (271966456001293/1125899906842624)), (2401/140737488355328), by norm_num⟩
  | 4 => ⟨((784914355690409/1125899906842624), (472781494272077/1125899906842624)), (42671/1125899906842624), by norm_num⟩
  | 5 => ⟨((348670607446479/1125899906842624), (1318387113112309/2251799813685248)), (190665/2251799813685248), by norm_num⟩
  | 6 => ⟨((-555937433880259/2251799813685248), (816560748934731/2251799813685248)), (170677/1125899906842624), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-70689085815/17179869184)), (1/8589934592), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-17862266831/17179869184), (-89199694987/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((367436800412007/2251799813685248), (706268715016459/2251799813685248)), (102439/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1943113573/8589934592), (-14939824479/34359738368)), (19/137438953472), by norm_num⟩
  | 2 => ⟨((10774909557/68719476736), (82843977725/274877906944)), (29/274877906944), by norm_num⟩
  | 3 => ⟨((-9958130907/137438953472), (-38282046391/274877906944)), (29/549755813888), by norm_num⟩
  | 4 => ⟨((27609801447/1099511627776), (13267546261/274877906944)), (11/549755813888), by norm_num⟩
  | 5 => ⟨((-15310124823/2199023255552), (-7357089827/549755813888)), (13/2199023255552), by norm_num⟩
  | 6 => ⟨((28299119613/17592186044416), (54395158087/17592186044416)), (13/8796093022208), by norm_num⟩
  | 7 => ⟨((-22417662825/70368744177664), (-168320761/274877906944)), (43/140737488355328), by norm_num⟩
  | 8 => ⟨((7769369891/140737488355328), (59735583189/562949953421312)), (1/17592186044416), by norm_num⟩
  | 9 => ⟨((-9573896595/1125899906842624), (-73609868563/4503599627370496)), (21/2251799813685248), by norm_num⟩
  | 10 => ⟨((42471164363/36028797018963968), (81635956569/36028797018963968)), (49/36028797018963968), by norm_num⟩
  | 11 => ⟨((-42820025939/288230376151711744), (-82306520913/288230376151711744)), (13/72057594037927936), by norm_num⟩
  | 12 => ⟨((39574107001/2305843009213693952), (76067377217/2305843009213693952)), (51/2305843009213693952), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414715929/10141204801825835211973625643008), (1421253139081/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445091076329999/158456325028528675187087900672), (105303247333/39614081257132168796771975168)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236442067734533/4951760157141521099596496896), (947640425017/19807040628566084398385987584)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891423438674913/2475880078570760549798248448), (2013522045431/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886544650197621/77371252455336267181195264), (2013281476647/154742504910672534362390528)), (27/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387833240779907/2417851639229258349412352), (943597902927/4835703278458516698824704)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260345367285487/604462909807314587353088), (825520390337/302231454903657293676544)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890320883867835/75557863725914323419136), (2682462175119/75557863725914323419136)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299435406741211/4722366482869645213696), (2011427486291/4722366482869645213696)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624053952383797/590295810358705651712), (43203621855/9223372036854775808)), (297/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826730268090815/73786976294838206464), (431908557327/9223372036854775808)), (93/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456579305363323/2305843009213693952), (485721633969/1152921504606846976)), (419/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597562876030127/1152921504606846976), (1942009317719/576460752303423488)), (419/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598853722699995/72057594037927936), (53070988193/2251799813685248)), (367/144115188075855872), by norm_num⟩
  | 4 => ⟨((748160509754871/18014398509481984), (2545435220677/18014398509481984)), (275/18014398509481984), by norm_num⟩
  | 3 => ⟨((46721906446901/281474976710656), (6356689128865/9007199254740992)), (43/562949953421312), by norm_num⟩
  | 2 => ⟨((559900298684439/1125899906842624), (24790423391/8796093022208)), (345/1125899906842624), by norm_num⟩
  | 1 => ⟨((1116749873153299/1125899906842624), (4746848743453/562949953421312)), (1037/1125899906842624), by norm_num⟩
  | 0 => ⟨((553797872017909/562949953421312), (18884255168861/1125899906842624)), (521/281474976710656), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((553797872017909/562949953421312), (18884255168861/1125899906842624)), (1987458349132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1089272420807119/1125899906842624), (37154493978017/1125899906842624)), (4171/1125899906842624), by norm_num⟩
  | 2 => ⟨((2105220798235477/2251799813685248), (71891587082181/1125899906842624)), (16693/2251799813685248), by norm_num⟩
  | 3 => ⟨((489750574334029/562949953421312), (33605932335493/281474976710656)), (33345/2251799813685248), by norm_num⟩
  | 4 => ⟨((418044603925623/562949953421312), (467779405606115/2251799813685248)), (32991/1125899906842624), by norm_num⟩
  | 5 => ⟨((1144579134418715/2251799813685248), (347371298554527/1125899906842624)), (125411/2251799813685248), by norm_num⟩
  | 6 => ⟨((367436800412007/2251799813685248), (706268715016459/2251799813685248)), (102439/1125899906842624), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/17179869184), (-89199694987/17179869184)), (1/8589934592), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-20737449597/17179869184), (-103557638923/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((1303221748208759/4503599627370496), (21261664055171/281474976710656)), (202193/4503599627370496), by norm_num⟩
  | 1 => ⟨((-64009231259/137438953472), (-8354328177/68719476736)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((51509441767/137438953472), (13445772501/137438953472)), (21/274877906944), by norm_num⟩
  | 3 => ⟨((-6908437369/34359738368), (-7213378675/137438953472)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((88949608139/1099511627776), (23218970233/1099511627776)), (23/1099511627776), by norm_num⟩
  | 5 => ⟨((-28631774327/1099511627776), (-1868474549/274877906944)), (17/2199023255552), by norm_num⟩
  | 6 => ⟨((30720708735/4398046511104), (8019183407/4398046511104)), (5/2199023255552), by norm_num⟩
  | 7 => ⟨((-28253184763/17592186044416), (-14750146059/35184372088832)), (5/8796093022208), by norm_num⟩
  | 8 => ⟨((45471746705/140737488355328), (23739444281/281474976710656)), (35/281474976710656), by norm_num⟩
  | 9 => ⟨((-16263100687/281474976710656), (-4245240183/281474976710656)), (27/1125899906842624), by norm_num⟩
  | 10 => ⟨((41879121311/4503599627370496), (21863841593/9007199254740992)), (37/9007199254740992), by norm_num⟩
  | 11 => ⟨((-98039048113/72057594037927936), (-25591633143/72057594037927936)), (45/72057594037927936), by norm_num⟩
  | 12 => ⟨((52595920311/288230376151711744), (27458763081/576460752303423488)), (25/288230376151711744), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673631/10141204801825835211973625643008), (332605440481/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780107337641519/633825300114114700748351602688), (394184818277/633825300114114700748351602688)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945623783744517/19807040628566084398385987584), (221705138747/19807040628566084398385987584)), (203/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891116544497103/2475880078570760549798248448), (471065390423/2475880078570760549798248448)), (27/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772782564917105/154742504910672534362390528), (471000119957/154742504910672534362390528)), (27/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387761391795021/2417851639229258349412352), (441493275209/9671406556917033397649408)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260094064356507/604462909807314587353088), (386237292755/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944956416233469/37778931862957161709568), (627505650165/75557863725914323419136)), (9/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1299129644454143/4722366482869645213696), (117628890259/1180591620717411303424)), (27/590295810358705651712), by norm_num⟩
  | 9 => ⟨((6342320226391/2305843009213693952), (646774228491/590295810358705651712)), (297/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826205972761999/73786976294838206464), (25255965081/2305843009213693952)), (371/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912864156789165/4611686018427387904), (454417080937/4611686018427387904)), (209/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596975122717251/1152921504606846976), (908358676377/1152921504606846976)), (209/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197194458896293/144115188075855872), (794279251571/144115188075855872)), (365/144115188075855872), by norm_num⟩
  | 4 => ⟨((373888532988323/9007199254740992), (1190350523601/36028797018963968)), (137/9007199254740992), by norm_num⟩
  | 3 => ⟨((747073463127375/4503599627370496), (1486070394137/9007199254740992)), (685/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118853297538911/2251799813685248), (1483272467229/2251799813685248)), (1369/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115345825424167/1125899906842624), (4435853728683/2251799813685248)), (1027/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104854966024819/1125899906842624), (8816008263467/2251799813685248)), (4113/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104854966024819/1125899906842624), (8816008263467/2251799813685248)), (15689858443450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((271046533095571/281474976710656), (2162805603591/281474976710656)), (8105/2251799813685248), by norm_num⟩
  | 2 => ⟨((2087902696958097/2251799813685248), (33322803609111/2251799813685248)), (15735/2251799813685248), by norm_num⟩
  | 3 => ⟨((1935441701450335/2251799813685248), (61794810624665/2251799813685248)), (14823/1125899906842624), by norm_num⟩
  | 4 => ⟨((830916664605403/1125899906842624), (53113182037469/1125899906842624)), (52591/2251799813685248), by norm_num⟩
  | 5 => ⟨((1221425615605693/2251799813685248), (156790591408485/2251799813685248)), (20647/562949953421312), by norm_num⟩
  | 6 => ⟨((1303221748208759/4503599627370496), (21261664055171/281474976710656)), (202193/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20737449597/17179869184), (-103557638923/17179869184)), (1/8589934592), by norm_num⟩, -1, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-2885830621/2147483648), (-28822233327/4294967296)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((267255977849325/1125899906842624), (-121765925902493/1125899906842624)), (25363/562949953421312), by norm_num⟩
  | 1 => ⟨((-29227199037/68719476736), (26632721041/137438953472)), (13/137438953472), by norm_num⟩
  | 2 => ⟨((26184055317/68719476736), (-11929857529/68719476736)), (13/137438953472), by norm_num⟩
  | 3 => ⟨((-62554038743/274877906944), (28500580259/274877906944)), (17/274877906944), by norm_num⟩
  | 4 => ⟨((14010223907/137438953472), (-25533092279/549755813888)), (17/549755813888), by norm_num⟩
  | 5 => ⟨((-20082361081/549755813888), (4574915987/274877906944)), (27/2199023255552), by norm_num⟩
  | 6 => ⟨((47977014175/4398046511104), (-5464766027/1099511627776)), (9/2199023255552), by norm_num⟩
  | 7 => ⟨((-49121868259/17592186044416), (11190338601/8796093022208)), (5/4398046511104), by norm_num⟩
  | 8 => ⟨((88014572599/140737488355328), (-1253149697/4398046511104)), (19/70368744177664), by norm_num⟩
  | 9 => ⟨((-70089308393/562949953421312), (15966882389/281474976710656)), (1/17592186044416), by norm_num⟩
  | 10 => ⟨((25116636401/1125899906842624), (-5721762543/562949953421312)), (25/2251799813685248), by norm_num⟩
  | 11 => ⟨((-8182358383/2251799813685248), (3728008079/2251799813685248)), (17/9007199254740992), by norm_num⟩
  | 12 => ⟨((39095514969/72057594037927936), (-35625033477/144115188075855872)), (21/72057594037927936), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (-139221123899/2535301200456458802993406410752)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779896113542455/633825300114114700748351602688), (-164959678233/158456325028528675187087900672)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891009958554727/39614081257132168796771975168), (-742229980573/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236358013351277/309485009821345068724781056), (-788511217325/2475880078570760549798248448)), (27/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((886265075880207/77371252455336267181195264), (-788389589131/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550808955907083/9671406556917033397649408), (-369493017767/4835703278458516698824704)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314971763887963/151115727451828646838272), (-646483605707/604462909807314587353088)), (177/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889576492015785/75557863725914323419136), (-262573429201/18889465931478580854784)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40589919745641/147573952589676412928), (-196877118575/1180591620717411303424)), (27/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811643627545683/295147905179352825856), (-1082480070557/590295810358705651712)), (297/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825772673343163/73786976294838206464), (-676292083491/36893488147419103232)), (371/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228155124366287/1152921504606846976), (-760474061493/4611686018427387904)), (209/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596487983029851/1152921504606846976), (-1520062281855/1152921504606846976)), (209/576460752303423488), by norm_num⟩
  | 5 => ⟨((598384206474773/72057594037927936), (-664529299321/72057594037927936)), (183/72057594037927936), by norm_num⟩
  | 4 => ⟨((747457732732543/18014398509481984), (-1991597784031/36028797018963968)), (137/9007199254740992), by norm_num⟩
  | 3 => ⟨((1493349297113165/9007199254740992), (-1243009155973/4503599627370496)), (685/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118056723775459/2251799813685248), (-2480807489183/2251799813685248)), (1371/4503599627370496), by norm_num⟩
  | 1 => ⟨((278538400302479/281474976710656), (-7416421160633/2251799813685248)), (1029/1125899906842624), by norm_num⟩
  | 0 => ⟨((551240525607479/562949953421312), (-14729153345959/2251799813685248)), (4125/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((551240525607479/562949953421312), (-14729153345959/2251799813685248)), (15735634810637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((269875284630509/281474976710656), (-28845570313435/2251799813685248)), (4067/1125899906842624), by norm_num⟩
  | 2 => ⟨((2069659450645203/2251799813685248), (-55313666526527/2251799813685248)), (15807/2251799813685248), by norm_num⟩
  | 3 => ⟨((237611632588641/281474976710656), (-101679067544737/2251799813685248)), (14917/1125899906842624), by norm_num⟩
  | 4 => ⟨((1600078201258337/2251799813685248), (-85834021630389/1125899906842624)), (53065/2251799813685248), by norm_num⟩
  | 5 => ⟨((280973059603743/562949953421312), (-243966885692831/2251799813685248)), (41753/1125899906842624), by norm_num⟩
  | 6 => ⟨((267255977849325/1125899906842624), (-121765925902493/1125899906842624)), (25363/562949953421312), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-28822233327/4294967296)), (1/8589934592), by norm_num⟩, -1, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-12536430677/8589934592), (-15650950173/2147483648)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((561139398557415/4503599627370496), (-220832198019725/1125899906842624)), (519573/4503599627370496), by norm_num⟩
  | 1 => ⟨((-33322962973/137438953472), (52456007735/137438953472)), (33/137438953472), by norm_num⟩
  | 2 => ⟨((32421745923/137438953472), (-51037338915/137438953472)), (17/68719476736), by norm_num⟩
  | 3 => ⟨((-10514967407/68719476736), (33104691925/137438953472)), (23/137438953472), by norm_num⟩
  | 4 => ⟨((10230590897/137438953472), (-32209377999/274877906944)), (47/549755813888), by norm_num⟩
  | 5 => ⟨((-7963124263/274877906944), (25070622217/549755813888)), (19/549755813888), by norm_num⟩
  | 6 => ⟨((41321398191/4398046511104), (-65046904287/4398046511104)), (51/4398046511104), by norm_num⟩
  | 7 => ⟨((-45947273207/17592186044416), (36164408919/8796093022208)), (29/8796093022208), by norm_num⟩
  | 8 => ⟨((44704632627/70368744177664), (-35186345175/35184372088832)), (29/35184372088832), by norm_num⟩
  | 9 => ⟨((-38662754817/281474976710656), (60861747719/281474976710656)), (13/70368744177664), by norm_num⟩
  | 10 => ⟨((30093698795/1125899906842624), (-23686298515/562949953421312)), (21/562949953421312), by norm_num⟩
  | 11 => ⟨((-10647206165/2251799813685248), (16760512245/2251799813685248)), (61/9007199254740992), by norm_num⟩
  | 12 => ⟨((27624675381/36028797018963968), (-10871483627/9007199254740992)), (41/36028797018963968), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693181983/10141204801825835211973625643008), (-1308937520893/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889858318852401/316912650057057350374175801344), (-1550632239449/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945404005992941/19807040628566084398385987584), (-872117396845/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890649491558867/2475880078570760549798248448), (-115810836545/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772315483648379/154742504910672534362390528), (-1852662850643/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550607648421911/9671406556917033397649408), (-868270771069/4835703278458516698824704)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259710855410823/604462909807314587353088), (-1519144038903/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889290061697107/75557863725914323419136), (-2467990817045/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((40583203664069/147573952589676412928), (-1850452295803/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1622991598365051/590295810358705651712), (-2543493357359/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825402878998361/73786976294838206464), (-1589024679701/36893488147419103232)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912412334751571/4611686018427387904), (-3573494981279/9223372036854775808)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596071274770307/1152921504606846976), (-3571232981885/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74775210214661/9007199254740992), (-1561142869709/72057594037927936)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1494367033860549/36028797018963968), (-4678346441511/36028797018963968)), (1099/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492662262316975/9007199254740992), (-5839048414397/9007199254740992)), (1375/9007199254740992), by norm_num⟩
  | 2 => ⟨((558683728052879/1125899906842624), (-364108734705/140737488355328)), (2753/4503599627370496), by norm_num⟩
  | 1 => ⟨((2226228305308451/2251799813685248), (-4352700979791/562949953421312)), (1035/562949953421312), by norm_num⟩
  | 0 => ⟨((2200760352027377/2251799813685248), (-34556713097939/2251799813685248)), (8323/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2200760352027377/2251799813685248), (-34556713097939/2251799813685248)), (31749733931731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((537586859543141/562949953421312), (-16886724037397/562949953421312)), (16525/2251799813685248), by norm_num⟩
  | 2 => ⟨((512859923604377/562949953421312), (-64503644688585/1125899906842624)), (16277/1125899906842624), by norm_num⟩
  | 3 => ⟨((232689530927885/281474976710656), (-235057017670155/2251799813685248)), (31523/1125899906842624), by norm_num⟩
  | 4 => ⟨((757170090595975/1125899906842624), (-97158382997577/562949953421312)), (117401/2251799813685248), by norm_num⟩
  | 5 => ⟨((475661768236703/1125899906842624), (-261356879805539/1125899906842624)), (99215/1125899906842624), by norm_num⟩
  | 6 => ⟨((561139398557415/4503599627370496), (-220832198019725/1125899906842624)), (519573/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12536430677/8589934592), (-15650950173/2147483648)), (1/4294967296), by norm_num⟩, -1, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-13396700123/8589934592), (-8362471405/1073741824)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((31137077978757/2251799813685248), (-1889429824190987/9007199254740992)), (1156575/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3951888027/137438953472), (119902309159/274877906944)), (19/68719476736), by norm_num⟩
  | 2 => ⟨((8217720131/274877906944), (-124664921305/274877906944)), (41/137438953472), by norm_num⟩
  | 3 => ⟨((-5696089539/274877906944), (43205569359/137438953472)), (59/274877906944), by norm_num⟩
  | 4 => ⟨((2961171303/274877906944), (-89843455757/549755813888)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((-307879131/68719476736), (18682421415/274877906944)), (55/1099511627776), by norm_num⟩
  | 6 => ⟨((6828977651/4398046511104), (-103597341839/4398046511104)), (79/4398046511104), by norm_num⟩
  | 7 => ⟨((-4057274233/8796093022208), (61549890351/8796093022208)), (97/17592186044416), by norm_num⟩
  | 8 => ⟨((4218432293/35184372088832), (-63994699441/35184372088832)), (13/8796093022208), by norm_num⟩
  | 9 => ⟨((-3898659267/140737488355328), (118287321303/281474976710656)), (99/281474976710656), by norm_num⟩
  | 10 => ⟨((6485627229/1125899906842624), (-98388627909/1125899906842624)), (85/1125899906842624), by norm_num⟩
  | 11 => ⟨((-4904175521/4503599627370496), (37198800019/2251799813685248)), (67/4503599627370496), by norm_num⟩
  | 12 => ⟨((6798630871/36028797018963968), (-51568486707/18014398509481984)), (95/36028797018963968), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521241/10141204801825835211973625643008), (-490098870821/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444890127670491/158456325028528675187087900672), (-2321998160121/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890632300149797/39614081257132168796771975168), (-1305942060235/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236307838575803/309485009821345068724781056), (-2774684856539/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772128600498501/154742504910672534362390528), (-1387093828821/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193804042383997/1208925819614629174706176), (-2600272742475/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259557353403409/604462909807314587353088), (-1137355280617/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889040421723581/75557863725914323419136), (-3695414704719/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162309389138767/590295810358705651712), (-2770695024431/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811366817471943/295147905179352825856), (-3808298792867/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((114067500070067/4611686018427387904), (-1189565969157/18446744073709551616)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824460850239017/9223372036854775808), (-2675073626489/4611686018427387904)), (419/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595706729638455/1152921504606846976), (-5346524410053/1152921504606846976)), (419/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196083571487995/144115188075855872), (-4674135452941/144115188075855872)), (367/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493885720136013/36028797018963968), (-7003062098231/36028797018963968)), (551/18014398509481984), by norm_num⟩
  | 3 => ⟨((746028892116341/4503599627370496), (-2184898405717/2251799813685248)), (1379/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233517485110687/4503599627370496), (-8718268403371/2251799813685248)), (691/1125899906842624), by norm_num⟩
  | 1 => ⟨((2224381116024183/2251799813685248), (-26048359539737/2251799813685248)), (4161/2251799813685248), by norm_num⟩
  | 0 => ⟨((1098491274397017/1125899906842624), (-51672018671851/2251799813685248)), (8387/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1098491274397017/1125899906842624), (-51672018671851/2251799813685248)), (31993874556731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1071157012464831/1125899906842624), (-12603531916235/281474976710656)), (16751/2251799813685248), by norm_num⟩
  | 2 => ⟨((2033636834192203/2251799813685248), (-95925838606799/1125899906842624)), (16687/1125899906842624), by norm_num⟩
  | 3 => ⟨((910132348893281/1125899906842624), (-346528705715277/2251799813685248)), (65969/2251799813685248), by norm_num⟩
  | 4 => ⟨((1418101825355977/2251799813685248), (-280119913835003/1125899906842624)), (63479/1125899906842624), by norm_num⟩
  | 5 => ⟨((376841696196947/1125899906842624), (-176409358733299/562949953421312)), (223081/2251799813685248), by norm_num⟩
  | 6 => ⟨((31137077978757/2251799813685248), (-1889429824190987/9007199254740992)), (1156575/9007199254740992), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13396700123/8589934592), (-8362471405/1073741824)), (1/4294967296), by norm_num⟩, -1, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨8,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile008Terms0
