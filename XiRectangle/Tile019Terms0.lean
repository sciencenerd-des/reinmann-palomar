/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile019Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨19,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5499/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5499/640))
  have he : value ((3/4), (5499/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1116391677/2147483648), (-12789662149/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1267748494686295/2251799813685248), (215373179215085/1125899906842624)), (844085/2251799813685248), by norm_num⟩
  | 1 => ⟨((-13408451763/34359738368), (-2277913085/17179869184)), (11/34359738368), by norm_num⟩
  | 2 => ⟨((18588061071/137438953472), (3157858065/68719476736)), (17/137438953472), by norm_num⟩
  | 3 => ⟨((-17179016165/549755813888), (-5836961105/549755813888)), (17/549755813888), by norm_num⟩
  | 4 => ⟨((2976896655/549755813888), (4045873133/2199023255552)), (13/2199023255552), by norm_num⟩
  | 5 => ⟨((-13205936149/17592186044416), (-560877111/2199023255552)), (1/1099511627776), by norm_num⟩
  | 6 => ⟨((24409753089/281474976710656), (1036721035/35184372088832)), (1/8796093022208), by norm_num⟩
  | 7 => ⟨((-9668315161/1125899906842624), (-3285029771/1125899906842624)), (7/562949953421312), by norm_num⟩
  | 8 => ⟨((13403130789/18014398509481984), (569252281/2251799813685248)), (21/18014398509481984), by norm_num⟩
  | 9 => ⟨((-2064520515/36028797018963968), (-1402935515/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 10 => ⟨((9158506075/2305843009213693952), (6223621099/4611686018427387904)), (33/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-72138553/288230376151711744), (-3137371213/36893488147419103232)), (35/73786976294838206464), by norm_num⟩
  | 12 => ⟨((17067565951/1180591620717411303424), (2899546681/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455309/5070602400912917605986812821504), (213325301501/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781168798580799/633825300114114700748351602688), (506214390387/633825300114114700748351602688)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946220807634761/19807040628566084398385987584), (284732200191/19807040628566084398385987584)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((473096276120615/618970019642690137449562112), (302511904719/1237940039285380274899124224)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221756374333161/19342813113834066795298816), (604987681337/154742504910672534362390528)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((194029322713727/1208925819614629174706176), (283568783899/4835703278458516698824704)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315283578432717/151115727451828646838272), (62025873919/75557863725914323419136)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891602978356925/75557863725914323419136), (806264403903/75557863725914323419136)), (1149/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300397026988761/4722366482869645213696), (604635346853/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625376260336309/590295810358705651712), (207817827547/147573952589676412928)), (593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828383272969519/73786976294838206464), (519467860465/36893488147419103232)), (741/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828177016482895/9223372036854775808), (584295885865/4611686018427387904)), (1667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599422876175729/1152921504606846976), (584164089757/576460752303423488)), (417/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199335175512979/144115188075855872), (1021990685503/144115188075855872)), (365/36028797018963968), by norm_num⟩
  | 4 => ⟨((749381536363621/18014398509481984), (1532393259255/36028797018963968)), (2189/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498154370084083/9007199254740992), (957227310023/4503599627370496)), (2737/9007199254740992), by norm_num⟩
  | 2 => ⟨((2245710296820053/4503599627370496), (239112496527/281474976710656)), (1369/1125899906842624), by norm_num⟩
  | 1 => ⟨((280333659422561/281474976710656), (2865466078859/1125899906842624)), (8221/2251799813685248), by norm_num⟩
  | 0 => ⟨((279194211098417/281474976710656), (11430826143337/2251799813685248)), (16469/2251799813685248), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((279194211098417/281474976710656), (11430826143337/2251799813685248)), (62824257857512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2215397384168403/2251799813685248), (11338203220007/1125899906842624)), (32839/2251799813685248), by norm_num⟩
  | 2 => ⟨((2179355074348153/2251799813685248), (44619642655827/2251799813685248)), (65279/2251799813685248), by norm_num⟩
  | 3 => ⟨((2108356879116395/2251799813685248), (86368285534613/2251799813685248)), (64473/1125899906842624), by norm_num⟩
  | 4 => ⟨((1970738793919951/2251799813685248), (20216624923507/281474976710656)), (62839/562949953421312), by norm_num⟩
  | 5 => ⟨((1713142441581719/2251799813685248), (283092212916957/2251799813685248)), (476073/2251799813685248), by norm_num⟩
  | 6 => ⟨((1267748494686295/2251799813685248), (215373179215085/1125899906842624)), (844085/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/2147483648), (-12789662149/2147483648)), (1/2147483648), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-55294967/67108864), (-20271134903/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-987738272708737/2251799813685248), (14525553915305/2251799813685248)), (611763/562949953421312), by norm_num⟩
  | 1 => ⟨((33115887585/68719476736), (-15218689/2147483648)), (85/68719476736), by norm_num⟩
  | 2 => ⟨((-18190760525/68719476736), (66877755/17179869184)), (3/4294967296), by norm_num⟩
  | 3 => ⟨((13323062035/137438953472), (-391854525/274877906944)), (73/274877906944), by norm_num⟩
  | 4 => ⟨((-7318439837/274877906944), (430496197/1099511627776)), (83/1099511627776), by norm_num⟩
  | 5 => ⟨((6432102351/1099511627776), (-189179365/2199023255552)), (75/4398046511104), by norm_num⟩
  | 6 => ⟨((-9421848913/8796093022208), (138556517/8796093022208)), (57/17592186044416), by norm_num⟩
  | 7 => ⟨((5914833713/35184372088832), (-173965591/70368744177664)), (37/70368744177664), by norm_num⟩
  | 8 => ⟨((-12996218005/562949953421312), (5972523/17592186044416)), (21/281474976710656), by norm_num⟩
  | 9 => ⟨((6345691025/2251799813685248), (-186637857/4503599627370496)), (21/2251799813685248), by norm_num⟩
  | 10 => ⟨((-348572707/1125899906842624), (328068229/72057594037927936)), (19/18014398509481984), by norm_num⟩
  | 11 => ⟨((8912203855/288230376151711744), (-131061741/288230376151711744)), (63/576460752303423488), by norm_num⟩
  | 12 => ⟨((-1631842779/576460752303423488), (383962771/9223372036854775808)), (95/9223372036854775808), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (4073120530753/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780686621520371/633825300114114700748351602688), (4830275776361/633825300114114700748351602688)), (1449/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891898459036075/39614081257132168796771975168), (5433620501821/39614081257132168796771975168)), (815/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891807130315579/2475880078570760549798248448), (1443182911337/618970019642690137449562112)), (1733/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443368010290093/38685626227668133590597632), (2886089949423/77371252455336267181195264)), (867/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775845386263005/4835703278458516698824704), (5410832148127/9671406556917033397649408)), (813/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260657440729733/604462909807314587353088), (295868206995/37778931862957161709568)), (1423/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118176631903069/4722366482869645213696), (7691472438963/75557863725914323419136)), (1157/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649906335545637/2361183241434822606848), (5767640344889/4722366482869645213696)), (1737/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624570001633749/590295810358705651712), (7928937764463/590295810358705651712)), (2389/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913685648862415/36893488147419103232), (1238602310151/9223372036854775808)), (2989/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827032839010053/9223372036854775808), (2786045228587/2305843009213693952)), (1683/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1598271572294087/1152921504606846976), (1392515726915/144115188075855872)), (3371/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198319774623591/144115188075855872), (9743040889587/144115188075855872)), (1477/72057594037927936), by norm_num⟩
  | 4 => ⟨((748611984733617/18014398509481984), (7302702468069/18014398509481984)), (2221/18014398509481984), by norm_num⟩
  | 3 => ⟨((748101264160967/4503599627370496), (4560173013901/2251799813685248)), (2785/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120861444103909/2251799813685248), (35579131363/4398046511104)), (1399/562949953421312), by norm_num⟩
  | 1 => ⟨((559119855306809/562949953421312), (13632024822355/562949953421312)), (8461/1125899906842624), by norm_num⟩
  | 0 => ⟨((1110171226512957/1125899906842624), (54283526384489/1125899906842624)), (2149/140737488355328), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1110171226512957/1125899906842624), (54283526384489/1125899906842624)), (8197784960699037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1092045077424817/1125899906842624), (26762596168391/281474976710656)), (35563/1125899906842624), by norm_num⟩
  | 2 => ⟨((262257474907605/281474976710656), (207662945717855/1125899906842624)), (75751/1125899906842624), by norm_num⟩
  | 3 => ⟨((469553210222525/562949953421312), (386969814597931/1125899906842624)), (169103/1125899906842624), by norm_num⟩
  | 4 => ⟨((325151120033577/562949953421312), (645538444756517/1125899906842624)), (199169/562949953421312), by norm_num⟩
  | 5 => ⟨((10965663537547/2251799813685248), (186426472781167/281474976710656)), (916925/1125899906842624), by norm_num⟩
  | 6 => ⟨((-987738272708737/2251799813685248), (14525553915305/2251799813685248)), (611763/562949953421312), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-20271134903/2147483648)), (1/1073741824), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1116391677/1073741824), (-12789662149/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((157834170231131/562949953421312), (970029474507707/4503599627370496)), (2567479/4503599627370496), by norm_num⟩
  | 1 => ⟨((-13354774181/34359738368), (-10259600759/34359738368)), (29/34359738368), by norm_num⟩
  | 2 => ⟨((18513648141/68719476736), (1777853335/8589934592)), (43/68719476736), by norm_num⟩
  | 3 => ⟨((-17110244015/137438953472), (-13144682951/137438953472)), (21/68719476736), by norm_num⟩
  | 4 => ⟨((5929958699/137438953472), (9111199927/274877906944)), (31/274877906944), by norm_num⟩
  | 5 => ⟨((-6576534645/549755813888), (-5052322033/549755813888)), (9/274877906944), by norm_num⟩
  | 6 => ⟨((1519502149/549755813888), (2334668515/1099511627776)), (35/4398046511104), by norm_num⟩
  | 7 => ⟨((-19259220671/35184372088832), (-924725085/2199023255552)), (29/17592186044416), by norm_num⟩
  | 8 => ⟨((3337368627/35184372088832), (1281941171/17592186044416)), (21/70368744177664), by norm_num⟩
  | 9 => ⟨((-8225022771/562949953421312), (-12637495585/1125899906842624)), (27/562949953421312), by norm_num⟩
  | 10 => ⟨((4560921075/2251799813685248), (14015431095/9007199254740992)), (31/4503599627370496), by norm_num⟩
  | 11 => ⟨((-9196769699/36028797018963968), (-14130554979/72057594037927936)), (65/72057594037927936), by norm_num⟩
  | 12 => ⟨((8499619983/288230376151711744), (13059405791/576460752303423488)), (31/288230376151711744), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791310707357927/5070602400912917605986812821504), (213325301501/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780365273805099/633825300114114700748351602688), (1011562379419/633825300114114700748351602688)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472884422250567/9903520314283042199192993792), (1137901666583/39614081257132168796771975168)), (1623/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891424729011789/2475880078570760549798248448), (1208892198377/2475880078570760549798248448)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886545335579895/77371252455336267181195264), (151093481953/19342813113834066795298816)), (1725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775667166819265/4835703278458516698824704), (566523885833/4835703278458516698824704)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260346651886001/604462909807314587353088), (495631740533/302231454903657293676544)), (177/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((118145195712307/4722366482869645213696), (1610515733993/75557863725914323419136)), (575/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324859308092369/1180591620717411303424), (603817678121/2361183241434822606848)), (863/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101503543123153/36893488147419103232), (1660090112861/590295810358705651712)), (2373/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826734030882243/73786976294838206464), (2074500054227/73786976294838206464)), (1483/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826321922857899/9223372036854775808), (2332970523945/9223372036854775808)), (3337/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597568162244933/1152921504606846976), (2331918382291/1152921504606846976)), (3339/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299428182008665/36028797018963968), (2039245481373/144115188075855872)), (2923/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496330256069469/36028797018963968), (3056503405803/36028797018963968)), (4385/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495114845049441/9007199254740992), (3816493954743/9007199254740992)), (5485/9007199254740992), by norm_num⟩
  | 2 => ⟨((2239635735339959/4503599627370496), (3810297248927/2251799813685248)), (2745/1125899906842624), by norm_num⟩
  | 1 => ⟨((2233568658899541/2251799813685248), (2849987979499/562949953421312)), (16497/2251799813685248), by norm_num⟩
  | 0 => ⟨((1107698692084201/1125899906842624), (22676406440013/2251799813685248)), (33107/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1107698692084201/1125899906842624), (22676406440013/2251799813685248)), (126293190962981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2179355074348151/2251799813685248), (44619642655825/2251799813685248)), (65811/2251799813685248), by norm_num⟩
  | 2 => ⟨((2108356879116391/2251799813685248), (86368285534609/2251799813685248)), (129997/2251799813685248), by norm_num⟩
  | 3 => ⟨((246342349239993/281474976710656), (10108312461753/140737488355328)), (253405/2251799813685248), by norm_num⟩
  | 4 => ⟨((428285610395427/562949953421312), (141546106458471/1125899906842624)), (239977/1125899906842624), by norm_num⟩
  | 5 => ⟨((1267748494686283/2251799813685248), (6730411850471/35184372088832)), (425483/1125899906842624), by norm_num⟩
  | 6 => ⟨((157834170231131/562949953421312), (970029474507707/4503599627370496)), (2567479/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/1073741824), (-12789662149/1073741824)), (1/1073741824), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-162011325/134217728), (-29696675867/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((409051836311109/4503599627370496), (-320818334432659/1125899906842624)), (2995757/4503599627370496), by norm_num⟩
  | 1 => ⟨((-2511381277/17179869184), (3939340137/8589934592)), (19/17179869184), by norm_num⟩
  | 2 => ⟨((8083824479/68719476736), (-25360493465/68719476736)), (1/1073741824), by norm_num⟩
  | 3 => ⟨((-4336804531/68719476736), (13605379887/68719476736)), (9/17179869184), by norm_num⟩
  | 4 => ⟨((6979817631/274877906944), (-21897014203/274877906944)), (15/68719476736), by norm_num⟩
  | 5 => ⟨((-4493433247/549755813888), (14096753931/549755813888)), (5/68719476736), by norm_num⟩
  | 6 => ⟨((4821267883/2199023255552), (-15125233479/2199023255552)), (11/549755813888), by norm_num⟩
  | 7 => ⟨((-4434017895/8796093022208), (13910356683/8796093022208)), (21/4398046511104), by norm_num⟩
  | 8 => ⟨((7136276505/70368744177664), (-22387855421/70368744177664)), (35/35184372088832), by norm_num⟩
  | 9 => ⟨((-2552309769/140737488355328), (16014161463/281474976710656)), (13/70368744177664), by norm_num⟩
  | 10 => ⟨((3286227285/1125899906842624), (-20619038875/2251799813685248)), (69/2251799813685248), by norm_num⟩
  | 11 => ⟨((-7693060045/18014398509481984), (6033647797/4503599627370496)), (83/18014398509481984), by norm_num⟩
  | 12 => ⟨((8254334999/144115188075855872), (-6473854343/36028797018963968)), (91/144115188075855872), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (-1644184690249/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890052696946117/316912650057057350374175801344), (-974296515419/316912650057057350374175801344)), (1445/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((29550707283759/618970019642690137449562112), (-2191929247453/39614081257132168796771975168)), (1625/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118194622244943/154742504910672534362390528), (-1164318838795/1237940039285380274899124224)), (1727/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772779815061521/154742504910672534362390528), (-1164157334677/77371252455336267181195264)), (1727/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551042817896509/9671406556917033397649408), (-1091225923357/4835703278458516698824704)), (1619/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157511435938849/75557863725914323419136), (-1909302255559/604462909807314587353088)), (709/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889908324201929/75557863725914323419136), (-3101972930109/75557863725914323419136)), (2303/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299125982627585/4722366482869645213696), (-2325916963475/4722366482869645213696)), (27/73786976294838206464), by norm_num⟩
  | 9 => ⟨((202953560901063/73786976294838206464), (-3197221563121/590295810358705651712)), (2377/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826198426220361/73786976294838206464), (-3995155878647/73786976294838206464)), (743/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1825718885253815/9223372036854775808), (-2246332825267/4611686018427387904)), (209/576460752303423488), by norm_num⟩
  | 6 => ⟨((1596964522521293/1152921504606846976), (-2245155266351/576460752303423488)), (1673/576460752303423488), by norm_num⟩
  | 5 => ⟨((598591933516039/72057594037927936), (-3926373271989/144115188075855872)), (1465/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495535614924545/36028797018963968), (-5884265678569/36028797018963968)), (4399/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494119188146953/9007199254740992), (-3673036589895/4503599627370496)), (5505/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118818690344217/2251799813685248), (-7332196769933/2251799813685248)), (1379/562949953421312), by norm_num⟩
  | 1 => ⟨((1115276807068235/1125899906842624), (-2740911506221/281474976710656)), (8301/1125899906842624), by norm_num⟩
  | 0 => ⟨((552324444559993/562949953421312), (-21788946955913/1125899906842624)), (16711/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((552324444559993/562949953421312), (-21788946955913/1125899906842624)), (63747410300826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1083377307886277/1125899906842624), (-10688843610193/281474976710656)), (33439/1125899906842624), by norm_num⟩
  | 2 => ⟨((2081674156072471/2251799813685248), (-164562416882011/2251799813685248)), (16723/281474976710656), by norm_num⟩
  | 3 => ⟨((956187685254847/1125899906842624), (-304259133695789/2251799813685248)), (66727/562949953421312), by norm_num⟩
  | 4 => ⟨((98937689632505/140737488355328), (-516793428968437/2251799813685248)), (525481/2251799813685248), by norm_num⟩
  | 5 => ⟨((994237207145165/2251799813685248), (-726605945251851/2251799813685248)), (245005/562949953421312), by norm_num⟩
  | 6 => ⟨((409051836311109/4503599627370496), (-320818334432659/1125899906842624)), (2995757/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-29696675867/2147483648)), (1/1073741824), by norm_num⟩, -2, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1442915311/1073741824), (-8265199263/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1117737491218727/4503599627370496), (-361532950022775/4503599627370496)), (6345183/4503599627370496), by norm_num⟩
  | 1 => ⟨((7639758049/17179869184), (4942169851/34359738368)), (89/34359738368), by norm_num⟩
  | 2 => ⟨((-13688608827/34359738368), (-4427589815/34359738368)), (81/34359738368), by norm_num⟩
  | 3 => ⟨((8175564829/34359738368), (5288783985/68719476736)), (49/34359738368), by norm_num⟩
  | 4 => ⟨((-14648645699/137438953472), (-4738114393/137438953472)), (89/137438953472), by norm_num⟩
  | 5 => ⟨((10498739857/274877906944), (848956133/68719476736)), (129/549755813888), by norm_num⟩
  | 6 => ⟨((-3135202759/274877906944), (-4056333841/1099511627776)), (39/549755813888), by norm_num⟩
  | 7 => ⟨((12840066815/4398046511104), (2076564163/2199023255552)), (81/4398046511104), by norm_num⟩
  | 8 => ⟨((-11503155651/17592186044416), (-7441407005/35184372088832)), (147/35184372088832), by norm_num⟩
  | 9 => ⟨((9160394695/70368744177664), (5925871763/140737488355328)), (119/140737488355328), by norm_num⟩
  | 10 => ⟨((-6565289575/281474976710656), (-2123547369/281474976710656)), (87/562949953421312), by norm_num⟩
  | 11 => ⟨((4277607187/1125899906842624), (345898737/281474976710656)), (115/4503599627370496), by norm_num⟩
  | 12 => ⟨((-20438515155/36028797018963968), (-6610851599/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582225292035027/10141204801825835211973625643008), (-3684779250131/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779886166969199/633825300114114700748351602688), (-2183002056145/316912650057057350374175801344)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1890998186158403/39614081257132168796771975168), (-4911141091781/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890850865286721/2475880078570760549798248448), (-326085537577/154742504910672534362390528)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772516085544687/154742504910672534362390528), (-652069970379/19342813113834066795298816)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((48462340404915/302231454903657293676544), (-4889665305855/9671406556917033397649408)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259873875006209/604462909807314587353088), (-2138798789511/302231454903657293676544)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889553432999951/75557863725914323419136), (-6949484189875/75557863725914323419136)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298858702914911/4722366482869645213696), (-5210702557035/4722366482869645213696)), (3469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623259173055131/590295810358705651712), (-7162423452189/590295810358705651712)), (4773/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114108379939823/4611686018427387904), (-4474794918569/36893488147419103232)), (1493/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912596389892353/4611686018427387904), (-1257944782515/1152921504606846976)), (1681/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596433779123067/1152921504606846976), (-1257205480821/144115188075855872)), (1683/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196714256698395/144115188075855872), (-8793782556483/144115188075855872)), (1475/36028797018963968), by norm_num⟩
  | 4 => ⟨((747410399612457/18014398509481984), (-13177357011255/36028797018963968)), (8869/36028797018963968), by norm_num⟩
  | 3 => ⟨((373301878021697/2251799813685248), (-16448380194583/9007199254740992)), (11117/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117879867430293/2251799813685248), (-2051672880009/281474976710656)), (5583/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113801012743387/1125899906842624), (-12266250962995/562949953421312)), (16871/1125899906842624), by norm_num⟩
  | 0 => ⟨((1101428902772585/1125899906842624), (-48714242240867/1125899906842624)), (34231/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1101428902772585/1125899906842624), (-48714242240867/1125899906842624)), (130580906394576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((268845512622233/281474976710656), (-95310913616153/1125899906842624)), (69937/1125899906842624), by norm_num⟩
  | 2 => ⟨((31845703414841/35184372088832), (-22758605160103/140737488355328)), (145439/1125899906842624), by norm_num⟩
  | 3 => ⟨((892920701684419/1125899906842624), (-329584413550087/1125899906842624)), (77579/281474976710656), by norm_num⟩
  | 4 => ⟨((152918010219203/281474976710656), (-522768931807945/1125899906842624)), (673885/1125899906842624), by norm_num⟩
  | 5 => ⟨((89577527197435/1125899906842624), (-284006719853697/562949953421312)), (2715989/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1117737491218727/4503599627370496), (-361532950022775/4503599627370496)), (6345183/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1442915311/1073741824), (-8265199263/536870912)), (1/536870912), by norm_num⟩, -2, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-1567053835/1073741824), (-17952560493/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((-277557569748967/2251799813685248), (887127026228061/4503599627370496)), (5818933/4503599627370496), by norm_num⟩
  | 1 => ⟨((8241303893/34359738368), (-823149435/2147483648)), (11/4294967296), by norm_num⟩
  | 2 => ⟨((-2004604611/8589934592), (6407099359/17179869184)), (87/34359738368), by norm_num⟩
  | 3 => ⟨((2600520305/17179869184), (-8311759779/34359738368)), (115/68719476736), by norm_num⟩
  | 4 => ⟨((-10120757709/137438953472), (16173937711/137438953472)), (57/68719476736), by norm_num⟩
  | 5 => ⟨((7877634057/274877906944), (-12589211817/274877906944)), (45/137438953472), by norm_num⟩
  | 6 => ⟨((-10219445375/1099511627776), (16331650029/1099511627776)), (59/549755813888), by norm_num⟩
  | 7 => ⟨((2840874639/1099511627776), (-9079978155/2199023255552)), (133/4398046511104), by norm_num⟩
  | 8 => ⟨((-11056173585/17592186044416), (17668821645/17592186044416)), (131/17592186044416), by norm_num⟩
  | 9 => ⟨((9561920173/70368744177664), (-7640430969/35184372088832)), (115/70368744177664), by norm_num⟩
  | 10 => ⟨((-1860663751/70368744177664), (11894073733/281474976710656)), (91/281474976710656), by norm_num⟩
  | 11 => ⟨((10532900297/2251799813685248), (-16832580939/2251799813685248)), (65/1125899906842624), by norm_num⟩
  | 12 => ⟨((-3416012931/4503599627370496), (2729557507/2251799813685248)), (43/4503599627370496), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197759336647691/1267650600228229401496703205376), (1387236508315/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889856075618661/316912650057057350374175801344), (1643389099325/316912650057057350374175801344)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890802703488487/39614081257132168796771975168), (3697136095221/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890643520667305/2475880078570760549798248448), (3927620790793/2475880078570760549798248448)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221538642624493/19342813113834066795298816), (3926961195757/154742504910672534362390528)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387650326841649/2417851639229258349412352), (3680825347749/9671406556917033397649408)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78731557023007/37778931862957161709568), (3220021458189/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944639832382499/37778931862957161709568), (5231221128523/75557863725914323419136)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298654072922769/4722366482869645213696), (3922266434139/4722366482869645213696)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622978937437325/590295810358705651712), (5391248760739/590295810358705651712)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825385479260711/73786976294838206464), (3368129968727/36893488147419103232)), (2979/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824802933383487/9223372036854775808), (7574441631709/9223372036854775808)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596046840262869/1152921504606846976), (3784814514821/576460752303423488)), (3357/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196378952200031/144115188075855872), (827251557233/18014398509481984)), (2941/72057594037927936), by norm_num⟩
  | 4 => ⟨((747162183266835/18014398509481984), (2479048973939/9007199254740992)), (2209/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492598365917735/9007199254740992), (12376311975351/9007199254740992)), (5535/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117287768469931/2251799813685248), (6173963339313/1125899906842624)), (5553/1125899906842624), by norm_num⟩
  | 1 => ⟨((556477662643677/562949953421312), (9225488111943/562949953421312)), (16751/1125899906842624), by norm_num⟩
  | 0 => ⟨((1099906428639429/1125899906842624), (36618596278239/1125899906842624)), (33869/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1099906428639429/1125899906842624), (36618596278239/1125899906842624)), (129199985984420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((536661040126487/562949953421312), (35773188370835/562949953421312)), (34189/562949953421312), by norm_num⟩
  | 2 => ⟨((509326538248849/562949953421312), (34102634458103/281474976710656)), (139061/1125899906842624), by norm_num⟩
  | 3 => ⟨((226273723186509/281474976710656), (246833689540601/1125899906842624)), (285327/1125899906842624), by norm_num⟩
  | 4 => ⟨((10523108698073/17592186044416), (396852172032529/1125899906842624)), (583847/1125899906842624), by norm_num⟩
  | 5 => ⟨((262973872579553/1125899906842624), (949539422291461/2251799813685248)), (1110063/1125899906842624), by norm_num⟩
  | 6 => ⟨((-277557569748967/2251799813685248), (887127026228061/4503599627370496)), (5818933/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1567053835/1073741824), (-17952560493/1073741824)), (1/536870912), by norm_num⟩, -3, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1674587515/1073741824), (-19184493223/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((525320049582691/4503599627370496), (787656766471539/4503599627370496)), (930753/1125899906842624), by norm_num⟩
  | 1 => ⟨((-8334139509/34359738368), (-12496080023/34359738368)), (61/34359738368), by norm_num⟩
  | 2 => ⟨((8665177955/34359738368), (6496216977/17179869184)), (33/17179869184), by norm_num⟩
  | 3 => ⟨((-12012487337/68719476736), (-2251417241/8589934592)), (47/34359738368), by norm_num⟩
  | 4 => ⟨((6244816297/68719476736), (9363381077/68719476736)), (101/137438953472), by norm_num⟩
  | 5 => ⟨((-10388584343/274877906944), (-7788241433/137438953472)), (87/274877906944), by norm_num⟩
  | 6 => ⟨((7200817947/549755813888), (5398397591/274877906944)), (63/549755813888), by norm_num⟩
  | 7 => ⟨((-2139097139/549755813888), (-12829316811/2199023255552)), (77/2199023255552), by norm_num⟩
  | 8 => ⟨((8896254905/8796093022208), (3334726791/2199023255552)), (41/4398046511104), by norm_num⟩
  | 9 => ⟨((-2055471335/8796093022208), (-12327767857/35184372088832)), (39/17592186044416), by norm_num⟩
  | 10 => ⟨((6838771971/140737488355328), (20507898079/281474976710656)), (133/281474976710656), by norm_num⟩
  | 11 => ⟨((-10342419295/1125899906842624), (-3876815927/281474976710656)), (103/1125899906842624), by norm_num⟩
  | 12 => ⟨((7168818775/4503599627370496), (10748816117/4503599627370496)), (37/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49435757453803/316912650057057350374175801344), (1279951809613/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889781081833585/316912650057057350374175801344), (189505495977/79228162514264337593543950336)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472658563879267/9903520314283042199192993792), (1705313516843/39614081257132168796771975168)), (203/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((236308113492555/309485009821345068724781056), (1811607202277/2475880078570760549798248448)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772130936732525/154742504910672534362390528), (1811282812349/154742504910672534362390528)), (863/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550434674677999/9671406556917033397649408), (424433260929/2417851639229258349412352)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259559542366977/604462909807314587353088), (1485171900749/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1889044251076049/75557863725914323419136), (2412758548499/75557863725914323419136)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298478223209005/4722366482869645213696), (1809004015615/4722366482869645213696)), (3453/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622738297905477/590295810358705651712), (1243231442899/295147905179352825856)), (4749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825086409141355/73786976294838206464), (3106702713449/73786976294838206464)), (2969/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912234427469569/4611686018427387904), (1746574803923/4611686018427387904)), (6681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595715727608151/1152921504606846976), (3490787290055/1152921504606846976)), (1671/288230376151711744), by norm_num⟩
  | 5 => ⟨((149511570039579/18014398509481984), (3051783144705/144115188075855872)), (1463/36028797018963968), by norm_num⟩
  | 4 => ⟨((746950715018109/18014398509481984), (2286183964767/18014398509481984)), (549/2251799813685248), by norm_num⟩
  | 3 => ⟨((746040654013383/4503599627370496), (2853091778649/4503599627370496)), (10991/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233576151094977/4503599627370496), (5692290052607/2251799813685248)), (22015/4503599627370496), by norm_num⟩
  | 1 => ⟨((278062252284035/281474976710656), (4251887411601/562949953421312)), (33107/2251799813685248), by norm_num⟩
  | 0 => ⟨((274666389050439/281474976710656), (8434674472859/562949953421312)), (66553/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((274666389050439/281474976710656), (8434674472859/562949953421312)), (253879555709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2143674445865183/2251799813685248), (32922593792877/1125899906842624)), (65941/1125899906842624), by norm_num⟩
  | 2 => ⟨((1019407789543613/1125899906842624), (125366957713507/2251799813685248)), (258813/2251799813685248), by norm_num⟩
  | 3 => ⟨((1838996551236623/2251799813685248), (56754624664161/562949953421312)), (248743/1125899906842624), by norm_num⟩
  | 4 => ⟨((1478981788917311/2251799813685248), (370802265422729/2251799813685248)), (912883/2251799813685248), by norm_num⟩
  | 5 => ⟨((455167639558423/1125899906842624), (487085747602033/2251799813685248)), (374953/562949953421312), by norm_num⟩
  | 6 => ⟨((525320049582691/4503599627370496), (787656766471539/4503599627370496)), (930753/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1674587515/1073741824), (-19184493223/1073741824)), (1/536870912), by norm_num⟩, -3, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile019Terms0
