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
namespace Reinmann.XiRectangle.Tile024Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6909/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6909/640))
  have he : value ((3/4), (6909/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-279097919/536870912), (-4017265675/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((485726147075595/2251799813685248), (-1247717429066721/2251799813685248)), (2869295/562949953421312), by norm_num⟩
  | 1 => ⟨((-1284331167/8589934592), (1649573933/4294967296)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1780461055/34359738368), (-4573590083/34359738368)), (47/34359738368), by norm_num⟩
  | 3 => ⟨((-822747707/68719476736), (2113447381/68719476736)), (45/137438953472), by norm_num⟩
  | 4 => ⟨((1140570507/549755813888), (-2929860187/549755813888)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((-632466585/2199023255552), (3249318925/4398046511104)), (37/4398046511104), by norm_num⟩
  | 6 => ⟨((2338092961/70368744177664), (-6006016671/70368744177664)), (71/70368744177664), by norm_num⟩
  | 7 => ⟨((-1852162907/562949953421312), (2378887727/281474976710656)), (29/281474976710656), by norm_num⟩
  | 8 => ⟨((1283821497/4503599627370496), (-1648919321/2251799813685248)), (21/2251799813685248), by norm_num⟩
  | 9 => ⟨((-791002001/36028797018963968), (4063800101/72057594037927936)), (53/72057594037927936), by norm_num⟩
  | 10 => ⟨((877249291/576460752303423488), (-1126724633/288230376151711744)), (15/288230376151711744), by norm_num⟩
  | 11 => ⟨((-1768910175/18446744073709551616), (4543918561/18446744073709551616)), (31/9223372036854775808), by norm_num⟩
  | 12 => ⟨((817410067/147573952589676412928), (-4199472453/295147905179352825856)), (59/295147905179352825856), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197912323863903/1267650600228229401496703205376), (-390638617251/2535301200456458802993406410752)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890583552304773/316912650057057350374175801344), (-926973444323/316912650057057350374175801344)), (5775/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892439606258581/39614081257132168796771975168), (-1042795077347/19807040628566084398385987584)), (6497/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892382844506227/2475880078570760549798248448), (-2215821674629/2475880078570760549798248448)), (863/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((443512148407987/38685626227668133590597632), (-1107844533087/77371252455336267181195264)), (6905/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552232180891821/9671406556917033397649408), (-1038533797227/4835703278458516698824704)), (3237/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261132063192807/604462909807314587353088), (-227161653799/75557863725914323419136)), (2833/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891599040372947/75557863725914323419136), (-1476418631841/37778931862957161709568)), (4605/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300393827805813/4722366482869645213696), (-2214396720993/4722366482869645213696)), (6909/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625371462312709/590295810358705651712), (-1522209854705/295147905179352825856)), (4751/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914188338453585/36893488147419103232), (-3804960896589/73786976294838206464)), (11881/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914084386617565/4611686018427387904), (-133743929899/288230376151711744)), (3343/2305843009213693952), by norm_num⟩
  | 6 => ⟨((799706802519245/576460752303423488), (-534854566045/144115188075855872)), (13379/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199325907521365/144115188075855872), (-3742891355799/144115188075855872)), (5857/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498746860819539/36028797018963968), (-5612155260215/36028797018963968)), (17587/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498130066377613/9007199254740992), (-7011374713235/9007199254740992)), (11005/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122824793547819/2251799813685248), (-7005643159753/2251799813685248)), (5513/562949953421312), by norm_num⟩
  | 1 => ⟨((560637001137971/562949953421312), (-5247063549201/562949953421312)), (8295/281474976710656), by norm_num⟩
  | 0 => ⟨((1116595309681035/1125899906842624), (-20930851318575/1125899906842624)), (33385/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1116595309681035/1125899906842624), (-20930851318575/1125899906842624)), (127353670360374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((138372311949105/140737488355328), (-2594734472833/70368744177664)), (16865/140737488355328), by norm_num⟩
  | 2 => ⟨((135855530389523/140737488355328), (-20409027450793/281474976710656)), (34407/140737488355328), by norm_num⟩
  | 3 => ⟨((65201508324175/70368744177664), (-39402141980273/281474976710656)), (571333/1125899906842624), by norm_num⟩
  | 4 => ⟨((118069568719871/140737488355328), (-292070477407503/1125899906842624)), (304679/281474976710656), by norm_num⟩
  | 5 => ⟨((358327550706647/562949953421312), (-245028071101037/562949953421312)), (2677143/1125899906842624), by norm_num⟩
  | 6 => ⟨((485726147075595/2251799813685248), (-1247717429066721/2251799813685248)), (2869295/562949953421312), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/536870912), (-4017265675/536870912)), (1/268435456), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-55294967/67108864), (-3183607725/268435456)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((187847059001575/562949953421312), (641290578350811/2251799813685248)), (1640401/562949953421312), by norm_num⟩
  | 1 => ⟨((-787243223/2147483648), (-1343783779/4294967296)), (15/4294967296), by norm_num⟩
  | 2 => ⟨((864875079/4294967296), (1476297373/8589934592)), (35/17179869184), by norm_num⟩
  | 3 => ⟨((-2533766373/34359738368), (-2162504581/34359738368)), (27/34359738368), by norm_num⟩
  | 4 => ⟨((1391813437/68719476736), (2375754107/137438953472)), (31/137438953472), by norm_num⟩
  | 5 => ⟨((-2446501353/549755813888), (-1044013063/274877906944)), (29/549755813888), by norm_num⟩
  | 6 => ⟨((895918817/1099511627776), (1529287441/2199023255552)), (45/4398046511104), by norm_num⟩
  | 7 => ⟨((-4499508215/35184372088832), (-3840214801/35184372088832)), (59/35184372088832), by norm_num⟩
  | 8 => ⟨((2471607509/140737488355328), (1054726793/70368744177664)), (17/70368744177664), by norm_num⟩
  | 9 => ⟨((-1206817059/562949953421312), (-16093553/8796093022208)), (35/1125899906842624), by norm_num⟩
  | 10 => ⟨((1060659241/4503599627370496), (3620981779/18014398509481984)), (1/281474976710656), by norm_num⟩
  | 11 => ⟨((-3389827713/144115188075855872), (-2893130967/144115188075855872)), (53/144115188075855872), by norm_num⟩
  | 12 => ⟨((620684397/288230376151711744), (1059476411/576460752303423488)), (41/1152921504606846976), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (920305086095/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780698424243499/633825300114114700748351602688), (1091381247047/633825300114114700748351602688)), (2885/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59122263946209/1237940039285380274899124224), (1227712687243/39614081257132168796771975168)), (1623/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891822864113003/2475880078570760549798248448), (1304334977237/2475880078570760549798248448)), (3449/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773488756197237/154742504910672534362390528), (1304211516175/154742504910672534362390528)), (6899/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551707485173691/9671406556917033397649408), (1222567131545/9671406556917033397649408)), (1617/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260673106297787/604462909807314587353088), (1069615089303/604462909807314587353088)), (1415/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890853520113471/75557863725914323419136), (434469660567/18889465931478580854784)), (4599/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299834936679805/4722366482869645213696), (651596934239/2361183241434822606848)), (1725/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1624603391676907/590295810358705651712), (447885516555/147573952589676412928)), (593/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1827417195476561/73786976294838206464), (1119451713225/36893488147419103232)), (11863/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827090190853341/9223372036854775808), (2518045799173/9223372036854775808)), (13349/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598336065125357/1152921504606846976), (78660791991/36028797018963968)), (13353/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599192116220063/72057594037927936), (2201489491959/144115188075855872)), (11689/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497336691796617/36028797018963968), (1650104845867/18014398509481984)), (8771/18014398509481984), by norm_num⟩
  | 3 => ⟨((1496371453951333/9007199254740992), (64401890727/140737488355328)), (21943/9007199254740992), by norm_num⟩
  | 2 => ⟨((2242144649012243/4503599627370496), (8232826077637/4503599627370496)), (21967/2251799813685248), by norm_num⟩
  | 1 => ⟨((2237321280069885/2251799813685248), (3080681282741/562949953421312)), (66021/2251799813685248), by norm_num⟩
  | 0 => ⟨((2222859695116351/2251799813685248), (3067443671337/281474976710656)), (66263/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2222859695116351/2251799813685248), (3067443671337/281474976710656)), (252773289207076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1097012044468535/1125899906842624), (12112083609947/562949953421312)), (264535/2251799813685248), by norm_num⟩
  | 2 => ⟨((1068344182392467/1125899906842624), (94410535238309/2251799813685248)), (16465/70368744177664), by norm_num⟩
  | 3 => ⟨((2023503062461943/2251799813685248), (44792146027109/562949953421312)), (522037/1125899906842624), by norm_num⟩
  | 4 => ⟨((1804096100182591/2251799813685248), (322007468369981/2251799813685248)), (2042591/2251799813685248), by norm_num⟩
  | 5 => ⟨((699678965656145/1125899906842624), (515971636897163/2251799813685248)), (3857147/2251799813685248), by norm_num⟩
  | 6 => ⟨((187847059001575/562949953421312), (641290578350811/2251799813685248)), (1640401/562949953421312), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-3183607725/268435456)), (1/268435456), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-279097919/268435456), (-4017265675/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-293291811469283/1125899906842624), (-538279624837373/2251799813685248)), (35629809/4503599627370496), by norm_num⟩
  | 1 => ⟨((387753281/1073741824), (1423290269/4294967296)), (97/8589934592), by norm_num⟩
  | 2 => ⟨((-537540187/2147483648), (-3946198549/17179869184)), (137/17179869184), by norm_num⟩
  | 3 => ⟨((3974340961/34359738368), (455882733/4294967296)), (129/34359738368), by norm_num⟩
  | 4 => ⟨((-86087601/2147483648), (-2527950649/68719476736)), (91/68719476736), by norm_num⟩
  | 5 => ⟨((3055174549/274877906944), (350448373/34359738368)), (103/274877906944), by norm_num⟩
  | 6 => ⟨((-2823580833/1099511627776), (-2591064551/1099511627776)), (97/1099511627776), by norm_num⟩
  | 7 => ⟨((559187741/1099511627776), (1026279479/2199023255552)), (39/2199023255552), by norm_num⟩
  | 8 => ⟨((-3100795249/35184372088832), (-1422725455/17592186044416)), (55/17592186044416), by norm_num⟩
  | 9 => ⟨((3820991083/281474976710656), (1753170023/140737488355328)), (69/140737488355328), by norm_num⟩
  | 10 => ⟨((-2118807357/1125899906842624), (-3888655547/2251799813685248)), (155/2251799813685248), by norm_num⟩
  | 11 => ⟨((534052853/2251799813685248), (1960298639/9007199254740992)), (79/9007199254740992), by norm_num⟩
  | 12 => ⟨((-3948557113/144115188075855872), (-1811700633/72057594037927936)), (37/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414717067/10141204801825835211973625643008), (-390638617251/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780358497918643/633825300114114700748351602688), (-1852360345349/316912650057057350374175801344)), (11571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118220603954797/2475880078570760549798248448), (-1041851663151/9903520314283042199192993792)), (13021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891415701358519/2475880078570760549798248448), (-4427397683859/2475880078570760549798248448)), (6919/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773081080809563/154742504910672534362390528), (-4426866702141/154742504910672534362390528)), (13841/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387831186252805/2417851639229258349412352), (-4149623297087/9671406556917033397649408)), (3245/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260337664378489/604462909807314587353088), (-1815178036097/302231454903657293676544)), (5681/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945153703459963/37778931862957161709568), (-2949135184173/37778931862957161709568)), (18471/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299424459664231/4722366482869645213696), (-69105885095/73786976294838206464)), (3465/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((406009384229763/147573952589676412928), (-6079812622917/590295810358705651712)), (4767/147573952589676412928), by norm_num⟩
  | 8 => ⟨((114169231574809/4611686018427387904), (-3798753674795/36893488147419103232)), (11925/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456572257597889/2305843009213693952), (-8544089567397/9223372036854775808)), (13427/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798765589175101/576460752303423488), (-8540205527941/1152921504606846976)), (13441/576460752303423488), by norm_num⟩
  | 5 => ⟨((37427367790673/4503599627370496), (-3734154263041/72057594037927936)), (23553/144115188075855872), by norm_num⟩
  | 4 => ⟨((374066408724467/9007199254740992), (-11193715766155/36028797018963968)), (553/562949953421312), by norm_num⟩
  | 3 => ⟨((373754506627213/2251799813685248), (-13976827555841/9007199254740992)), (44349/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119697042609693/2251799813685248), (-13953832207469/2251799813685248)), (44515/2251799813685248), by norm_num⟩
  | 1 => ⟨((279135818404233/281474976710656), (-10436595865033/562949953421312)), (4199/70368744177664), by norm_num⟩
  | 0 => ⟨((138372311949105/140737488355328), (-41515751565327/1125899906842624)), (17003/140737488355328), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((138372311949105/140737488355328), (-41515751565327/1125899906842624)), (64861298144292787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((135855530389523/140737488355328), (-40818054901585/562949953421312)), (69377/281474976710656), by norm_num⟩
  | 2 => ⟨((65201508324175/70368744177664), (-2462633873767/17592186044416)), (576007/1125899906842624), by norm_num⟩
  | 3 => ⟨((944556549758969/1125899906842624), (-292070477407495/1125899906842624)), (614343/562949953421312), by norm_num⟩
  | 4 => ⟨((179163775353325/281474976710656), (-245028071101031/562949953421312)), (674761/281474976710656), by norm_num⟩
  | 5 => ⟨((485726147075631/2251799813685248), (-1247717429066701/2251799813685248)), (11571071/2251799813685248), by norm_num⟩
  | 6 => ⟨((-293291811469283/1125899906842624), (-538279624837373/2251799813685248)), (35629809/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/268435456), (-4017265675/268435456)), (1/134217728), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-162011325/134217728), (-2331950509/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((128601031618737/4503599627370496), (1340736975989873/4503599627370496)), (6329/1099511627776), by norm_num⟩
  | 1 => ⟨((-49346775/1073741824), (-4115739669/8589934592)), (81/8589934592), by norm_num⟩
  | 2 => ⟨((158841141/4294967296), (6624027461/17179869184)), (33/4294967296), by norm_num⟩
  | 3 => ⟨((-340859939/17179869184), (-3553653643/17179869184)), (9/2147483648), by norm_num⟩
  | 4 => ⟨((548592909/68719476736), (5719384901/68719476736)), (59/34359738368), by norm_num⟩
  | 5 => ⟨((-706340981/274877906944), (-7363995917/274877906944)), (77/137438953472), by norm_num⟩
  | 6 => ⟨((189468659/274877906944), (3950631405/549755813888)), (21/137438953472), by norm_num⟩
  | 7 => ⟨((-697001241/4398046511104), (-1816655989/1099511627776)), (39/1099511627776), by norm_num⟩
  | 8 => ⟨((560890111/17592186044416), (5847590045/17592186044416)), (127/17592186044416), by norm_num⟩
  | 9 => ⟨((-401207915/70368744177664), (-2091407359/35184372088832)), (93/70368744177664), by norm_num⟩
  | 10 => ⟨((516575383/562949953421312), (2692792235/281474976710656)), (61/281474976710656), by norm_num⟩
  | 11 => ⟨((-604651641/4503599627370496), (-3151914119/2251799813685248)), (145/4503599627370496), by norm_num⟩
  | 12 => ⟨((648766183/36028797018963968), (6763746773/36028797018963968)), (79/18014398509481984), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (960787274243/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445026163091005/158456325028528675187087900672), (1138669760041/316912650057057350374175801344)), (5777/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945622194109067/19807040628566084398385987584), (2561727841513/39614081257132168796771975168)), (1625/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891112968394219/2475880078570760549798248448), (1360750055335/1237940039285380274899124224)), (6907/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886389383005265/77371252455336267181195264), (1360561225093/77371252455336267181195264)), (1727/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387760442265987/2417851639229258349412352), (39853922973/151115727451828646838272)), (3239/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260090504462315/604462909807314587353088), (2231418501865/604462909807314587353088)), (5669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889906604331119/75557863725914323419136), (453162866745/9444732965739290427392)), (9215/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299124585667497/4722366482869645213696), (339789896871/590295810358705651712)), (13827/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623626392529371/590295810358705651712), (3736619742231/590295810358705651712)), (9509/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913097773636441/36893488147419103232), (1167292821757/18446744073709551616)), (11891/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456428822105861/2305843009213693952), (5250613513977/9223372036854775808)), (1673/576460752303423488), by norm_num⟩
  | 6 => ⟨((1596960478635511/1152921504606846976), (5247859001947/1152921504606846976)), (26785/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598589913165263/72057594037927936), (4588778788297/144115188075855872)), (23457/144115188075855872), by norm_num⟩
  | 4 => ⟨((373882137714475/9007199254740992), (3438487488157/18014398509481984)), (35223/36028797018963968), by norm_num⟩
  | 3 => ⟨((373527151590127/2251799813685248), (2146346543279/2251799813685248)), (689/140737488355328), by norm_num⟩
  | 2 => ⟨((559402744070213/1125899906842624), (2142287122537/562949953421312)), (22099/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115250477670793/1125899906842624), (12813167560095/1125899906842624)), (66549/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104570275434335/1125899906842624), (25464349007689/1125899906842624)), (67057/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104570275434335/1125899906842624), (25464349007689/1125899906842624)), (255802156688499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1083068799359219/1125899906842624), (49963878362965/1125899906842624)), (134607/562949953421312), by norm_num⟩
  | 2 => ⟨((1039649819571365/1125899906842624), (96126338444525/1125899906842624)), (33865/70368744177664), by norm_num⟩
  | 3 => ⟨((237949987356605/281474976710656), (177525070945539/1125899906842624)), (1093187/1125899906842624), by norm_num⟩
  | 4 => ⟨((776630309319441/1125899906842624), (150074045233493/562949953421312)), (1096513/562949953421312), by norm_num⟩
  | 5 => ⟨((911387873867811/2251799813685248), (828152140076863/2251799813685248)), (4194695/1125899906842624), by norm_num⟩
  | 6 => ⟨((128601031618737/4503599627370496), (1340736975989873/4503599627370496)), (6329/1099511627776), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-2331950509/134217728)), (1/134217728), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-90182207/67108864), (-5192240563/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((129354120881507/562949953421312), (-17375784069535/140737488355328)), (1702829/562949953421312), by norm_num⟩
  | 1 => ⟨((-1768275993/4294967296), (475055323/2147483648)), (49/8589934592), by norm_num⟩
  | 2 => ⟨((3168325255/8589934592), (-1702369747/8589934592)), (45/8589934592), by norm_num⟩
  | 3 => ⟨((-1892292259/8589934592), (1016745705/8589934592)), (7/2147483648), by norm_num⟩
  | 4 => ⟨((1695266287/17179869184), (-1821763745/34359738368)), (13/8589934592), by norm_num⟩
  | 5 => ⟨((-1215003769/34359738368), (2611329953/137438953472)), (77/137438953472), by norm_num⟩
  | 6 => ⟨((181416209/17179869184), (-1559625057/274877906944)), (3/17179869184), by norm_num⟩
  | 7 => ⟨((-2971924209/1099511627776), (798420847/549755813888)), (25/549755813888), by norm_num⟩
  | 8 => ⟨((166405417/274877906944), (-1430578113/4398046511104)), (23/2199023255552), by norm_num⟩
  | 9 => ⟨((-530059523/4398046511104), (569611529/8796093022208)), (75/35184372088832), by norm_num⟩
  | 10 => ⟨((3039165343/140737488355328), (-1632970961/140737488355328)), (55/140737488355328), by norm_num⟩
  | 11 => ⟨((-990082415/281474976710656), (531980215/281474976710656)), (73/1125899906842624), by norm_num⟩
  | 12 => ⟨((1182659695/2251799813685248), (-2541814901/9007199254740992)), (89/9007199254740992), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646016907/5070602400912917605986812821504), (-80281173167/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222487004599811/79228162514264337593543950336), (-380492733369/316912650057057350374175801344)), (11535/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891009867723531/39614081257132168796771975168), (-428003232261/19807040628566084398385987584)), (6489/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945432002321697/1237940039285380274899124224), (-909382150757/2475880078570760549798248448)), (13789/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772530043230657/154742504910672534362390528), (-909241872713/154742504910672534362390528)), (6895/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550808847402601/9671406556917033397649408), (-852265239527/9671406556917033397649408)), (12929/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259886953855729/604462909807314587353088), (-745583101383/604462909807314587353088)), (5657/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472394078525293/18889465931478580854784), (-1211293266219/75557863725914323419136)), (9193/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649438643677545/2361183241434822606848), (-454112827643/2361183241434822606848)), (13791/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202910879802625/73786976294838206464), (-624206714391/295147905179352825856)), (18965/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912886187781943/36893488147419103232), (-1559921744519/73786976294838206464)), (23709/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825240622919693/9223372036854775808), (-1754094153189/9223372036854775808)), (26677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798243782405579/576460752303423488), (-219134056261/144115188075855872)), (26683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598383997548487/72057594037927936), (-766394872765/72057594037927936)), (23355/144115188075855872), by norm_num⟩
  | 4 => ⟨((747457367522903/18014398509481984), (-2296889239601/36028797018963968)), (8761/9007199254740992), by norm_num⟩
  | 3 => ⟨((186668525390913/1125899906842624), (-2867098948421/9007199254740992)), (43827/9007199254740992), by norm_num⟩
  | 2 => ⟨((2236110718327057/4503599627370496), (-2861088660953/2251799813685248)), (87721/4503599627370496), by norm_num⟩
  | 1 => ⟨((557075440289337/562949953421312), (-133644918167/35184372088832)), (131751/2251799813685248), by norm_num⟩
  | 0 => ⟨((1102472932160671/1125899906842624), (-4246736323315/562949953421312)), (264187/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1102472932160671/1125899906842624), (-4246736323315/562949953421312)), (1007793435103606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1079469337978399/1125899906842624), (-33266984519843/2251799813685248)), (521367/2251799813685248), by norm_num⟩
  | 2 => ⟨((517353883542687/562949953421312), (-31895099677979/1125899906842624)), (1015139/2251799813685248), by norm_num⟩
  | 3 => ⟨((949998183126983/1125899906842624), (-58623519139131/1125899906842624)), (240419/281474976710656), by norm_num⟩
  | 4 => ⟨((399262769933767/562949953421312), (-197858571022935/2251799813685248)), (3446017/2251799813685248), by norm_num⟩
  | 5 => ⟨((557648180333927/1125899906842624), (-140327857994567/1125899906842624)), (5493641/2251799813685248), by norm_num⟩
  | 6 => ⟨((129354120881507/562949953421312), (-17375784069535/140737488355328)), (1702829/562949953421312), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-90182207/67108864), (-5192240563/268435456)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-391763459/268435456), (-5638945283/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-579055139268537/4503599627370496), (-871689349717501/4503599627370496)), (23333277/4503599627370496), by norm_num⟩
  | 1 => ⟨((1074589989/4294967296), (3235300355/8589934592)), (11/1073741824), by norm_num⟩
  | 2 => ⟨((-1045527783/4294967296), (-1573900949/4294967296)), (87/8589934592), by norm_num⟩
  | 3 => ⟨((169541927/1073741824), (2041779887/8589934592)), (115/17179869184), by norm_num⟩
  | 4 => ⟨((-2639306851/34359738368), (-993280051/8589934592)), (57/17179869184), by norm_num⟩
  | 5 => ⟨((2054341595/68719476736), (3092533971/68719476736)), (45/34359738368), by norm_num⟩
  | 6 => ⟨((-2665042773/274877906944), (-250741385/17179869184)), (59/137438953472), by norm_num⟩
  | 7 => ⟨((2963390731/1099511627776), (4460984739/1099511627776)), (133/1099511627776), by norm_num⟩
  | 8 => ⟨((-2883246049/4398046511104), (-4340337739/4398046511104)), (131/4398046511104), by norm_num⟩
  | 9 => ⟨((2493572333/17592186044416), (1876868279/8796093022208)), (115/17592186044416), by norm_num⟩
  | 10 => ⟨((-485226771/17592186044416), (-1460886813/35184372088832)), (91/70368744177664), by norm_num⟩
  | 11 => ⟨((2746786031/562949953421312), (4134915601/562949953421312)), (131/562949953421312), by norm_num⟩
  | 12 => ⟨((-55677071/70368744177664), (-1341029039/1125899906842624)), (87/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693180315/10141204801825835211973625643008), (-1404965816549/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779712002784671/633825300114114700748351602688), (-1664392116267/316912650057057350374175801344)), (5783/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890802527835785/39614081257132168796771975168), (-3744386316209/39614081257132168796771975168)), (1627/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890643323097279/2475880078570760549798248448), (-3977816620059/2475880078570760549798248448)), (1729/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772308931124939/154742504910672534362390528), (-1988574274553/77371252455336267181195264)), (13835/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387650274387155/2417851639229258349412352), (-3727866983589/9671406556917033397649408)), (6487/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314926178930021/151115727451828646838272), (-815293469769/151115727451828646838272)), (2839/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889279320743563/75557863725914323419136), (-5298076912423/75557863725914323419136)), (4615/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649326896755447/2361183241434822606848), (-3972393479131/4722366482869645213696)), (13851/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622978518504151/590295810358705651712), (-5460149398985/590295810358705651712)), (9527/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825384903527537/73786976294838206464), (-6822349644695/73786976294838206464)), (2979/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824802214166779/9223372036854775808), (-7671242899231/9223372036854775808)), (26831/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596046031762275/1152921504606846976), (-3833184093993/576460752303423488)), (3357/144115188075855872), by norm_num⟩
  | 5 => ⟨((1196378144471899/144115188075855872), (-6702589289977/144115188075855872)), (2941/18014398509481984), by norm_num⟩
  | 4 => ⟨((1494322954746753/36028797018963968), (-10042921135101/36028797018963968)), (8837/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492596251710327/9007199254740992), (-12534473182335/9007199254740992)), (44283/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117285131784887/2251799813685248), (-12505719222847/2251799813685248)), (2777/140737488355328), by norm_num⟩
  | 1 => ⟨((1112950070126743/1125899906842624), (-4671685282091/281474976710656)), (67019/1125899906842624), by norm_num⟩
  | 0 => ⟨((274972688529071/281474976710656), (-37086417055245/1125899906842624)), (16941/140737488355328), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274972688529071/281474976710656), (-37086417055245/1125899906842624)), (64624786913824037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((134157603766171/140737488355328), (-566088942699/8796093022208)), (68431/281474976710656), by norm_num⟩
  | 2 => ⟨((254604880970151/281474976710656), (-138143397764039/1125899906842624)), (278543/562949953421312), by norm_num⟩
  | 3 => ⟨((226062441716169/281474976710656), (-249911972677277/1125899906842624)), (1144517/1125899906842624), by norm_num⟩
  | 4 => ⟨((335381343491369/562949953421312), (-401426168803665/1125899906842624)), (4692985/2251799813685248), by norm_num⟩
  | 5 => ⟨((512975641072291/2251799813685248), (-956609709177529/2251799813685248)), (8938213/2251799813685248), by norm_num⟩
  | 6 => ⟨((-579055139268537/4503599627370496), (-871689349717501/4503599627370496)), (23333277/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-391763459/268435456), (-5638945283/268435456)), (1/134217728), by norm_num⟩, -3, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-418646879/268435456), (-6025898513/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-849578070179635/4503599627370496), (104457358902509/1125899906842624)), (5246339/1125899906842624), by norm_num⟩
  | 1 => ⟨((1684806759/4294967296), (-6473451/33554432)), (85/8589934592), by norm_num⟩
  | 2 => ⟨((-3503457165/8589934592), (1723028855/8589934592)), (91/8589934592), by norm_num⟩
  | 3 => ⟨((4856822913/17179869184), (-1194312593/8589934592)), (129/17179869184), by norm_num⟩
  | 4 => ⟨((-5049739663/34359738368), (620875805/8589934592)), (137/34359738368), by norm_num⟩
  | 5 => ⟨((1050063843/17179869184), (-1032859953/34359738368)), (29/17179869184), by norm_num⟩
  | 6 => ⟨((-2911395169/137438953472), (1431847929/137438953472)), (41/68719476736), by norm_num⟩
  | 7 => ⟨((1729736017/274877906944), (-1701396609/549755813888)), (25/137438953472), by norm_num⟩
  | 8 => ⟨((-1798442465/1099511627776), (884488697/1099511627776)), (53/1099511627776), by norm_num⟩
  | 9 => ⟨((3324227531/8796093022208), (-817441129/4398046511104)), (25/2199023255552), by norm_num⟩
  | 10 => ⟨((-2765014729/35184372088832), (2719713667/70368744177664)), (169/70368744177664), by norm_num⟩
  | 11 => ⟨((4181590175/281474976710656), (-2056540211/281474976710656)), (65/140737488355328), by norm_num⟩
  | 12 => ⟨((-90576795/35184372088832), (1425485049/1125899906842624)), (23/281474976710656), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238520483/10141204801825835211973625643008), (218555435903/633825300114114700748351602688)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779554224430651/633825300114114700748351602688), (258868847831/39614081257132168796771975168)), (11577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890624863948835/39614081257132168796771975168), (2329486914785/19807040628566084398385987584)), (13027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118153396540303/154742504910672534362390528), (1237342317855/618970019642690137449562112)), (13845/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772119715917087/154742504910672534362390528), (4948479957227/154742504910672534362390528)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775211728442121/4835703278458516698824704), (4638255068877/9671406556917033397649408)), (12989/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259549028895395/604462909807314587353088), (4057528300071/604462909807314587353088)), (11369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889025858919859/75557863725914323419136), (3295855920293/37778931862957161709568)), (4621/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324615821399719/1180591620717411303424), (1235558425595/1180591620717411303424)), (6935/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622715902017423/590295810358705651712), (6793052326767/590295810358705651712)), (19083/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912527815948867/36893488147419103232), (8487536933393/73786976294838206464)), (373/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1824430409031047/9223372036854775808), (4771641862247/4611686018427387904)), (105/36028797018963968), by norm_num⟩
  | 6 => ⟨((797836255606821/576460752303423488), (9536789689209/1152921504606846976)), (841/36028797018963968), by norm_num⟩
  | 5 => ⟨((598024693984809/72057594037927936), (8337385364147/144115188075855872)), (23583/144115188075855872), by norm_num⟩
  | 4 => ⟨((373456494371841/9007199254740992), (12491467283251/36028797018963968)), (8861/9007199254740992), by norm_num⟩
  | 3 => ⟨((186496040899897/1125899906842624), (15588766384485/9007199254740992)), (11107/2251799813685248), by norm_num⟩
  | 2 => ⟨((1116647195732611/2251799813685248), (15550417210305/2251799813685248)), (22307/1125899906842624), by norm_num⟩
  | 1 => ⟨((17374504485499/17592186044416), (11614881039589/562949953421312)), (67383/1125899906842624), by norm_num⟩
  | 0 => ⟨((274457142540981/281474976710656), (46076130638999/1125899906842624)), (8539/70368744177664), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((274457142540981/281474976710656), (46076130638999/1125899906842624)), (32573700219607331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((133571438315883/140737488355328), (89854688344279/1125899906842624)), (138809/562949953421312), by norm_num⟩
  | 2 => ⟨((1006991112312569/1125899906842624), (42639740490709/281474976710656)), (571277/1125899906842624), by norm_num⟩
  | 3 => ⟨((109350388829495/140737488355328), (152545850459725/562949953421312)), (1194969/1125899906842624), by norm_num⟩
  | 4 => ⟨((597033121970395/1125899906842624), (948202117689159/2251799813685248)), (2504553/1125899906842624), by norm_num⟩
  | 5 => ⟨((116952434165687/1125899906842624), (1005609943019611/2251799813685248)), (4765455/1125899906842624), by norm_num⟩
  | 6 => ⟨((-849578070179635/4503599627370496), (104457358902509/1125899906842624)), (5246339/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-418646879/268435456), (-6025898513/268435456)), (1/134217728), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile024Terms0
