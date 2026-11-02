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
namespace Reinmann.XiRectangle.Tile025Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7191/640))
  have he : value ((5/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-232581599/536870912), (-4181235703/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((96039876166345/2251799813685248), (-728474782697471/1125899906842624)), (14017331/2251799813685248), by norm_num⟩
  | 1 => ⟨((-507887035/17179869184), (3852388319/8589934592)), (77/17179869184), by norm_num⟩
  | 2 => ⟨((176020233/17179869184), (-1335136051/8589934592)), (55/34359738368), by norm_num⟩
  | 3 => ⟨((-325354475/137438953472), (4935710877/137438953472)), (53/137438953472), by norm_num⟩
  | 4 => ⟨((225518537/549755813888), (-6842348157/1099511627776)), (19/274877906944), by norm_num⟩
  | 5 => ⟨((-250108061/4398046511104), (3794203467/4398046511104)), (43/4398046511104), by norm_num⟩
  | 6 => ⟨((115574465/17592186044416), (-3506588581/35184372088832)), (41/35184372088832), by norm_num⟩
  | 7 => ⟨((-366217667/562949953421312), (2777807987/281474976710656)), (67/562949953421312), by norm_num⟩
  | 8 => ⟨((507685487/9007199254740992), (-3850859549/4503599627370496)), (95/9007199254740992), by norm_num⟩
  | 9 => ⟨((-312800679/72057594037927936), (4745266559/72057594037927936)), (15/18014398509481984), by norm_num⟩
  | 10 => ⟨((173453527/576460752303423488), (-5262669019/1152921504606846976)), (17/288230376151711744), by norm_num⟩
  | 11 => ⟨((-349756577/18446744073709551616), (331618563/1152921504606846976)), (35/9223372036854775808), by norm_num⟩
  | 12 => ⟨((161621857/147573952589676412928), (-4903690069/295147905179352825856)), (67/295147905179352825856), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583411453610655/10141204801825835211973625643008), (-1960395484497/10141204801825835211973625643008)), (4853/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55665624164537/19807040628566084398385987584), (-2326310894431/633825300114114700748351602688)), (5777/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473147253050295/9903520314283042199192993792), (-2616992902911/39614081257132168796771975168)), (1625/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892541502659427/2475880078570760549798248448), (-173776966145/154742504910672534362390528)), (1727/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((887103577710451/77371252455336267181195264), (-2780292488651/154742504910672534362390528)), (6909/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552380730190783/9671406556917033397649408), (-2606376523471/9671406556917033397649408)), (6479/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261261941461147/604462909807314587353088), (-570107935093/151115727451828646838272)), (5671/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472952475159911/18889465931478580854784), (-3705424537323/75557863725914323419136)), (9/73786976294838206464), by norm_num⟩
  | 10 => ⟨((650275902548765/2361183241434822606848), (-1389412961089/2361183241434822606848)), (3457/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812794204138733/295147905179352825856), (-3820491480227/590295810358705651712)), (4755/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57145232819235/2305843009213693952), (-4775022876219/73786976294838206464)), (2973/18446744073709551616), by norm_num⟩
  | 7 => ⟨((914236415371007/4611686018427387904), (-1342771771375/2305843009213693952)), (6693/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599716959633703/1152921504606846976), (-5370069462941/1152921504606846976)), (13395/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199590552250027/144115188075855872), (-2348832592811/72057594037927936)), (5865/72057594037927936), by norm_num⟩
  | 4 => ⟨((1499142247412837/36028797018963968), (-1761051167149/9007199254740992)), (17615/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498621535062581/9007199254740992), (-1100154822031/1125899906842624)), (5513/2251799813685248), by norm_num⟩
  | 2 => ⟨((1123312118039577/2251799813685248), (-4397602032241/1125899906842624)), (2763/281474976710656), by norm_num⟩
  | 1 => ⟨((560997318902171/562949953421312), (-3294422423173/281474976710656)), (8321/281474976710656), by norm_num⟩
  | 0 => ⟨((1117995231763999/1125899906842624), (-26294733455313/1125899906842624)), (67085/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1117995231763999/1125899906842624), (-26294733455313/1125899906842624)), (255908970359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1109531955414013/1125899906842624), (-13055062197307/281474976710656)), (68181/562949953421312), by norm_num⟩
  | 2 => ⟨((1090979933683331/1125899906842624), (-102922177005593/1125899906842624)), (281409/1125899906842624), by norm_num⟩
  | 3 => ⟨((261933639484927/281474976710656), (-99730028541339/562949953421312)), (149203/281474976710656), by norm_num⟩
  | 4 => ⟨((234915062853267/281474976710656), (-46403146821505/140737488355328)), (165277/140737488355328), by norm_num⟩
  | 5 => ⟨((661829042991283/1125899906842624), (-77454829410067/140737488355328)), (3078913/1125899906842624), by norm_num⟩
  | 6 => ⟨((96039876166345/2251799813685248), (-728474782697471/1125899906842624)), (14017331/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/536870912), (-4181235703/536870912)), (1/268435456), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-368633113/536870912), (-6627101795/536870912)), (3/536870912), by norm_num⟩
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
  | 0 => ⟨((69083717156561/140737488355328), (15624941467225/140737488355328)), (7872295/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1158084421/2147483648), (-1047714399/8589934592)), (35/8589934592), by norm_num⟩
  | 2 => ⟨((5089143105/17179869184), (575515957/8589934592)), (41/17179869184), by norm_num⟩
  | 3 => ⟨((-3727330103/34359738368), (-210756301/8589934592)), (1/1073741824), by norm_num⟩
  | 4 => ⟨((4094890655/137438953472), (926157849/137438953472)), (37/137438953472), by norm_num⟩
  | 5 => ⟨((-899739439/137438953472), (-813990715/549755813888)), (35/549755813888), by norm_num⟩
  | 6 => ⟨((2635906145/2199023255552), (1192346937/4398046511104)), (27/2199023255552), by norm_num⟩
  | 7 => ⟨((-413691269/2199023255552), (-748529713/17592186044416)), (71/35184372088832), by norm_num⟩
  | 8 => ⟨((3635890495/140737488355328), (822343941/140737488355328)), (41/140737488355328), by norm_num⟩
  | 9 => ⟨((-3550607981/1125899906842624), (-803055253/1125899906842624)), (21/562949953421312), by norm_num⟩
  | 10 => ⟨((6241186497/18014398509481984), (1411594191/18014398509481984)), (77/18014398509481984), by norm_num⟩
  | 11 => ⟨((-2493325157/72057594037927936), (-1127850709/144115188075855872)), (63/144115188075855872), by norm_num⟩
  | 12 => ⟨((3652263543/1152921504606846976), (826047099/1152921504606846976)), (3/72057594037927936), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583081351377037/10141204801825835211973625643008), (289741996799/10141204801825835211973625643008)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780911156120141/633825300114114700748351602688), (21480003385/39614081257132168796771975168)), (1081/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1892151787785267/39614081257132168796771975168), (96654038161/9903520314283042199192993792)), (9729/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892077187196043/2475880078570760549798248448), (51343858757/309485009821345068724781056)), (10337/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886871552421907/77371252455336267181195264), (410718482151/154742504910672534362390528)), (10337/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775972982090413/4835703278458516698824704), (385014168359/9671406556917033397649408)), (2423/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630440901284213/302231454903657293676544), (336852992585/604462909807314587353088)), (265/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((29549885975235/1180591620717411303424), (136830403107/18889465931478580854784)), (13781/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325022341971365/1180591620717411303424), (102608694927/1180591620717411303424)), (10337/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624953306817761/590295810358705651712), (564256139619/590295810358705651712)), (14213/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913927348835823/36893488147419103232), (705182678173/73786976294838206464)), (17767/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827582529561787/9223372036854775808), (793141499929/9223372036854775808)), (19989/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99926786847577/72057594037927936), (396452650169/576460752303423488)), (19991/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299703849998781/36028797018963968), (346763252457/72057594037927936)), (17495/144115188075855872), by norm_num⟩
  | 4 => ⟨((748991929901203/18014398509481984), (1039758720669/36028797018963968)), (13123/18014398509481984), by norm_num⟩
  | 3 => ⟨((374295285405437/2251799813685248), (1298769601767/9007199254740992)), (32815/9007199254740992), by norm_num⟩
  | 2 => ⟨((2243766201288493/4503599627370496), (1297377432913/2251799813685248)), (16413/1125899906842624), by norm_num⟩
  | 1 => ⟨((279969878707665/281474976710656), (3885178657597/2251799813685248)), (49267/1125899906842624), by norm_num⟩
  | 0 => ⟨((2227756752261779/2251799813685248), (1935646482109/562949953421312)), (12331/140737488355328), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2227756752261779/2251799813685248), (1935646482109/562949953421312)), (47039032519292787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((275492972857177/281474976710656), (15319832586549/2251799813685248)), (48967/281474976710656), by norm_num⟩
  | 2 => ⟨((2157000578473401/2251799813685248), (14994250189711/1125899906842624)), (96519/281474976710656), by norm_num⟩
  | 3 => ⟨((64556029763235/70368744177664), (28726004981811/1125899906842624)), (1499857/2251799813685248), by norm_num⟩
  | 4 => ⟨((1893685114866017/2251799813685248), (52706264812759/1125899906842624)), (1414231/1125899906842624), by norm_num⟩
  | 5 => ⟨((1587588510815449/2251799813685248), (88648261297049/1125899906842624)), (1255523/562949953421312), by norm_num⟩
  | 6 => ⟨((69083717156561/140737488355328), (15624941467225/140737488355328)), (7872295/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-368633113/536870912), (-6627101795/536870912)), (3/536870912), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-232581599/268435456), (-4181235703/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-1877145886100385/4503599627370496), (-248557185218345/4503599627370496)), (19466335/2251799813685248), by norm_num⟩
  | 1 => ⟨((4963449015/8589934592), (328610825/4294967296)), (105/8589934592), by norm_num⟩
  | 2 => ⟨((-3440400691/8589934592), (-911102667/17179869184)), (37/4294967296), by norm_num⟩
  | 3 => ⟨((6359210771/34359738368), (210509415/8589934592)), (139/34359738368), by norm_num⟩
  | 4 => ⟨((-4407869017/68719476736), (-291828015/34359738368)), (49/34359738368), by norm_num⟩
  | 5 => ⟨((4888483171/274877906944), (647295251/274877906944)), (111/274877906944), by norm_num⟩
  | 6 => ⟨((-2258958885/549755813888), (-299113919/549755813888)), (13/137438953472), by norm_num⟩
  | 7 => ⟨((7157901633/8796093022208), (947794147/8796093022208)), (167/8796093022208), by norm_num⟩
  | 8 => ⟨((-620184917/4398046511104), (-656960841/35184372088832)), (117/35184372088832), by norm_num⟩
  | 9 => ⟨((6113840735/281474976710656), (809547653/281474976710656)), (73/140737488355328), by norm_num⟩
  | 10 => ⟨((-6780466349/2251799813685248), (-897817077/2251799813685248)), (41/562949953421312), by norm_num⟩
  | 11 => ⟨((427260103/1125899906842624), (905191819/18014398509481984)), (167/18014398509481984), by norm_num⟩
  | 12 => ⟨((-6317954897/144115188075855872), (-209143719/36028797018963968)), (157/144115188075855872), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197855892514491/1267650600228229401496703205376), (-1960395484497/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780621923630049/633825300114114700748351602688), (-1162326075511/158456325028528675187087900672)), (11583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118239108487007/2475880078570760549798248448), (-5230027199061/39614081257132168796771975168)), (6517/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891729936274921/2475880078570760549798248448), (-5556408382845/2475880078570760549798248448)), (6927/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773394930836049/154742504910672534362390528), (-5555850629781/154742504910672534362390528)), (6929/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387904642634231/2417851639229258349412352), (-2604008559525/4835703278458516698824704)), (12997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260594352919553/604462909807314587353088), (-569552733757/75557863725914323419136)), (11377/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945361879740577/37778931862957161709568), (-7403072901291/75557863725914323419136)), (9249/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299736053727723/4722366482869645213696), (-5551330560561/4722366482869645213696)), (6941/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624464889746265/590295810358705651712), (-7631495538703/590295810358705651712)), (19101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913620131639003/36893488147419103232), (-4768495812049/36893488147419103232)), (2987/9223372036854775808), by norm_num⟩
  | 7 => ⟨((913442956918823/4611686018427387904), (-5362921569423/4611686018427387904)), (13455/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199765657209767/144115188075855872), (-5360874075195/576460752303423488)), (13473/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198192435976905/144115188075855872), (-9376916673071/144115188075855872)), (23617/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497034334192825/36028797018963968), (-14056133879353/36028797018963968)), (35503/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495967885108619/9007199254740992), (-8776980609353/4503599627370496)), (44517/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120630399503501/2251799813685248), (-17529583910907/2251799813685248)), (44725/2251799813685248), by norm_num⟩
  | 1 => ⟨((558951065315635/562949953421312), (-13116597536745/562949953421312)), (67605/1125899906842624), by norm_num⟩
  | 0 => ⟨((1109531955414013/1125899906842624), (-52220248789227/1125899906842624)), (137291/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1109531955414013/1125899906842624), (-52220248789227/1125899906842624)), (523723606589889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1090979933683331/1125899906842624), (-102922177005591/1125899906842624)), (283327/1125899906842624), by norm_num⟩
  | 2 => ⟨((261933639484927/281474976710656), (-99730028541337/562949953421312)), (37555/70368744177664), by norm_num⟩
  | 3 => ⟨((469830125706535/562949953421312), (-371225174572033/1125899906842624)), (332807/281474976710656), by norm_num⟩
  | 4 => ⟨((661829042991291/1125899906842624), (-309819317640263/562949953421312)), (3099899/1125899906842624), by norm_num⟩
  | 5 => ⟨((48019938083193/1125899906842624), (-182118695674367/281474976710656)), (7056437/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1877145886100385/4503599627370496), (-248557185218345/4503599627370496)), (19466335/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/268435456), (-4181235703/268435456)), (1/134217728), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-270018875/268435456), (-4854264325/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((4636675058681/17592186044416), (570918231645753/2251799813685248)), (11380139/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1821884919/4294967296), (-1752581495/4294967296)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((2932210661/8589934592), (2820671103/8589934592)), (15/2147483648), by norm_num⟩
  | 3 => ⟨((-1573070335/8589934592), (-3026463341/17179869184)), (33/8589934592), by norm_num⟩
  | 4 => ⟨((632939759/8589934592), (2435452421/34359738368)), (55/34359738368), by norm_num⟩
  | 5 => ⟨((-1629883591/68719476736), (-195985473/8589934592)), (73/137438953472), by norm_num⟩
  | 6 => ⟨((3497595259/549755813888), (1682274403/274877906944)), (5/34359738368), by norm_num⟩
  | 7 => ⟨((-804166059/549755813888), (-386788029/274877906944)), (19/549755813888), by norm_num⟩
  | 8 => ⟨((2588510687/8796093022208), (311255659/1099511627776)), (63/8796093022208), by norm_num⟩
  | 9 => ⟨((-3703153099/70368744177664), (-1781143673/35184372088832)), (23/17592186044416), by norm_num⟩
  | 10 => ⟨((2383997997/281474976710656), (573328031/70368744177664)), (61/281474976710656), by norm_num⟩
  | 11 => ⟨((-2790470371/2251799813685248), (-2684322529/2251799813685248)), (73/2251799813685248), by norm_num⟩
  | 12 => ⟨((1497029603/9007199254740992), (2880166965/18014398509481984)), (5/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197833183968175/1267650600228229401496703205376), (249454079773/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780417302961577/633825300114114700748351602688), (147868315399/79228162514264337593543950336)), (11541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891596204436739/39614081257132168796771975168), (665347323271/19807040628566084398385987584)), (1623/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1891486880326575/2475880078570760549798248448), (1413717856483/2475880078570760549798248448)), (13797/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110822049904971/9671406556917033397649408), (1413554520025/154742504910672534362390528)), (13797/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775696276256123/4835703278458516698824704), (662516919559/4835703278458516698824704)), (12937/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260397567918911/604462909807314587353088), (1159231110099/604462909807314587353088)), (11321/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118150363886699/4722366482869645213696), (1883425294625/75557863725914323419136)), (9199/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81218700542759/295147905179352825856), (1412284420667/4722366482869645213696)), (13801/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624141839541499/590295810358705651712), (1941428780867/590295810358705651712)), (18979/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826840366102071/73786976294838206464), (2426092698937/73786976294838206464)), (23729/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913220705080457/4611686018427387904), (2728401305095/9223372036854775808)), (26703/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597687474891815/1152921504606846976), (681802622699/288230376151711744)), (26711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299454232568669/36028797018963968), (596242520003/36028797018963968)), (11691/72057594037927936), by norm_num⟩
  | 4 => ⟨((748243083591297/18014398509481984), (3574778337357/36028797018963968)), (35093/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495309048419603/9007199254740992), (4463791737339/9007199254740992)), (43901/9007199254740992), by norm_num⟩
  | 2 => ⟨((2240022089156499/4503599627370496), (1114194082123/562949953421312)), (87907/4503599627370496), by norm_num⟩
  | 1 => ⟨((2234143070039519/2251799813685248), (13335296488847/2251799813685248)), (132123/2251799813685248), by norm_num⟩
  | 0 => ⟨((2216525804335499/2251799813685248), (3316341258381/281474976710656)), (66325/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2216525804335499/2251799813685248), (3316341258381/281474976710656)), (253009798290061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1090745885090003/1125899906842624), (52230262605121/2251799813685248)), (528541/2251799813685248), by norm_num⟩
  | 2 => ⟨((528041870565687/562949953421312), (25299737422249/562949953421312)), (262149/562949953421312), by norm_num⟩
  | 3 => ⟨((1976645623051887/2251799813685248), (189847365181565/2251799813685248)), (1030699/1125899906842624), by norm_num⟩
  | 4 => ⟨((107444217330549/140737488355328), (166649344739011/1125899906842624)), (3966609/2251799813685248), by norm_num⟩
  | 5 => ⟨((631548702681437/1125899906842624), (254452578675055/1125899906842624)), (903843/281474976710656), by norm_num⟩
  | 6 => ⟨((4636675058681/17592186044416), (570918231645753/2251799813685248)), (11380139/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-270018875/268435456), (-4854264325/268435456)), (1/134217728), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-75151839/67108864), (-5404168749/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((208896319412751/2251799813685248), (-352254667189903/1125899906842624)), (1645401/281474976710656), by norm_num⟩
  | 1 => ⟨((-713905255/4294967296), (2407667677/4294967296)), (23/2147483648), by norm_num⟩
  | 2 => ⟨((1279146501/8589934592), (-4313961359/8589934592)), (21/2147483648), by norm_num⟩
  | 3 => ⟨((-1527948571/17179869184), (5153054077/17179869184)), (51/8589934592), by norm_num⟩
  | 4 => ⟨((85553635/2147483648), (-4616516719/34359738368)), (93/34359738368), by norm_num⟩
  | 5 => ⟨((-245266457/17179869184), (6617350037/137438953472)), (135/137438953472), by norm_num⟩
  | 6 => ⟨((1171889325/274877906944), (-3952233197/274877906944)), (41/137438953472), by norm_num⟩
  | 7 => ⟨((-1199853597/1099511627776), (4046543575/1099511627776)), (43/549755813888), by norm_num⟩
  | 8 => ⟨((537462261/2199023255552), (-28322003/34359738368)), (79/4398046511104), by norm_num⟩
  | 9 => ⟨((-1712005503/35184372088832), (90215497/549755813888)), (1/274877906944), by norm_num⟩
  | 10 => ⟨((1227000829/140737488355328), (-2069049229/70368744177664)), (47/70368744177664), by norm_num⟩
  | 11 => ⟨((-399725519/281474976710656), (1348086745/281474976710656)), (31/281474976710656), by norm_num⟩
  | 12 => ⟨((1909898623/9007199254740992), (-6441192509/9007199254740992)), (75/4503599627370496), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582517037882311/10141204801825835211973625643008), (-835326743849/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780239999848795/633825300114114700748351602688), (-1980246952673/633825300114114700748351602688)), (5775/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945698338875577/19807040628566084398385987584), (-2227552816131/39614081257132168796771975168)), (3249/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472818701676861/618970019642690137449562112), (-1183252045737/1237940039285380274899124224)), (13809/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772940638819661/154742504910672534362390528), (-2366199492637/154742504910672534362390528)), (3453/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775596780725739/4835703278458516698824704), (-1108994209727/4835703278458516698824704)), (12951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157527919925573/75557863725914323419136), (-1940416297413/604462909807314587353088)), (5667/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890122562188483/75557863725914323419136), (-197035616579/4722366482869645213696)), (18421/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649643307004953/2361183241434822606848), (-1181948341583/2361183241434822606848)), (3455/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202981159851911/73786976294838206464), (-101546739589/18446744073709551616)), (19007/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913237150461691/36893488147419103232), (-2030288210483/36893488147419103232)), (2971/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1826029086454157/9223372036854775808), (-285398173445/576460752303423488)), (13375/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199659315805805/144115188075855872), (-4564149252331/1152921504606846976)), (26765/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197454898567175/144115188075855872), (-997783052073/36028797018963968)), (23437/144115188075855872), by norm_num⟩
  | 4 => ⟨((747970859258359/18014398509481984), (-747712950281/4503599627370496)), (8797/9007199254740992), by norm_num⟩
  | 3 => ⟨((747313020671811/4503599627370496), (-233387293991/281474976710656)), (44043/9007199254740992), by norm_num⟩
  | 2 => ⟨((139915547437833/281474976710656), (-7455298565345/2251799813685248)), (44131/2251799813685248), by norm_num⟩
  | 1 => ⟨((139504054016137/140737488355328), (-11150243314613/1125899906842624)), (66417/1125899906842624), by norm_num⟩
  | 0 => ⟨((1106148513137823/1125899906842624), (-5542466025519/281474976710656)), (133715/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1106148513137823/1125899906842624), (-5542466025519/281474976710656)), (510082249168014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1086307071178815/1125899906842624), (-43561886920747/1125899906842624)), (268005/1125899906842624), by norm_num⟩
  | 2 => ⟨((65401318522007/70368744177664), (-21015005644953/281474976710656)), (537901/1125899906842624), by norm_num⟩
  | 3 => ⟨((966276857190207/1125899906842624), (-78126110902721/562949953421312)), (270045/281474976710656), by norm_num⟩
  | 4 => ⟨((1615199010846607/2251799813685248), (-268199517377265/1125899906842624)), (4307785/2251799813685248), by norm_num⟩
  | 5 => ⟨((1030794969449585/2251799813685248), (-192377489572813/562949953421312)), (8232191/2251799813685248), by norm_num⟩
  | 6 => ⟨((208896319412751/2251799813685248), (-352254667189903/1125899906842624)), (1645401/281474976710656), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75151839/67108864), (-5404168749/268435456)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-326469549/268435456), (-5869106315/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-1323915778540659/4503599627370496), (-84539552269557/2251799813685248)), (27557437/4503599627370496), by norm_num⟩
  | 1 => ⟨((307109493/536870912), (313771005/4294967296)), (13/1073741824), by norm_num⟩
  | 2 => ⟨((-2390429917/4294967296), (-610570183/8589934592)), (103/8589934592), by norm_num⟩
  | 3 => ⟨((387630153/1073741824), (792076477/17179869184)), (135/17179869184), by norm_num⟩
  | 4 => ⟨((-3017173795/17179869184), (-192663707/8589934592)), (133/34359738368), by norm_num⟩
  | 5 => ⟨((4696919287/68719476736), (149962505/17179869184)), (105/68719476736), by norm_num⟩
  | 6 => ⟨((-3046594303/137438953472), (-778169495/274877906944)), (69/137438953472), by norm_num⟩
  | 7 => ⟨((6775312885/1099511627776), (865284525/1099511627776)), (39/274877906944), by norm_num⟩
  | 8 => ⟨((-6592075053/4398046511104), (-841882969/4398046511104)), (77/2199023255552), by norm_num⟩
  | 9 => ⟨((2850574611/8796093022208), (364050803/8796093022208)), (135/17592186044416), by norm_num⟩
  | 10 => ⟨((-4437569653/70368744177664), (-283364061/35184372088832)), (53/35184372088832), by norm_num⟩
  | 11 => ⟨((6280081327/562949953421312), (802037821/562949953421312)), (19/70368744177664), by norm_num⟩
  | 12 => ⟨((-2036745665/1125899906842624), (-520231179/2251799813685248)), (25/562949953421312), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791195769417651/5070602400912917605986812821504), (-1963406281643/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780081788291645/633825300114114700748351602688), (-4653762252369/633825300114114700748351602688)), (11583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891218149744117/39614081257132168796771975168), (-1308720535015/9903520314283042199192993792)), (13035/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891084443509215/2475880078570760549798248448), (-2780683972295/1237940039285380274899124224)), (13853/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772749514031859/154742504910672534362390528), (-5560586561111/154742504910672534362390528)), (6929/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551013573088571/9671406556917033397649408), (-651527440353/1208925819614629174706176)), (12997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78754066316639/37778931862957161709568), (-4559861526257/604462909807314587353088)), (5689/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889863812163405/75557863725914323419136), (-7408217309491/75557863725914323419136)), (9249/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299091226420355/4722366482869645213696), (-5554799643031/4722366482869645213696)), (6941/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811789234524287/295147905179352825856), (-3817816688467/295147905179352825856)), (19101/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456533140858531/18446744073709551616), (-4770608144591/36893488147419103232)), (2987/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1825640201024813/9223372036854775808), (-10729293855893/9223372036854775808)), (26911/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399220027146571/288230376151711744), (-2680893193941/288230376151711744)), (13473/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197103567221959/144115188075855872), (-9376685859755/144115188075855872)), (23617/144115188075855872), by norm_num⟩
  | 4 => ⟨((186925288841851/4503599627370496), (-14052137927629/36028797018963968)), (2219/2251799813685248), by norm_num⟩
  | 3 => ⟨((746965054649055/4503599627370496), (-8771295247805/4503599627370496)), (22259/4503599627370496), by norm_num⟩
  | 2 => ⟨((559298016020177/1125899906842624), (-17508672059743/2251799813685248)), (22363/1125899906842624), by norm_num⟩
  | 1 => ⟨((1114859198203149/1125899906842624), (-13089026814015/562949953421312)), (67609/1125899906842624), by norm_num⟩
  | 0 => ⟨((1103481149974585/1125899906842624), (-6501918501655/140737488355328)), (17163/140737488355328), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1103481149974585/1125899906842624), (-6501918501655/140737488355328)), (65471649706792787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1079105739805447/1125899906842624), (-101959251782763/1125899906842624)), (70457/281474976710656), by norm_num⟩
  | 2 => ⟨((512511592568359/562949953421312), (-24430416317733/140737488355328)), (295637/562949953421312), by norm_num⟩
  | 3 => ⟨((224814485830677/281474976710656), (-177932286847371/562949953421312)), (640937/562949953421312), by norm_num⟩
  | 4 => ⟨((605760112131689/1125899906842624), (-568459136904213/1125899906842624)), (2857997/1125899906842624), by norm_num⟩
  | 5 => ⟨((4862723903533/140737488355328), (-76461030954129/140737488355328)), (5961303/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1323915778540659/4503599627370496), (-84539552269557/2251799813685248)), (27557437/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-326469549/268435456), (-5869106315/268435456)), (1/134217728), by norm_num⟩, -3, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-348872399/268435456), (-3135926777/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-240881157450085/4503599627370496), (37623175069671/140737488355328)), (25682141/4503599627370496), by norm_num⟩
  | 1 => ⟨((238846915/2147483648), (-596887155/1073741824)), (13/1073741824), by norm_num⟩
  | 2 => ⟨((-496668197/4294967296), (620595973/1073741824)), (111/8589934592), by norm_num⟩
  | 3 => ⟨((688528321/8589934592), (-430164349/1073741824)), (157/17179869184), by norm_num⟩
  | 4 => ⟨((-1431754393/34359738368), (7156012937/34359738368)), (83/17179869184), by norm_num⟩
  | 5 => ⟨((1190899825/68719476736), (-2976102115/34359738368)), (35/17179869184), by norm_num⟩
  | 6 => ⟨((-103183607/17179869184), (1031438395/34359738368)), (99/137438953472), by norm_num⟩
  | 7 => ⟨((980865275/549755813888), (-1225609055/137438953472)), (15/68719476736), by norm_num⟩
  | 8 => ⟨((-63739125/137438953472), (2548582383/1099511627776)), (127/2199023255552), by norm_num⟩
  | 9 => ⟨((942519355/8796093022208), (-4710780515/8796093022208)), (15/1099511627776), by norm_num⟩
  | 10 => ⟨((-97995695/4398046511104), (3918317079/35184372088832)), (51/17592186044416), by norm_num⟩
  | 11 => ⟨((1185607675/281474976710656), (-5925753679/281474976710656)), (157/281474976710656), by norm_num⟩
  | 12 => ⟨((-821800617/1125899906842624), (64178429/17592186044416)), (111/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582282826618775/10141204801825835211973625643008), (2303363932821/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889980271164659/316912650057057350374175801344), (2729397855471/633825300114114700748351602688)), (11559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891082212111163/39614081257132168796771975168), (23986026751/309485009821345068724781056)), (6503/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((29545946703607/38685626227668133590597632), (3261666243717/2475880078570760549798248448)), (13821/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772606311036665/154742504910672534362390528), (3261178693207/154742504910672534362390528)), (13825/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775440006117131/4835703278458516698824704), (3056837042435/9671406556917033397649408)), (3241/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314987221748663/151115727451828646838272), (334276809327/75557863725914323419136)), (5673/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236209540699903/9444732965739290427392), (2172313741975/37778931862957161709568)), (9221/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298951745171189/4722366482869645213696), (1628810525461/2361183241434822606848)), (13837/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811694261721989/295147905179352825856), (4477848586083/590295810358705651712)), (9517/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912948945579927/36893488147419103232), (5595240508377/73786976294838206464)), (5951/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912689993098455/4611686018427387904), (3145899762321/4611686018427387904)), (26795/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798312314191283/576460752303423488), (6288242732943/1152921504606846976)), (419/18014398509481984), by norm_num⟩
  | 5 => ⟨((299221335498621/36028797018963968), (5498212057241/144115188075855872)), (23487/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495085596534667/36028797018963968), (8239320063315/36028797018963968)), (8819/9007199254740992), by norm_num⟩
  | 3 => ⟨((1493552771314857/9007199254740992), (2571289875953/2251799813685248)), (2761/562949953421312), by norm_num⟩
  | 2 => ⟨((559123226475429/1125899906842624), (10264185597691/2251799813685248)), (22149/1125899906842624), by norm_num⟩
  | 1 => ⟨((557201985098593/562949953421312), (7671942804387/562949953421312)), (66751/1125899906842624), by norm_num⟩
  | 0 => ⟨((551422857599603/562949953421312), (30478452955989/1125899906842624)), (134721/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((551422857599603/562949953421312), (30478452955989/1125899906842624)), (513919834617232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1079438525620675/1125899906842624), (59708737951093/1125899906842624)), (67805/281474976710656), by norm_num⟩
  | 2 => ⟨((1031727945039073/1125899906842624), (114489594801269/1125899906842624)), (548823/1125899906842624), by norm_num⟩
  | 3 => ⟨((466895271447849/562949953421312), (104913512875155/562949953421312)), (558727/562949953421312), by norm_num⟩
  | 4 => ⟨((735356129114547/1125899906842624), (87012393863249/281474976710656)), (1135039/562949953421312), by norm_num⟩
  | 5 => ⟨((186344330922825/562949953421312), (909282919341609/2251799813685248)), (136525/35184372088832), by norm_num⟩
  | 6 => ⟨((-240881157450085/4503599627370496), (37623175069671/140737488355328)), (25682141/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-348872399/268435456), (-3135926777/134217728)), (1/134217728), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile025Terms0
