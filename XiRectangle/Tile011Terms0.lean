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
namespace Reinmann.XiRectangle.Tile011Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3243/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3243/640))
  have he : value ((3/4), (3243/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-8931133415/17179869184), (-30170485069/8589934592)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1247973298869029/2251799813685248), (242534181404831/1125899906842624)), (450971/2251799813685248), by norm_num⟩
  | 1 => ⟨((52797190767/137438953472), (-10260735109/68719476736)), (21/137438953472), by norm_num⟩
  | 2 => ⟨((-73192447843/549755813888), (28448798445/549755813888)), (31/549755813888), by norm_num⟩
  | 3 => ⟨((67644185147/2199023255552), (-26292272577/2199023255552)), (31/2199023255552), by norm_num⟩
  | 4 => ⟨((-5860922027/1099511627776), (18224414607/8796093022208)), (23/8796093022208), by norm_num⟩
  | 5 => ⟨((51999764205/70368744177664), (-20211522563/70368744177664)), (7/17592186044416), by norm_num⟩
  | 6 => ⟨((-24028993299/281474976710656), (37358826345/1125899906842624)), (27/562949953421312), by norm_num⟩
  | 7 => ⟨((9517502261/1125899906842624), (-29594474457/9007199254740992)), (45/9007199254740992), by norm_num⟩
  | 8 => ⟨((-52776238865/72057594037927936), (10256663265/36028797018963968)), (33/72057594037927936), by norm_num⟩
  | 9 => ⟨((65034135413/1152921504606846976), (-12638892843/576460752303423488)), (43/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-72125164163/18446744073709551616), (14016980703/9223372036854775808)), (25/9223372036854775808), by norm_num⟩
  | 11 => ⟨((36358803045/147573952589676412928), (-14132117315/147573952589676412928)), (13/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-8400667273/590295810358705651712), (26121699393/4722366482869645213696)), (25/2361183241434822606848), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455347/5070602400912917605986812821504), (1804689359151/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781159168300357/633825300114114700748351602688), (2141236218473/316912650057057350374175801344)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((946215096989341/19807040628566084398385987584), (2408764402359/19807040628566084398385987584)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892372256503565/2475880078570760549798248448), (2559174727953/1237940039285380274899124224)), (109/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1774037344783193/154742504910672534362390528), (319877497583/9671406556917033397649408)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((776110466530369/4835703278458516698824704), (4797833407573/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((4926255935285/2361183241434822606848), (2098887465099/302231454903657293676544)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945790295478983/37778931862957161709568), (6820766300405/75557863725914323419136)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650189419843417/2361183241434822606848), (2557516744249/2361183241434822606848)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25396077870163/9223372036854775808), (7032290560837/590295810358705651712)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828345774584999/73786976294838206464), (8789040765081/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828130154015749/9223372036854775808), (4942924869351/4611686018427387904)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799685085184751/576460752303423488), (4941784590101/576460752303423488)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199282487813241/144115188075855872), (4322775847267/72057594037927936)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498670910046817/36028797018963968), (6481585302447/18014398509481984)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((749008103893893/4503599627370496), (16194906568553/9007199254740992)), (87/1125899906842624), by norm_num⟩
  | 2 => ⟨((1122682588862965/2251799813685248), (16181257537427/2251799813685248)), (699/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120989949786379/1125899906842624), (378711565041/17592186044416)), (1055/1125899906842624), by norm_num⟩
  | 0 => ⟨((557872472576447/562949953421312), (48336357832305/1125899906842624)), (1069/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557872472576447/562949953421312), (48336357832305/1125899906842624)), (4077913524436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((538870328197/549755813888), (47900392024843/562949953421312)), (2211/562949953421312), by norm_num⟩
  | 2 => ⟨((1073602866033155/1125899906842624), (187807745323459/1125899906842624)), (4711/562949953421312), by norm_num⟩
  | 3 => ⟨((992407369394431/1125899906842624), (1399095656291/4398046511104)), (21113/1125899906842624), by norm_num⟩
  | 4 => ⟨((760802728394205/1125899906842624), (315702172836365/562949953421312)), (50653/1125899906842624), by norm_num⟩
  | 5 => ⟨((320009518968437/2251799813685248), (853315904883393/1125899906842624)), (31317/281474976710656), by norm_num⟩
  | 6 => ⟨((-1247973298869029/2251799813685248), (242534181404831/1125899906842624)), (450971/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/17179869184), (-30170485069/8589934592)), (1/8589934592), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-55294967/67108864), (-47819087463/8589934592)), (3/17179869184), by norm_num⟩
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
  | 0 => ⟨((372532763257947/1125899906842624), (648625661138823/2251799813685248)), (154787/1125899906842624), by norm_num⟩
  | 1 => ⟨((-3122475217/8589934592), (-43492927373/137438953472)), (23/137438953472), by norm_num⟩
  | 2 => ⟨((54886234311/274877906944), (23890932241/137438953472)), (7/68719476736), by norm_num⟩
  | 3 => ⟨((-20099563831/274877906944), (-34995828997/549755813888)), (11/274877906944), by norm_num⟩
  | 4 => ⟨((44163255643/2199023255552), (9611711947/549755813888)), (13/1099511627776), by norm_num⟩
  | 5 => ⟨((-19407318143/4398046511104), (-527977243/137438953472)), (25/8796093022208), by norm_num⟩
  | 6 => ⟨((56856315205/70368744177664), (49496941849/70368744177664)), (39/70368744177664), by norm_num⟩
  | 7 => ⟨((-17846584735/140737488355328), (-62146226933/562949953421312)), (13/140737488355328), by norm_num⟩
  | 8 => ⟨((39212954601/2251799813685248), (34137304301/2251799813685248)), (31/2251799813685248), by norm_num⟩
  | 9 => ⟨((-598331025/281474976710656), (-33336588451/18014398509481984)), (1/562949953421312), by norm_num⟩
  | 10 => ⟨((16827745709/72057594037927936), (58598377175/288230376151711744)), (59/288230376151711744), by norm_num⟩
  | 11 => ⟨((-53780853023/2305843009213693952), (-11704890411/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 12 => ⟨((39389537351/18446744073709551616), (34291030515/18446744073709551616)), (39/18446744073709551616), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (233268714891/2535301200456458802993406410752)), (57/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1780698406500267/633825300114114700748351602688), (1106524802705/633825300114114700748351602688)), (271/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891912425251431/39614081257132168796771975168), (311186977319/9903520314283042199192993792)), (305/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472955710114991/618970019642690137449562112), (165304172031/309485009821345068724781056)), (81/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((13855380711477/1208925819614629174706176), (1322308200257/154742504910672534362390528)), (81/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775853730024539/4835703278458516698824704), (619765475409/4835703278458516698824704)), (19/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1260673082747253/604462909807314587353088), (271114152295/151115727451828646838272)), (267/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945426739453809/37778931862957161709568), (1761992695985/75557863725914323419136)), (27/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1299834903207155/4722366482869645213696), (330319104959/1180591620717411303424)), (81/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812301670740183/295147905179352825856), (1816400717593/590295810358705651712)), (223/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913708563238259/36893488147419103232), (141873091001/4611686018427387904)), (557/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827090104633579/9223372036854775808), (2552985066803/9223372036854775808)), (627/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598335968169765/1152921504606846976), (2552072092945/1152921504606846976)), (627/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599192067768283/72057594037927936), (2232036315915/144115188075855872)), (549/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497336522332409/36028797018963968), (3346001768369/36028797018963968)), (823/36028797018963968), by norm_num⟩
  | 3 => ⟨((748185599994469/4503599627370496), (4178911832449/9007199254740992)), (515/4503599627370496), by norm_num⟩
  | 2 => ⟨((560536003731099/1125899906842624), (4173529977789/2251799813685248)), (515/1125899906842624), by norm_num⟩
  | 1 => ⟨((1118660007173171/1125899906842624), (6246853319339/1125899906842624)), (387/281474976710656), by norm_num⟩
  | 0 => ⟨((2222855910190615/2251799813685248), (3110004488361/281474976710656)), (3107/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2222855910190615/2251799813685248), (3110004488361/281474976710656)), (11852268699264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1097004571911113/1125899906842624), (12280118002779/562949953421312)), (12407/2251799813685248), by norm_num⟩
  | 2 => ⟨((1068315059172807/1125899906842624), (95719667517759/2251799813685248)), (1545/140737488355328), by norm_num⟩
  | 3 => ⟨((2023281989892159/2251799813685248), (181648051743785/2251799813685248)), (24507/1125899906842624), by norm_num⟩
  | 4 => ⟨((1803301506306659/2251799813685248), (163213989697741/1125899906842624)), (23997/562949953421312), by norm_num⟩
  | 5 => ⟨((1396812042438199/2251799813685248), (261412254929155/1125899906842624)), (90785/1125899906842624), by norm_num⟩
  | 6 => ⟨((372532763257947/1125899906842624), (648625661138823/2251799813685248)), (154787/1125899906842624), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-47819087463/8589934592)), (3/17179869184), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-8931133415/8589934592), (-30170485069/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((1174301578724613/4503599627370496), (-1075321813659543/4503599627370496)), (338945/2251799813685248), by norm_num⟩
  | 1 => ⟨((-49680409449/137438953472), (45492937215/137438953472)), (31/137438953472), by norm_num⟩
  | 2 => ⟨((68871671477/274877906944), (-15766650583/68719476736)), (45/274877906944), by norm_num⟩
  | 3 => ⟨((-63650939873/549755813888), (7285739599/68719476736)), (11/137438953472), by norm_num⟩
  | 4 => ⟨((44119469513/1099511627776), (-40400718891/1099511627776)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((-48930057441/4398046511104), (44805831027/4398046511104)), (37/4398046511104), by norm_num⟩
  | 6 => ⟨((22610487573/8796093022208), (-41409380599/17592186044416)), (9/4398046511104), by norm_num⟩
  | 7 => ⟨((-35822618771/70368744177664), (65606389511/140737488355328)), (15/35184372088832), by norm_num⟩
  | 8 => ⟨((49660694403/562949953421312), (-11368720979/140737488355328)), (11/140737488355328), by norm_num⟩
  | 9 => ⟨((-1912342795/140737488355328), (56036955685/4503599627370496)), (7/562949953421312), by norm_num⟩
  | 10 => ⟨((67867392851/36028797018963968), (-485523223/281474976710656)), (1/562949953421312), by norm_num⟩
  | 11 => ⟨((-17106215275/72057594037927936), (62657452799/288230376151711744)), (67/288230376151711744), by norm_num⟩
  | 12 => ⟨((31618999701/1152921504606846976), (-57907782331/2305843009213693952)), (1/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414716005/10141204801825835211973625643008), (-965792947281/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((445091280098181/158456325028528675187087900672), (-572458942343/316912650057057350374175801344)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472884376823091/9903520314283042199192993792), (-643956261733/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236428065577067/309485009821345068724781056), (-1368261803487/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((886545227012201/77371252455336267181195264), (-171012301931/19342813113834066795298816)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387833529135507/2417851639229258349412352), (-1282418687659/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315086612099835/151115727451828646838272), (-560971400357/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945161387688931/37778931862957161709568), (-1822831697953/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((81214808948839/295147905179352825856), (-683419572147/2361183241434822606848)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624056256323839/590295810358705651712), (-1878941403899/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826733434838231/73786976294838206464), (-2347983305649/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826321178132887/9223372036854775808), (-1320264009333/4611686018427387904)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1597567324882873/1152921504606846976), (-1319668478531/576460752303423488)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((299427972809825/36028797018963968), (-2308080496069/144115188075855872)), (731/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496328792951909/36028797018963968), (-3459443568213/36028797018963968)), (1097/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495112652919831/9007199254740992), (-2159811395687/4503599627370496)), (1373/9007199254740992), by norm_num⟩
  | 2 => ⟨((559907565980209/1125899906842624), (-4312607062233/2251799813685248)), (687/1125899906842624), by norm_num⟩
  | 1 => ⟨((2233557742741193/2251799813685248), (-3225697481921/562949953421312)), (4129/2251799813685248), by norm_num⟩
  | 0 => ⟨((2215364768848449/2251799813685248), (-6416434719467/562949953421312)), (259/70368744177664), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2215364768848449/2251799813685248), (-6416434719467/562949953421312)), (988006860232331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((272403340379079/281474976710656), (-25250456692879/1125899906842624)), (8249/1125899906842624), by norm_num⟩
  | 2 => ⟨((1053930002853753/1125899906842624), (-97746646321717/2251799813685248)), (32673/2251799813685248), by norm_num⟩
  | 3 => ⟨((492219531444305/562949953421312), (-182996947793853/2251799813685248)), (32003/1125899906842624), by norm_num⟩
  | 4 => ⟨((426657952441695/562949953421312), (-160004759484217/1125899906842624)), (30583/562949953421312), by norm_num⟩
  | 5 => ⟨((1247973298869021/2251799813685248), (-485068362809655/2251799813685248)), (220201/2251799813685248), by norm_num⟩
  | 6 => ⟨((1174301578724613/4503599627370496), (-1075321813659543/4503599627370496)), (338945/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/8589934592), (-30170485069/4294967296)), (1/4294967296), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-5184362399/4294967296), (-70053696919/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-399759828444327/4503599627370496), (-1286198252419399/4503599627370496)), (449413/2251799813685248), by norm_num⟩
  | 1 => ⟨((19634662591/137438953472), (63173102733/137438953472)), (23/68719476736), by norm_num⟩
  | 2 => ⟨((-7900192593/68719476736), (-101673186585/274877906944)), (19/68719476736), by norm_num⟩
  | 3 => ⟨((4238289825/68719476736), (27272780195/137438953472)), (43/274877906944), by norm_num⟩
  | 4 => ⟨((-27285057313/1099511627776), (-87787692847/1099511627776)), (71/1099511627776), by norm_num⟩
  | 5 => ⟨((17565442273/2199023255552), (56515536445/2199023255552)), (47/2199023255552), by norm_num⟩
  | 6 => ⟨((-18846992495/8796093022208), (-60638831331/8796093022208)), (13/2199023255552), by norm_num⟩
  | 7 => ⟨((17333179575/35184372088832), (55768248063/35184372088832)), (49/35184372088832), by norm_num⟩
  | 8 => ⟨((-27896676351/281474976710656), (-89755532743/281474976710656)), (81/281474976710656), by norm_num⟩
  | 9 => ⟨((19954652689/1125899906842624), (32101323833/562949953421312)), (15/281474976710656), by norm_num⟩
  | 10 => ⟨((-12846309827/4503599627370496), (-41332070093/4503599627370496)), (79/9007199254740992), by norm_num⟩
  | 11 => ⟨((7518304753/18014398509481984), (96758400883/72057594037927936)), (95/72057594037927936), by norm_num⟩
  | 12 => ⟨((-16133659609/288230376151711744), (-6488609947/36028797018963968)), (13/72057594037927936), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791201706336853/5070602400912917605986812821504), (-2438669245503/10141204801825835211973625643008)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890051481028005/316912650057057350374175801344), (-361271297903/79228162514264337593543950336)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945621193477447/19807040628566084398385987584), (-3251084361563/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945555358670855/1237940039285380274899124224), (-431731337397/309485009821345068724781056)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772776374710215/154742504910672534362390528), (-1726685477221/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775519689130985/4835703278458516698824704), (-3237025560277/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260088263614901/604462909807314587353088), (-2831887677377/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889902683906927/75557863725914323419136), (-4600861857069/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81195087582209/295147905179352825856), (-1724905136317/2361183241434822606848)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101476351108613/36893488147419103232), (-4742130516345/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826188984756161/73786976294838206464), (-2962812692409/36893488147419103232)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912853544754675/4611686018427387904), (-6663526885055/9223372036854775808)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596951260674723/1152921504606846976), (-6660025167151/1152921504606846976)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((1197170615639935/144115188075855872), (-2911791551849/72057594037927936)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((373878112125609/9007199254740992), (-4363749057013/18014398509481984)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((1494084485521205/9007199254740992), (-10895591621629/9007199254740992)), (1383/9007199254740992), by norm_num⟩
  | 2 => ⟨((69923462142369/140737488355328), (-2718731496035/562949953421312)), (693/1125899906842624), by norm_num⟩
  | 1 => ⟨((557595230697089/562949953421312), (-2032593211529/140737488355328)), (2089/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104391083062463/1125899906842624), (-32315044553097/1125899906842624)), (2109/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104391083062463/1125899906842624), (-32315044553097/1125899906842624)), (8045198680686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((270591416438795/281474976710656), (-63395417010537/1125899906842624)), (4259/562949953421312), by norm_num⟩
  | 2 => ⟨((1036945156858339/1125899906842624), (-121888317640705/1125899906842624)), (17337/1125899906842624), by norm_num⟩
  | 3 => ⟨((235455765186173/281474976710656), (-224516406630819/1125899906842624)), (35689/1125899906842624), by norm_num⟩
  | 4 => ⟨((1486141096236943/2251799813685248), (-187809527290417/562949953421312)), (36971/562949953421312), by norm_num⟩
  | 5 => ⟨((365098320746503/1125899906842624), (-991603090380701/2251799813685248)), (293875/2251799813685248), by norm_num⟩
  | 6 => ⟨((-399759828444327/4503599627370496), (-1286198252419399/4503599627370496)), (449413/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/4294967296), (-70053696919/8589934592)), (1/4294967296), by norm_num⟩, -1, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-2885830621/2147483648), (-19497393133/2147483648)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1105293341698477/4503599627370496), (-24872314813489/281474976710656)), (399201/4503599627370496), by norm_num⟩
  | 1 => ⟨((30218808155/68719476736), (21760354291/137438953472)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((-13536208915/34359738368), (-19494660427/137438953472)), (23/137438953472), by norm_num⟩
  | 3 => ⟨((32338174001/137438953472), (11643247473/137438953472)), (29/274877906944), by norm_num⟩
  | 4 => ⟨((-14485557371/137438953472), (-651934341/17179869184)), (7/137438953472), by norm_num⟩
  | 5 => ⟨((83054830677/2199023255552), (29903603937/2199023255552)), (21/1099511627776), by norm_num⟩
  | 6 => ⟨((-49604759777/4398046511104), (-35720043679/8796093022208)), (13/2199023255552), by norm_num⟩
  | 7 => ⟨((12697114007/4398046511104), (4571551893/4398046511104)), (7/4398046511104), by norm_num⟩
  | 8 => ⟨((-11375087127/17592186044416), (-32764485573/140737488355328)), (13/35184372088832), by norm_num⟩
  | 9 => ⟨((72467271371/562949953421312), (13045794951/281474976710656)), (43/562949953421312), by norm_num⟩
  | 10 => ⟨((-51937567875/2251799813685248), (-9349970655/1125899906842624)), (1/70368744177664), by norm_num⟩
  | 11 => ⟨((67679730217/18014398509481984), (24367852303/18014398509481984)), (43/18014398509481984), by norm_num⟩
  | 12 => ⟨((-40421932497/72057594037927936), (-14553776703/72057594037927936)), (53/144115188075855872), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (-3642096806019/10141204801825835211973625643008)), (19/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779886401421523/633825300114114700748351602688), (-134857210509/19807040628566084398385987584)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890998463647463/39614081257132168796771975168), (-4854253790785/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472712794350765/618970019642690137449562112), (-5156934246867/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772516417099615/154742504910672534362390528), (-5156134872197/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550795224434923/9671406556917033397649408), (-1208256758125/2417851639229258349412352)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259874185684381/604462909807314587353088), (-528506144911/75557863725914323419136)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236194247065313/9444732965739290427392), (-6868986904267/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298859144372991/4722366482869645213696), (-5150346143451/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405814958743183/147573952589676412928), (-3539730154323/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825734988735839/73786976294838206464), (-4422963174243/36893488147419103232)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825193916250885/9223372036854775808), (-4973496263779/4611686018427387904)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199554382092965/144115188075855872), (-1242643482265/144115188075855872)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196715533188983/144115188075855872), (-8691927205541/144115188075855872)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494823030539889/36028797018963968), (-13024731703557/36028797018963968)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493210853969813/9007199254740992), (-4064468889035/2251799813685248)), (695/9007199254740992), by norm_num⟩
  | 2 => ⟨((279471008968059/562949953421312), (-8111647932113/1125899906842624)), (699/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113809322870321/1125899906842624), (-3031052708693/140737488355328)), (1055/1125899906842624), by norm_num⟩
  | 0 => ⟨((1101453699218797/1125899906842624), (-24075162277953/562949953421312)), (2139/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1101453699218797/1125899906842624), (-24075162277953/562949953421312)), (8159641746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1075479081585169/1125899906842624), (-94209712210415/1125899906842624)), (4369/1125899906842624), by norm_num⟩
  | 2 => ⟨((1019433235651687/1125899906842624), (-179981495954813/1125899906842624)), (9079/1125899906842624), by norm_num⟩
  | 3 => ⟨((447131568688313/562949953421312), (-325924387529579/1125899906842624)), (19345/1125899906842624), by norm_num⟩
  | 4 => ⟨((615933839473253/1125899906842624), (-517740810827683/1125899906842624)), (41931/1125899906842624), by norm_num⟩
  | 5 => ⟨((98871086794855/1125899906842624), (-1132939379520401/2251799813685248)), (168883/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1105293341698477/4503599627370496), (-24872314813489/281474976710656)), (399201/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-19497393133/2147483648)), (1/8589934592), by norm_num⟩, -1, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-12536430677/8589934592), (-84699259759/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-948806335158413/4503599627370496), (441490337258077/4503599627370496)), (722119/4503599627370496), by norm_num⟩
  | 1 => ⟨((7043044575/17179869184), (-3277208435/17179869184)), (11/34359738368), by norm_num⟩
  | 2 => ⟨((-54820527675/137438953472), (25508612617/137438953472)), (11/34359738368), by norm_num⟩
  | 3 => ⟨((71117214119/274877906944), (-33091645453/274877906944)), (59/274877906944), by norm_num⟩
  | 4 => ⟨((-69193854363/549755813888), (2012292773/34359738368)), (59/549755813888), by norm_num⟩
  | 5 => ⟨((53858009383/1099511627776), (-25060741951/1099511627776)), (47/1099511627776), by norm_num⟩
  | 6 => ⟨((-69868564711/4398046511104), (32510634737/4398046511104)), (63/4398046511104), by norm_num⟩
  | 7 => ⟨((77690256669/17592186044416), (-36150156621/17592186044416)), (71/17592186044416), by norm_num⟩
  | 8 => ⟨((-75589129467/70368744177664), (35172478329/70368744177664)), (71/70368744177664), by norm_num⟩
  | 9 => ⟨((65373179639/281474976710656), (-7604720283/70368744177664)), (63/281474976710656), by norm_num⟩
  | 10 => ⟨((-25442066747/562949953421312), (23676963807/1125899906842624)), (25/562949953421312), by norm_num⟩
  | 11 => ⟨((72011601303/9007199254740992), (-16753906971/4503599627370496)), (9/1125899906842624), by norm_num⟩
  | 12 => ⟨((-93418737217/72057594037927936), (43468796815/72057594037927936)), (3/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693181983/10141204801825835211973625643008), (3524970073187/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((55615893965339/19807040628566084398385987584), (521981774467/79228162514264337593543950336)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890798509731515/39614081257132168796771975168), (4697204848265/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890638803634719/2475880078570760549798248448), (4990034126087/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886152065136479/77371252455336267181195264), (4989194729683/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550596297908415/9671406556917033397649408), (292279885865/604462909807314587353088)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259700217344895/604462909807314587353088), (2045513243447/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944635725580979/37778931862957161709568), (1661561409203/18889465931478580854784)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649323700944921/2361183241434822606848), (622902601349/590295810358705651712)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622968935296985/590295810358705651712), (1712387611313/147573952589676412928)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912685866741083/36893488147419103232), (8558370598623/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912392880953211/4611686018427387904), (2405815335265/2305843009213693952)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798013768563111/576460752303423488), (4808564438429/576460752303423488)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((299089916882719/36028797018963968), (8408088085195/144115188075855872)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((186786332488847/4503599627370496), (12598331140231/36028797018963968)), (1109/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492547889070079/9007199254740992), (3930939654005/2251799813685248)), (1389/9007199254740992), by norm_num⟩
  | 2 => ⟨((279306204447475/562949953421312), (7843759334549/1125899906842624)), (349/562949953421312), by norm_num⟩
  | 1 => ⟨((1112829859974337/1125899906842624), (23440654500025/1125899906842624)), (2107/1125899906842624), by norm_num⟩
  | 0 => ⟨((274883053067399/281474976710656), (46518679586575/1125899906842624)), (267/70368744177664), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((274883053067399/281474976710656), (46518679586575/1125899906842624)), (1018524438357331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((33495625669455/35184372088832), (45429248520967/562949953421312)), (4349/562949953421312), by norm_num⟩
  | 2 => ⟨((1013081742086587/1125899906842624), (86497556304889/562949953421312)), (8983/562949953421312), by norm_num⟩
  | 3 => ⟨((442493733726545/562949953421312), (311321084565427/1125899906842624)), (18927/562949953421312), by norm_num⟩
  | 4 => ⟨((609540862099003/1125899906842624), (978826826505165/2251799813685248)), (80443/1125899906842624), by norm_num⟩
  | 5 => ⟨((234504990531641/2251799813685248), (1059836569925191/2251799813685248)), (39259/281474976710656), by norm_num⟩
  | 6 => ⟨((-948806335158413/4503599627370496), (441490337258077/4503599627370496)), (722119/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12536430677/8589934592), (-84699259759/8589934592)), (1/4294967296), by norm_num⟩, -2, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-13396700123/8589934592), (-11313931901/1073741824)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-419172440378049/4503599627370496), (848916250794733/4503599627370496)), (162933/1125899906842624), by norm_num⟩
  | 1 => ⟨((6650120435/34359738368), (-53871817545/137438953472)), (43/137438953472), by norm_num⟩
  | 2 => ⟨((-6914268345/34359738368), (56011647665/137438953472)), (47/137438953472), by norm_num⟩
  | 3 => ⟨((4792605609/34359738368), (-77648631315/274877906944)), (17/68719476736), by norm_num⟩
  | 4 => ⟨((-39863772785/549755813888), (40366447403/274877906944)), (73/549755813888), by norm_num⟩
  | 5 => ⟨((33157754055/1099511627776), (-4196983381/68719476736)), (63/1099511627776), by norm_num⟩
  | 6 => ⟨((-22983203737/2199023255552), (46546035159/2199023255552)), (23/1099511627776), by norm_num⟩
  | 7 => ⟨((27309844921/8796093022208), (-55308433777/8796093022208)), (57/8796093022208), by norm_num⟩
  | 8 => ⟨((-28394613013/35184372088832), (57505327401/35184372088832)), (61/35184372088832), by norm_num⟩
  | 9 => ⟨((6560548651/35184372088832), (-53146207407/140737488355328)), (29/70368744177664), by norm_num⟩
  | 10 => ⟨((-10913821921/281474976710656), (22102886293/281474976710656)), (99/1125899906842624), by norm_num⟩
  | 11 => ⟨((33010406809/4503599627370496), (-33426661781/2251799813685248)), (77/4503599627370496), by norm_num⟩
  | 12 => ⟨((-22881070409/18014398509481984), (23169596369/9007199254740992)), (55/18014398509481984), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521241/10141204801825835211973625643008), (1321792885435/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222444769074037/79228162514264337593543950336), (3131205590109/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890629510692629/39614081257132168796771975168), (1761055509737/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890459571122041/2475880078570760549798248448), (3741646338239/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886062633859333/77371252455336267181195264), (3740975178981/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550429007189009/9671406556917033397649408), (3506451198631/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259554230715877/604462909807314587353088), (3067431851481/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944517479462757/37778931862957161709568), (1245810040437/18889465931478580854784)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649235338186169/2361183241434822606848), (58379074663/73786976294838206464)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202840872870153/73786976294838206464), (5135458724785/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825070859719925/73786976294838206464), (6416474227147/73786976294838206464)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912224715548701/4611686018427387904), (3607308421689/4611686018427387904)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398923473390813/288230376151711744), (7209722455159/1152921504606846976)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((37377210890003/4503599627370496), (6303002943051/144115188075855872)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((1493863309255505/36028797018963968), (2360875241173/9007199254740992)), (1105/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492024226633219/9007199254740992), (11785131348189/9007199254740992)), (173/1125899906842624), by norm_num⟩
  | 2 => ⟨((1116716898216225/2251799813685248), (2939071616701/562949953421312)), (347/562949953421312), by norm_num⟩
  | 1 => ⟨((556053588452937/562949953421312), (2195299515051/140737488355328)), (523/281474976710656), by norm_num⟩
  | 0 => ⟨((1098242666074963/1125899906842624), (34837131301913/1125899906842624)), (1057/281474976710656), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1098242666074963/1125899906842624), (34837131301913/1125899906842624)), (4032136083507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((535093448603739/562949953421312), (67962744693191/1125899906842624)), (8511/1125899906842624), by norm_num⟩
  | 2 => ⟨((1013128301508759/1125899906842624), (129199475773785/1125899906842624)), (2151/140737488355328), by norm_num⟩
  | 3 => ⟨((896826125165441/1125899906842624), (116258687518315/562949953421312)), (4365/140737488355328), by norm_num⟩
  | 4 => ⟨((1332681110506923/2251799813685248), (46302441100763/140737488355328)), (35027/562949953421312), by norm_num⟩
  | 5 => ⟨((544984694269877/2251799813685248), (876900523754589/2251799813685248)), (16127/140737488355328), by norm_num⟩
  | 6 => ⟨((-419172440378049/4503599627370496), (848916250794733/4503599627370496)), (162933/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13396700123/8589934592), (-11313931901/1073741824)), (1/4294967296), by norm_num⟩, -2, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile011Terms0
