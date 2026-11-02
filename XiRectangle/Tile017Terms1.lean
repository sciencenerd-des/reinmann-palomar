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
namespace Reinmann.XiRectangle.Tile017Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/128))
  have he : value ((3/4), (987/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/33554432), (-18192044143/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-285848958309339/4503599627370496), (818224131153055/4503599627370496)), (9374303/9007199254740992), by norm_num⟩
  | 1 => ⟨((4791827061/34359738368), (-13716294637/34359738368)), (81/34359738368), by norm_num⟩
  | 2 => ⟨((-2632180047/17179869184), (15068889843/34359738368)), (91/34359738368), by norm_num⟩
  | 3 => ⟨((3855660461/34359738368), (-2759144593/8589934592)), (17/8589934592), by norm_num⟩
  | 4 => ⟨((-8471751927/137438953472), (757807539/4294967296)), (19/17179869184), by norm_num⟩
  | 5 => ⟨((7445736619/274877906944), (-10656469437/137438953472)), (17/34359738368), by norm_num⟩
  | 6 => ⟨((-2726659249/274877906944), (3902442759/137438953472)), (51/274877906944), by norm_num⟩
  | 7 => ⟨((6846951675/2199023255552), (-2449869469/274877906944)), (65/1099511627776), by norm_num⟩
  | 8 => ⟨((-3761072625/4398046511104), (10765826817/4398046511104)), (145/8796093022208), by norm_num⟩
  | 9 => ⟨((7345707741/35184372088832), (-21026612691/35184372088832)), (9/2199023255552), by norm_num⟩
  | 10 => ⟨((-3228033917/70368744177664), (18480076073/140737488355328)), (129/140737488355328), by norm_num⟩
  | 11 => ⟨((5158338515/562949953421312), (-14765409941/562949953421312)), (105/562949953421312), by norm_num⟩
  | 12 => ⟨((-7556018775/4503599627370496), (21628614411/4503599627370496)), (39/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (2483943034803/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779422482072311/633825300114114700748351602688), (2941687557903/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472619234946497/9903520314283042199192993792), (206806844567/2475880078570760549798248448)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890297536522837/2475880078570760549798248448), (3515124343565/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771963314089683/154742504910672534362390528), (1757229198969/77371252455336267181195264)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550277261669865/9671406556917033397649408), (3294097280387/9671406556917033397649408)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629710769684499/302231454903657293676544), (2881627764565/604462909807314587353088)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888819496649253/75557863725914323419136), (4681319063193/75557863725914323419136)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649154610313863/2361183241434822606848), (3509829237851/4722366482869645213696)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811252605137159/295147905179352825856), (1206032637867/147573952589676412928)), (4761/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228099248390651/9223372036854775808), (6027336994513/73786976294838206464)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824138421125325/9223372036854775808), (6776869370567/9223372036854775808)), (6703/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797691736387979/576460752303423488), (1693003835103/288230376151711744)), (1677/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195799792523849/144115188075855872), (1480013814935/36028797018963968)), (1469/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493458198285371/36028797018963968), (8869173118963/36028797018963968)), (4413/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491520149729513/9007199254740992), (11067389059963/9007199254740992)), (5527/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116216282266267/2251799813685248), (1379850324505/281474976710656)), (11087/2251799813685248), by norm_num⟩
  | 1 => ⟨((555682440846995/562949953421312), (2060855156013/140737488355328)), (16713/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096792448378305/1125899906842624), (32688853862681/1125899906842624)), (16877/562949953421312), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1096792448378305/1125899906842624), (32688853862681/1125899906842624)), (64380647899436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((266872105226317/281474976710656), (63687522922483/1125899906842624)), (67723/1125899906842624), by norm_num⟩
  | 2 => ⟨((504252385709423/562949953421312), (60383425615997/562949953421312)), (68041/562949953421312), by norm_num⟩
  | 3 => ⟨((111299551976761/140737488355328), (432699016871737/2251799813685248)), (545959/2251799813685248), by norm_num⟩
  | 4 => ⟨((1325159835186675/2251799813685248), (684383489877537/2251799813685248)), (1073343/2251799813685248), by norm_num⟩
  | 5 => ⟨((571839388097137/2251799813685248), (805504563184377/2251799813685248)), (1915739/2251799813685248), by norm_num⟩
  | 6 => ⟨((-285848958309339/4503599627370496), (818224131153055/4503599627370496)), (9374303/9007199254740992), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-18192044143/1073741824)), (1/536870912), by norm_num⟩, -3, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-927143219/536870912), (-19064382443/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((45901719336059/562949953421312), (88964544070441/562949953421312)), (3336295/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1612741313/8589934592), (-6251478057/17179869184)), (61/34359738368), by norm_num⟩
  | 2 => ⟨((1856737053/8589934592), (14394560183/34359738368)), (9/4294967296), by norm_num⟩
  | 3 => ⟨((-5700393413/34359738368), (-22096466465/68719476736)), (113/68719476736), by norm_num⟩
  | 4 => ⟨((205088139/2147483648), (3179937143/17179869184)), (67/68719476736), by norm_num⟩
  | 5 => ⟨((-6044581013/137438953472), (-11715321379/137438953472)), (1/2147483648), by norm_num⟩
  | 6 => ⟨((2319693689/137438953472), (17983682911/549755813888)), (25/137438953472), by norm_num⟩
  | 7 => ⟨((-3052166919/549755813888), (-5915565741/549755813888)), (17/274877906944), by norm_num⟩
  | 8 => ⟨((7027874049/4398046511104), (3405273373/1099511627776)), (5/274877906944), by norm_num⟩
  | 9 => ⟨((-7192123565/17592186044416), (-435607317/549755813888)), (21/4398046511104), by norm_num⟩
  | 10 => ⟨((6624190603/70368744177664), (6419346653/35184372088832)), (79/70368744177664), by norm_num⟩
  | 11 => ⟨((-173326847/8796093022208), (-10749885025/281474976710656)), (135/562949953421312), by norm_num⟩
  | 12 => ⟨((1064266171/281474976710656), (4125420835/562949953421312)), (53/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239623/5070602400912917605986812821504), (178208049861/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779303690355773/633825300114114700748351602688), (1688167811191/633825300114114700748351602688)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945171749355387/19807040628566084398385987584), (237362347751/4951760157141521099596496896)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945078004436695/1237940039285380274899124224), (252153045447/309485009821345068724781056)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((110738879466731/9671406556917033397649408), (2016824419897/154742504910672534362390528)), (863/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550145149410781/9671406556917033397649408), (945174025423/4835703278458516698824704)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157413280460111/75557863725914323419136), (826814905595/302231454903657293676544)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888632708075111/75557863725914323419136), (671588075223/18889465931478580854784)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649084812455295/2361183241434822606848), (2014067833747/4722366482869645213696)), (1727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811157035529567/295147905179352825856), (2768212070487/590295810358705651712)), (2375/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824556269333209/73786976294838206464), (3458569049389/73786976294838206464)), (5939/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455968161339401/2305843009213693952), (243034960383/576460752303423488)), (1671/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595119765224675/1152921504606846976), (1942823852701/576460752303423488)), (6687/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298892842856107/36028797018963968), (1698334338137/72057594037927936)), (5855/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493120203322173/36028797018963968), (636057907385/4503599627370496)), (8789/36028797018963968), by norm_num⟩
  | 3 => ⟨((745552874628935/4503599627370496), (6349148837395/9007199254740992)), (10999/9007199254740992), by norm_num⟩
  | 2 => ⟨((2231627959536229/4503599627370496), (12664064247357/4503599627370496)), (11017/2251799813685248), by norm_num⟩
  | 1 => ⟨((2221583053184707/2251799813685248), (9455356510653/1125899906842624)), (33145/2251799813685248), by norm_num⟩
  | 0 => ⟨((68485328576501/70368744177664), (2342568238449/140737488355328)), (66669/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((68485328576501/70368744177664), (2342568238449/140737488355328)), (254322060591887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2132250448877747/2251799813685248), (284983690909/8796093022208)), (131989/2251799813685248), by norm_num⟩
  | 2 => ⟨((504171085364435/562949953421312), (69082557600217/1125899906842624)), (258517/2251799813685248), by norm_num⟩
  | 3 => ⟨((898820159194733/1125899906842624), (15467373180057/140737488355328)), (247387/1125899906842624), by norm_num⟩
  | 4 => ⟨((1407880642391411/2251799813685248), (49391199837683/281474976710656)), (898723/2251799813685248), by norm_num⟩
  | 5 => ⟨((810907120763137/2251799813685248), (123522373051727/562949953421312)), (359803/562949953421312), by norm_num⟩
  | 6 => ⟨((45901719336059/562949953421312), (88964544070441/562949953421312)), (3336295/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-927143219/536870912), (-19064382443/1073741824)), (1/536870912), by norm_num⟩, -3, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1931040333/1073741824), (-2481688553/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1395883371688143/9007199254740992), (524674106794685/9007199254740992)), (983933/2251799813685248), by norm_num⟩
  | 1 => ⟨((-12768486551/34359738368), (-4799322359/34359738368)), (19/17179869184), by norm_num⟩
  | 2 => ⟨((15308746771/34359738368), (5754136199/34359738368)), (3/2147483648), by norm_num⟩
  | 3 => ⟨((-24472514343/68719476736), (-4599271997/34359738368)), (79/68719476736), by norm_num⟩
  | 4 => ⟨((7335315807/34359738368), (2757143145/34359738368)), (49/68719476736), by norm_num⟩
  | 5 => ⟨((-14071455279/137438953472), (-5289072411/137438953472)), (49/137438953472), by norm_num⟩
  | 6 => ⟨((22494584063/549755813888), (1056886811/68719476736)), (81/549755813888), by norm_num⟩
  | 7 => ⟨((-15411330511/1099511627776), (-5792694601/1099511627776)), (57/1099511627776), by norm_num⟩
  | 8 => ⟨((9238689145/2199023255552), (1736284375/1099511627776)), (35/2199023255552), by norm_num⟩
  | 9 => ⟨((-615372473/549755813888), (-7401649947/17592186044416)), (77/17592186044416), by norm_num⟩
  | 10 => ⟨((4721915981/17592186044416), (887419071/8796093022208)), (19/17592186044416), by norm_num⟩
  | 11 => ⟨((-8234661825/140737488355328), (-6190365077/281474976710656)), (17/70368744177664), by norm_num⟩
  | 12 => ⟨((6581952221/562949953421312), (1236987263/281474976710656)), (7/140737488355328), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (468334923915/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444798699311975/158456325028528675187087900672), (69312834513/79228162514264337593543950336)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472555272821867/9903520314283042199192993792), (77964621403/4951760157141521099596496896)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472506518682655/618970019642690137449562112), (165644428355/618970019642690137449562112)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771692276455803/154742504910672534362390528), (165610247853/38685626227668133590597632)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775011807171555/4835703278458516698824704), (620893201739/9671406556917033397649408)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((314800012043309/151115727451828646838272), (543136368171/604462909807314587353088)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944230208550021/37778931862957161709568), (441162236861/37778931862957161709568)), (4595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649020324322475/2361183241434822606848), (661505340495/4722366482869645213696)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622137121572155/590295810358705651712), (909183245663/590295810358705651712)), (1185/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912167835619705/36893488147419103232), (1135899469561/73786976294838206464)), (5925/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227953160144597/1152921504606846976), (319272617963/2305843009213693952)), (6667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594873410497849/1152921504606846976), (638047842109/576460752303423488)), (1667/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195356944850233/144115188075855872), (1115465620229/144115188075855872)), (1459/36028797018963968), by norm_num⟩
  | 4 => ⟨((746400413237163/18014398509481984), (1670964802419/36028797018963968)), (2189/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490710478115557/9007199254740992), (1042401474931/4503599627370496)), (10949/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230849225663349/4503599627370496), (4157919887905/4503599627370496)), (21909/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220444329086883/2251799813685248), (6207745661107/2251799813685248)), (16447/1125899906842624), by norm_num⟩
  | 0 => ⟨((136835606886419/140737488355328), (12299438530231/2251799813685248)), (32957/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((136835606886419/140737488355328), (12299438530231/2251799813685248)), (125720982078170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064301636083917/1125899906842624), (11958442312095/1125899906842624)), (64447/1125899906842624), by norm_num⟩
  | 2 => ⟨((251486602260347/281474976710656), (22608385772887/1125899906842624)), (246423/2251799813685248), by norm_num⟩
  | 3 => ⟨((1796637574280183/2251799813685248), (20199685908347/562949953421312)), (112559/562949953421312), by norm_num⟩
  | 4 => ⟨((1430579271196673/2251799813685248), (4029167520913/70368744177664)), (46923/140737488355328), by norm_num⟩
  | 5 => ⟨((450735724229855/1125899906842624), (163823970512937/2251799813685248)), (2079817/4503599627370496), by norm_num⟩
  | 6 => ⟨((1395883371688143/9007199254740992), (524674106794685/9007199254740992)), (983933/2251799813685248), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-2481688553/134217728)), (1/536870912), by norm_num⟩, -3, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2001111149/1073741824), (-642935125/33554432)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1329833119348297/9007199254740992), (-214020821778333/4503599627370496)), (1775507/4503599627370496), by norm_num⟩
  | 1 => ⟨((-25211419383/68719476736), (1014369513/8589934592)), (35/34359738368), by norm_num⟩
  | 2 => ⟨((15662005919/34359738368), (-630153387/4294967296)), (45/34359738368), by norm_num⟩
  | 3 => ⟨((-12972874219/34359738368), (2087829789/17179869184)), (77/68719476736), by norm_num⟩
  | 4 => ⟨((16118190707/68719476736), (-2594031063/34359738368)), (25/34359738368), by norm_num⟩
  | 5 => ⟨((-4005219927/34359738368), (5156740031/137438953472)), (13/34359738368), by norm_num⟩
  | 6 => ⟨((6635065087/137438953472), (-2135669599/137438953472)), (45/274877906944), by norm_num⟩
  | 7 => ⟨((-18842876979/1099511627776), (6065073815/1099511627776)), (33/549755813888), by norm_num⟩
  | 8 => ⟨((23411395153/4398046511104), (-7535571127/4398046511104)), (21/1099511627776), by norm_num⟩
  | 9 => ⟨((-25855613999/17592186044416), (520144189/1099511627776)), (3/549755813888), by norm_num⟩
  | 10 => ⟨((1606219679/4398046511104), (-4136031213/35184372088832)), (49/35184372088832), by norm_num⟩
  | 11 => ⟨((-23222143775/281474976710656), (7474655611/281474976710656)), (91/281474976710656), by norm_num⟩
  | 12 => ⟨((19234953163/1125899906842624), (-6191273811/1125899906842624)), (77/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-405638410811/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444773549271345/158456325028528675187087900672), (-480219089033/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945053968332079/19807040628566084398385987584), (-540158185821/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889905873431689/2475880078570760549798248448), (-286904488175/1237940039285380274899124224)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885786051910499/77371252455336267181195264), (-573686283387/154742504910672534362390528)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549910982944321/9671406556917033397649408), (-134425141553/2417851639229258349412352)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((78693845383449/37778931862957161709568), (-470357712387/604462909807314587353088)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944150187916645/37778931862957161709568), (-764087089887/75557863725914323419136)), (4595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297920667587137/4722366482869645213696), (-572851736705/4722366482869645213696)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810986114325487/295147905179352825856), (-98415529265/73786976294838206464)), (1185/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912064838282573/36893488147419103232), (-491817612565/36893488147419103232)), (5925/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911696852030625/4611686018427387904), (-276468750887/2305843009213693952)), (3333/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398660510466629/288230376151711744), (-1104982424305/1152921504606846976)), (6667/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298788682894191/36028797018963968), (-482928216785/72057594037927936)), (5835/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492497974514513/36028797018963968), (-1446780682339/36028797018963968)), (4377/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490332730713907/9007199254740992), (-1804974318625/9007199254740992)), (10945/9007199254740992), by norm_num⟩
  | 2 => ⟨((557524044513313/1125899906842624), (-899866409743/1125899906842624)), (21901/4503599627370496), by norm_num⟩
  | 1 => ⟨((2219320856616671/2251799813685248), (-2686533212411/1125899906842624)), (16439/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093573523560233/1125899906842624), (-10642056257027/2251799813685248)), (32933/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1093573523560233/1125899906842624), (-10642056257027/2251799813685248)), (125629429343795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2124300270074995/2251799813685248), (-20673011673941/2251799813685248)), (128573/2251799813685248), by norm_num⟩
  | 2 => ⟨((1001915054039465/1125899906842624), (-39004963065829/2251799813685248)), (61237/562949953421312), by norm_num⟩
  | 3 => ⟨((1782491361135219/2251799813685248), (-69419420750285/2251799813685248)), (444435/2251799813685248), by norm_num⟩
  | 4 => ⟨((1408853654425171/2251799813685248), (-54951384679211/1125899906842624)), (182755/562949953421312), by norm_num⟩
  | 5 => ⟨((876094752688465/2251799813685248), (-68761404677735/1125899906842624)), (986093/2251799813685248), by norm_num⟩
  | 6 => ⟨((1329833119348297/9007199254740992), (-214020821778333/4503599627370496)), (1775507/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-642935125/33554432)), (1/536870912), by norm_num⟩, -3, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2065570051/1073741824), (-2654580261/134217728)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((787992590275893/9007199254740992), (-1053535914126461/9007199254740992)), (316117/562949953421312), by norm_num⟩
  | 1 => ⟨((-1927529419/8589934592), (1288540967/4294967296)), (51/34359738368), by norm_num⟩
  | 2 => ⟨((9888030689/34359738368), (-13220169301/34359738368)), (17/8589934592), by norm_num⟩
  | 3 => ⟨((-8454099321/34359738368), (11303021585/34359738368)), (15/8589934592), by norm_num⟩
  | 4 => ⟨((5421084155/34359738368), (-56624371/268435456)), (79/68719476736), by norm_num⟩
  | 5 => ⟨((-173810079/2147483648), (14872437147/137438953472)), (83/137438953472), by norm_num⟩
  | 6 => ⟨((9510699743/274877906944), (-12715682701/274877906944)), (73/274877906944), by norm_num⟩
  | 7 => ⟨((-6969846627/549755813888), (18637189813/1099511627776)), (109/1099511627776), by norm_num⟩
  | 8 => ⟨((4469325907/1099511627776), (-11950862009/2199023255552)), (9/274877906944), by norm_num⟩
  | 9 => ⟨((-5094930939/4398046511104), (6811856851/4398046511104)), (85/8796093022208), by norm_num⟩
  | 10 => ⟨((5227295935/17592186044416), (-6988827141/17592186044416)), (45/17592186044416), by norm_num⟩
  | 11 => ⟨((-2437772609/35184372088832), (407408811/4398046511104)), (43/70368744177664), by norm_num⟩
  | 12 => ⟨((2084254429/140737488355328), (-43540957/2199023255552)), (75/562949953421312), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418445/10141204801825835211973625643008), (-604807971785/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889500326054629/316912650057057350374175801344), (-1431874103443/633825300114114700748351602688)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890002660500455/39614081257132168796771975168), (-1610586126825/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236224245910821/309485009821345068724781056), (-1710911900117/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885730070615325/77371252455336267181195264), (-855267086709/77371252455336267181195264)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((12107859047547/75557863725914323419136), (-400806140485/2417851639229258349412352)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157376196187867/75557863725914323419136), (-1402420388659/604462909807314587353088)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1888150834131845/75557863725914323419136), (-569545330955/18889465931478580854784)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297808413261959/4722366482869645213696), (-213497302679/590295810358705651712)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621817719817417/590295810358705651712), (-73356320745/18446744073709551616)), (1187/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823936302156599/73786976294838206464), (-2932651584865/73786976294838206464)), (371/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1823175830646341/9223372036854775808), (-1648516353687/4611686018427387904)), (835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594423760267201/1152921504606846976), (-3294284378325/1152921504606846976)), (6683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194963277098885/144115188075855872), (-719852453967/36028797018963968)), (5851/144115188075855872), by norm_num⟩
  | 4 => ⟨((746104939729243/18014398509481984), (-4312943824519/36028797018963968)), (4391/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489971019877315/9007199254740992), (-1345099183483/2251799813685248)), (2747/2251799813685248), by norm_num⟩
  | 2 => ⟨((2229368005574309/4503599627370496), (-10728508346773/4503599627370496)), (11003/2251799813685248), by norm_num⟩
  | 1 => ⟨((138638550559303/140737488355328), (-16012273383845/2251799813685248)), (33089/2251799813685248), by norm_num⟩
  | 0 => ⟨((2184892322073139/2251799813685248), (-1981495563955/140737488355328)), (16625/562949953421312), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2184892322073139/2251799813685248), (-1981495563955/140737488355328)), (63419344188499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1059763237151987/1125899906842624), (-15380956753245/562949953421312)), (65461/1125899906842624), by norm_num⟩
  | 2 => ⟨((498335516628269/562949953421312), (-115819691752347/2251799813685248)), (126809/1125899906842624), by norm_num⟩
  | 3 => ⟨((1758592557413957/2251799813685248), (-205052209612449/2251799813685248)), (475107/2251799813685248), by norm_num⟩
  | 4 => ⟨((677369576945711/1125899906842624), (-160140029994755/1125899906842624)), (828619/2251799813685248), by norm_num⟩
  | 5 => ⟨((192372657610247/562949953421312), (-385377008063943/2251799813685248)), (1232751/2251799813685248), by norm_num⟩
  | 6 => ⟨((787992590275893/9007199254740992), (-1053535914126461/9007199254740992)), (316117/562949953421312), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2065570051/1073741824), (-2654580261/134217728)), (1/536870912), by norm_num⟩, -3, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2125249673/1073741824), (-21850223201/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((87969888130135/9007199254740992), (-310345905113339/2251799813685248)), (6111071/9007199254740992), by norm_num⟩
  | 1 => ⟨((-442805439/17179869184), (24994526233/68719476736)), (125/68719476736), by norm_num⟩
  | 2 => ⟨((1168588939/34359738368), (-8245248457/17179869184)), (21/8589934592), by norm_num⟩
  | 3 => ⟨((-2055982137/68719476736), (29012911167/68719476736)), (75/34359738368), by norm_num⟩
  | 4 => ⟨((678231841/34359738368), (-19141683967/68719476736)), (101/68719476736), by norm_num⟩
  | 5 => ⟨((-1431914169/137438953472), (10103200275/68719476736)), (27/34359738368), by norm_num⟩
  | 6 => ⟨((39363579/8589934592), (-17775283159/274877906944)), (97/274877906944), by norm_num⟩
  | 7 => ⟨((-949785067/549755813888), (13402854659/549755813888)), (149/1099511627776), by norm_num⟩
  | 8 => ⟨((1253268621/2199023255552), (-17685450913/2199023255552)), (25/549755813888), by norm_num⟩
  | 9 => ⟨((-1469976773/8796093022208), (20743519493/8796093022208)), (119/8796093022208), by norm_num⟩
  | 10 => ⟨((1551741191/35184372088832), (-1368583429/2199023255552)), (127/35184372088832), by norm_num⟩
  | 11 => ⟨((-1489139623/140737488355328), (21013935299/140737488355328)), (31/35184372088832), by norm_num⟩
  | 12 => ⟨((654987473/281474976710656), (-2310707499/70368744177664)), (111/562949953421312), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (-244247859339/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778913187111219/633825300114114700748351602688), (-1156400471879/316912650057057350374175801344)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944952089455885/19807040628566084398385987584), (-2601446662073/39614081257132168796771975168)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889689221220473/2475880078570760549798248448), (-21589676877/19342813113834066795298816)), (3455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221419409027631/19342813113834066795298816), (-1381425279069/77371252455336267181195264)), (27/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((1549707512850499/9671406556917033397649408), (-647376306183/2417851639229258349412352)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629461649741193/302231454903657293676544), (-2265150082265/604462909807314587353088)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888010400985851/75557863725914323419136), (-1839809334917/37778931862957161709568)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1297702874796471/4722366482869645213696), (-689655114099/1180591620717411303424)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621672257713509/590295810358705651712), (-3791326848507/590295810358705651712)), (1189/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911876977574073/36893488147419103232), (-4736495424743/73786976294838206464)), (5947/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822969977240131/9223372036854775808), (-2662448812283/4611686018427387904)), (6693/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594217017267789/1152921504606846976), (-1330081522071/288230376151711744)), (3349/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194781378494487/144115188075855872), (-2325073321187/72057594037927936)), (5865/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491935040364311/36028797018963968), (-6964953321009/36028797018963968)), (1101/4503599627370496), by norm_num⟩
  | 3 => ⟨((186202999924321/1125899906842624), (-8688249145363/9007199254740992)), (5513/4503599627370496), by norm_num⟩
  | 2 => ⟨((557165900373809/1125899906842624), (-17322767159165/4503599627370496)), (2763/562949953421312), by norm_num⟩
  | 1 => ⟨((554283618890243/562949953421312), (-25850159864555/2251799813685248)), (33285/2251799813685248), by norm_num⟩
  | 0 => ⟨((545656456238241/562949953421312), (-51166374785395/2251799813685248)), (33545/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((545656456238241/562949953421312), (-51166374785395/2251799813685248)), (127964024070357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1057207098274599/1125899906842624), (-99189146652479/2251799813685248)), (33277/562949953421312), by norm_num⟩
  | 2 => ⟨((247630189007261/281474976710656), (-93137470991423/1125899906842624)), (130851/1125899906842624), by norm_num⟩
  | 3 => ⟨((1727430251502097/2251799813685248), (-327754172890087/2251799813685248)), (62971/281474976710656), by norm_num⟩
  | 4 => ⟨((1277463679708705/2251799813685248), (-15714442894343/70368744177664)), (229891/562949953421312), by norm_num⟩
  | 5 => ⟨((612418155442919/2251799813685248), (-570555302044219/2251799813685248)), (1454059/2251799813685248), by norm_num⟩
  | 6 => ⟨((87969888130135/9007199254740992), (-310345905113339/2251799813685248)), (6111071/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-21850223201/1073741824)), (1/536870912), by norm_num⟩, -3, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-272601259/134217728), (-22421453551/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-262978761103993/4503599627370496), (-1058241082468743/9007199254740992)), (819477/1125899906842624), by norm_num⟩
  | 1 => ⟨((10866694441/68719476736), (2733011223/8589934592)), (137/68719476736), by norm_num⟩
  | 2 => ⟨((-1839222129/8589934592), (-925141449/2147483648)), (95/34359738368), by norm_num⟩
  | 3 => ⟨((3320470571/17179869184), (835109829/2147483648)), (11/4294967296), by norm_num⟩
  | 4 => ⟨((-8992000997/68719476736), (-18092154723/68719476736)), (61/34359738368), by norm_num⟩
  | 5 => ⟨((9740316043/137438953472), (9798892647/68719476736)), (67/68719476736), by norm_num⟩
  | 6 => ⟨((-4396210803/137438953472), (-17690595469/274877906944)), (123/274877906944), by norm_num⟩
  | 7 => ⟨((3401474157/274877906944), (855482511/34359738368)), (97/549755813888), by norm_num⟩
  | 8 => ⟨((-9211362775/2199023255552), (-18533516687/2199023255552)), (67/1099511627776), by norm_num⟩
  | 9 => ⟨((5543296181/4398046511104), (22306530485/8796093022208)), (41/2199023255552), by norm_num⟩
  | 10 => ⟨((-6004609735/17592186044416), (-12081440873/17592186044416)), (45/8796093022208), by norm_num⟩
  | 11 => ⟨((2956506291/35184372088832), (11897144867/70368744177664)), (45/35184372088832), by norm_num⟩
  | 12 => ⟨((-83399661/4398046511104), (-10739355183/281474976710656)), (165/562949953421312), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (-661742977107/2535301200456458802993406410752)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222353877432439/79228162514264337593543950336), (-1566389473357/316912650057057350374175801344)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889811621287565/39614081257132168796771975168), (-3523740868967/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236198840327573/309485009821345068724781056), (-3743197964055/2475880078570760549798248448)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771256598130519/154742504910672534362390528), (-935581082141/38685626227668133590597632)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549614819559553/9671406556917033397649408), (-3507501013573/9671406556917033397649408)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157355250833177/75557863725914323419136), (-3068135559673/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887877951362091/75557863725914323419136), (-4983981070121/75557863725914323419136)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297603232686997/4722366482869645213696), (-1868232225847/2361183241434822606848)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202691844366947/73786976294838206464), (-5135167291475/590295810358705651712)), (4763/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823581335359085/73786976294838206464), (-6415253634735/73786976294838206464)), (1489/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822774762289835/9223372036854775808), (-7212067766139/9223372036854775808)), (3353/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594020532639823/1152921504606846976), (-3602852871109/576460752303423488)), (6711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194608029397593/144115188075855872), (-6297840324311/144115188075855872)), (5879/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491672174962577/36028797018963968), (-9432468777955/36028797018963968)), (69/281474976710656), by norm_num⟩
  | 3 => ⟨((1489290463298815/9007199254740992), (-11765604038349/9007199254740992)), (11063/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227981741036369/4503599627370496), (-5864094123531/1125899906842624)), (5549/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108037487585145/1125899906842624), (-8749471384047/562949953421312)), (8367/562949953421312), by norm_num⟩
  | 0 => ⟨((2180361545517497/2251799813685248), (-135256743363/4398046511104)), (67641/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2180361545517497/2251799813685248), (-135256743363/4398046511104)), (258029946334075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((263632488366693/281474976710656), (-67054452756705/1125899906842624)), (135151/2251799813685248), by norm_num⟩
  | 2 => ⟨((491845285887807/562949953421312), (-7850490140767/70368744177664)), (269267/2251799813685248), by norm_num⟩
  | 3 => ⟨((1690860448926235/2251799813685248), (-109742659550561/562949953421312)), (265297/1125899906842624), by norm_num⟩
  | 4 => ⟨((592040602440523/1125899906842624), (-659239854151467/2251799813685248)), (501855/1125899906842624), by norm_num⟩
  | 5 => ⟨((859269201970127/4503599627370496), (-346653159870269/1125899906842624)), (3286545/4503599627370496), by norm_num⟩
  | 6 => ⟨((-262978761103993/4503599627370496), (-1058241082468743/9007199254740992)), (819477/1125899906842624), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-22421453551/1073741824)), (1/536870912), by norm_num⟩, -3, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile017Terms1
