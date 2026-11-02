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
namespace Reinmann.XiRectangle.Tile022Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/128))
  have he : value ((3/4), (1269/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-279097919/536870912), (-922331405/134217728)), (3/1073741824), by norm_num⟩
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
  | 0 => ⟨((278380777380891/562949953421312), (-92937727580997/281474976710656)), (6146893/2251799813685248), by norm_num⟩
  | 1 => ⟨((-2944318405/8589934592), (491481963/2147483648)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((2040846001/17179869184), (-340669337/4294967296)), (27/34359738368), by norm_num⟩
  | 3 => ⟨((-943071101/34359738368), (2518762565/137438953472)), (27/137438953472), by norm_num⟩
  | 4 => ⟨((2614748299/549755813888), (-1745873171/549755813888)), (5/137438953472), by norm_num⟩
  | 5 => ⟨((-1449924329/2199023255552), (968117653/2199023255552)), (3/549755813888), by norm_num⟩
  | 6 => ⟨((2680029229/35184372088832), (-1789461391/35184372088832)), (3/4398046511104), by norm_num⟩
  | 7 => ⟨((-4246067895/562949953421312), (2835108841/562949953421312)), (5/70368744177664), by norm_num⟩
  | 8 => ⟨((1471574995/2251799813685248), (-491286925/1125899906842624)), (29/4503599627370496), by norm_num⟩
  | 9 => ⟨((-906682719/18014398509481984), (605394039/18014398509481984)), (37/72057594037927936), by norm_num⟩
  | 10 => ⟨((2011086625/576460752303423488), (-335701737/144115188075855872)), (43/1152921504606846976), by norm_num⟩
  | 11 => ⟨((-2027605853/9223372036854775808), (1353836873/9223372036854775808)), (23/9223372036854775808), by norm_num⟩
  | 12 => ⟨((1873905707/147573952589676412928), (-2502421897/295147905179352825856)), (45/295147905179352825856), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197912323863903/1267650600228229401496703205376), (-191718110111/2535301200456458802993406410752)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((890584247079043/316912650057057350374175801344), (-113735297165/79228162514264337593543950336)), (4327/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892441254231151/39614081257132168796771975168), (-1023569348601/39614081257132168796771975168)), (1217/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1892384698342881/2475880078570760549798248448), (-1087484685325/2475880078570760549798248448)), (5173/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774050563176299/154742504910672534362390528), (-1087419721861/154742504910672534362390528)), (5173/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388058537564859/2417851639229258349412352), (-1019386968717/9671406556917033397649408)), (2425/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630566954643581/302231454903657293676544), (-445947290323/302231454903657293676544)), (1061/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891602270662495/75557863725914323419136), (-1449199294245/75557863725914323419136)), (6897/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40637389126999/147573952589676412928), (-1086786253829/4722366482869645213696)), (2587/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625375398083751/590295810358705651712), (-747073567879/295147905179352825856)), (7115/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828382087591025/73786976294838206464), (-233425999943/9223372036854775808)), (4447/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1828175535087929/9223372036854775808), (-2100454649471/9223372036854775808)), (1251/1152921504606846976), by norm_num⟩
  | 6 => ⟨((799710605028783/576460752303423488), (-2099980522249/1152921504606846976)), (5005/576460752303423488), by norm_num⟩
  | 5 => ⟨((599666754979357/72057594037927936), (-918474823381/72057594037927936)), (4381/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498760159275823/36028797018963968), (-2754358057057/36028797018963968)), (3287/9007199254740992), by norm_num⟩
  | 3 => ⟨((187268750305425/1125899906842624), (-3441081814989/9007199254740992)), (8223/4503599627370496), by norm_num⟩
  | 2 => ⟨((561424846648183/1125899906842624), (-1719142056915/1125899906842624)), (4115/562949953421312), by norm_num⟩
  | 1 => ⟨((560661870383877/562949953421312), (-5150435185447/1125899906842624)), (3091/140737488355328), by norm_num⟩
  | 0 => ⟨((1116744220101063/1125899906842624), (-5136463021303/562949953421312)), (24803/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1116744220101063/1125899906842624), (-5136463021303/562949953421312)), (94615938426780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((553784627097389/562949953421312), (-5094693903021/281474976710656)), (6207/70368744177664), by norm_num⟩
  | 2 => ⟨((1089168185279491/1125899906842624), (-10023495502977/281474976710656)), (99493/562949953421312), by norm_num⟩
  | 3 => ⟨((1052207040103291/1125899906842624), (-77571886032037/1125899906842624)), (399161/1125899906842624), by norm_num⟩
  | 4 => ⟨((244498256694117/281474976710656), (-72494618838625/562949953421312)), (801073/1125899906842624), by norm_num⟩
  | 5 => ⟨((830845153904007/1125899906842624), (-125942335143835/562949953421312)), (3195989/2251799813685248), by norm_num⟩
  | 6 => ⟨((278380777380891/562949953421312), (-92937727580997/281474976710656)), (6146893/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/536870912), (-922331405/134217728)), (3/1073741824), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-55294967/67108864), (-5847442761/536870912)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-51208285550517/1125899906842624), (1965043239273931/4503599627370496)), (5011693/1125899906842624), by norm_num⟩
  | 1 => ⟨((429214873/8589934592), (-64337869/134217728)), (11/2147483648), by norm_num⟩
  | 2 => ⟨((-235770367/8589934592), (4523671905/17179869184)), (25/8589934592), by norm_num⟩
  | 3 => ⟨((690720593/68719476736), (-6626348727/68719476736)), (19/17179869184), by norm_num⟩
  | 4 => ⟨((-189708533/68719476736), (7279788141/274877906944)), (43/137438953472), by norm_num⟩
  | 5 => ⟨((333465801/549755813888), (-6398131769/1099511627776)), (39/549755813888), by norm_num⟩
  | 6 => ⟨((-488466169/4398046511104), (1171511031/1099511627776)), (59/4398046511104), by norm_num⟩
  | 7 => ⟨((306648535/17592186044416), (-183862345/1099511627776)), (19/8796093022208), by norm_num⟩
  | 8 => ⟨((-336887849/140737488355328), (6463789813/281474976710656)), (43/140737488355328), by norm_num⟩
  | 9 => ⟨((164492947/562949953421312), (-3156088409/1125899906842624)), (43/1125899906842624), by norm_num⟩
  | 10 => ⟨((-289142357/9007199254740992), (5547708017/18014398509481984)), (39/9007199254740992), by norm_num⟩
  | 11 => ⟨((115511035/36028797018963968), (-4432567419/144115188075855872)), (65/144115188075855872), by norm_num⟩
  | 12 => ⟨((-676809827/2305843009213693952), (6492897383/2305843009213693952)), (49/1152921504606846976), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (545357815565/2535301200456458802993406410752)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780695491672707/633825300114114700748351602688), (1293469528379/316912650057057350374175801344)), (5779/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472977242732483/9903520314283042199192993792), (1455042715589/19807040628566084398385987584)), (3251/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891818954785941/2475880078570760549798248448), (3091705035299/2475880078570760549798248448)), (3455/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773484603062341/154742504910672534362390528), (3091411682215/154742504910672534362390528)), (27/604462909807314587353088), by norm_num⟩
  | 13 => ⟨((1551703332629545/9671406556917033397649408), (724471687489/2417851639229258349412352)), (6481/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630334606957651/302231454903657293676544), (2535339187815/604462909807314587353088)), (5673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945423354849689/37778931862957161709568), (514917709209/9444732965739290427392)), (2305/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324957351098777/1180591620717411303424), (3088994777563/4722366482869645213696)), (6917/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406148773827271/147573952589676412928), (2123268301685/295147905179352825856)), (9515/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827405791316855/73786976294838206464), (5306923817849/73786976294838206464)), (11899/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827075940672457/9223372036854775808), (5968574574893/9223372036854775808)), (6697/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1598320040572117/1152921504606846976), (5966430901403/1152921504606846976)), (13403/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74898013531963/9007199254740992), (652276878947/18014398509481984)), (11739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497308683324343/36028797018963968), (7822497600637/36028797018963968)), (8815/18014398509481984), by norm_num⟩
  | 3 => ⟨((1496329480043381/9007199254740992), (1221209532051/1125899906842624)), (22075/9007199254740992), by norm_num⟩
  | 2 => ⟨((280254981252383/562949953421312), (9757003490423/2251799813685248)), (22133/2251799813685248), by norm_num⟩
  | 1 => ⟨((279639011164173/281474976710656), (14603808913891/1125899906842624)), (33343/1125899906842624), by norm_num⟩
  | 0 => ⟨((555558539572183/562949953421312), (29080747028073/1125899906842624)), (67261/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((555558539572183/562949953421312), (29080747028073/1125899906842624)), (256580357078170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((136972152921921/140737488355328), (57397845937801/1125899906842624)), (136231/1125899906842624), by norm_num⟩
  | 2 => ⟨((531767168321343/562949953421312), (27931102874779/281474976710656)), (34883/140737488355328), by norm_num⟩
  | 3 => ⟨((496768378030221/562949953421312), (105535800428053/562949953421312)), (582597/1125899906842624), by norm_num⟩
  | 4 => ⟨((837165061677989/1125899906842624), (372515162913807/1125899906842624)), (1246651/1125899906842624), by norm_num⟩
  | 5 => ⟨((1950099088785/4398046511104), (1107937490504879/2251799813685248)), (1339417/562949953421312), by norm_num⟩
  | 6 => ⟨((-51208285550517/1125899906842624), (1965043239273931/4503599627370496)), (5011693/1125899906842624), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-5847442761/536870912)), (1/268435456), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-279097919/268435456), (-922331405/67108864)), (3/536870912), by norm_num⟩
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
  | 0 => ⟨((610301816316047/4503599627370496), (-1470657301297813/4503599627370496)), (10221303/2251799813685248), by norm_num⟩
  | 1 => ⟨((-806863753/4294967296), (3888633583/8589934592)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1118550671/8589934592), (-5390790809/17179869184)), (5/1073741824), by norm_num⟩
  | 3 => ⟨((-2067520651/34359738368), (4982148601/34359738368)), (19/8589934592), by norm_num⟩
  | 4 => ⟨((716548055/34359738368), (-215835141/4294967296)), (27/34359738368), by norm_num⟩
  | 5 => ⟨((-1589354445/274877906944), (1914950649/137438953472)), (31/137438953472), by norm_num⟩
  | 6 => ⟨((1468875403/1099511627776), (-1769790191/549755813888)), (59/1099511627776), by norm_num⟩
  | 7 => ⟨((-2327192787/8796093022208), (5607886085/8796093022208)), (3/274877906944), by norm_num⟩
  | 8 => ⟨((1613087119/35184372088832), (-3887090429/35184372088832)), (17/8796093022208), by norm_num⟩
  | 9 => ⟨((-993872701/140737488355328), (4789912483/281474976710656)), (43/140737488355328), by norm_num⟩
  | 10 => ⟨((1102240097/1125899906842624), (-5312182933/2251799813685248)), (49/1125899906842624), by norm_num⟩
  | 11 => ⟨((-2222587973/18014398509481984), (5355817633/18014398509481984)), (101/18014398509481984), by norm_num⟩
  | 12 => ⟨((2054107449/144115188075855872), (-4949826523/144115188075855872)), (3/4503599627370496), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414717067/10141204801825835211973625643008), (-191718110111/1267650600228229401496703205376)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780364056112805/633825300114114700748351602688), (-909103731613/316912650057057350374175801344)), (8661/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891536246701743/39614081257132168796771975168), (-127830715655/2475880078570760549798248448)), (9745/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891423106649997/2475880078570760549798248448), (-2172891346977/2475880078570760549798248448)), (2589/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773088947674891/154742504910672534362390528), (-1086315847465/77371252455336267181195264)), (10357/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387833152615605/2417851639229258349412352), (-2036566358943/9671406556917033397649408)), (9711/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((19692891199007/9444732965739290427392), (-222714967177/75557863725914323419136)), (8499/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890320305541209/75557863725914323419136), (-2894777458661/75557863725914323419136)), (13813/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299434936976631/4722366482869645213696), (-542657669759/1180591620717411303424)), (5181/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624053247957079/590295810358705651712), (-2983882122541/590295810358705651712)), (3563/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826729299861795/73786976294838206464), (-3728750259559/73786976294838206464)), (4455/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826316011703527/9223372036854775808), (-4193328572723/9223372036854775808)), (20055/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798780757899605/576460752303423488), (-1047858679783/288230376151711744)), (10033/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197706086090801/144115188075855872), (-1832687729123/72057594037927936)), (17569/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496318642791835/36028797018963968), (-5493805006587/36028797018963968)), (26377/36028797018963968), by norm_num⟩
  | 3 => ⟨((373774361342097/2251799813685248), (-3429904090433/4503599627370496)), (33011/9007199254740992), by norm_num⟩
  | 2 => ⟨((279949038362863/562949953421312), (-214020110813/70368744177664)), (2067/140737488355328), by norm_num⟩
  | 1 => ⟨((139592625880457/140737488355328), (-640317495653/70368744177664)), (24879/562949953421312), by norm_num⟩
  | 0 => ⟨((1107569254194777/1125899906842624), (-5094693903021/281474976710656)), (100123/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1107569254194777/1125899906842624), (-5094693903021/281474976710656)), (381938938621139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1089168185279489/1125899906842624), (-10023495502977/281474976710656)), (200611/1125899906842624), by norm_num⟩
  | 2 => ⟨((1052207040103287/1125899906842624), (-77571886032037/1125899906842624)), (402421/1125899906842624), by norm_num⟩
  | 3 => ⟨((1955986053552921/2251799813685248), (-289978475354499/2251799813685248)), (1615231/2251799813685248), by norm_num⟩
  | 4 => ⟨((415422576951997/562949953421312), (-503769340575335/2251799813685248)), (805523/562949953421312), by norm_num⟩
  | 5 => ⟨((139190388690441/281474976710656), (-185875455161989/562949953421312)), (6197097/2251799813685248), by norm_num⟩
  | 6 => ⟨((610301816316047/4503599627370496), (-1470657301297813/4503599627370496)), (10221303/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/268435456), (-922331405/67108864)), (3/536870912), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-162011325/134217728), (-1070793601/67108864)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-1305648071014427/4503599627370496), (330752141000115/4503599627370496)), (14328621/4503599627370496), by norm_num⟩
  | 1 => ⟨((1002006295/2147483648), (-253832357/2147483648)), (23/4294967296), by norm_num⟩
  | 2 => ⟨((-6450667679/17179869184), (1634109675/17179869184)), (19/4294967296), by norm_num⟩
  | 3 => ⟨((865162427/4294967296), (-876666021/17179869184)), (21/8589934592), by norm_num⟩
  | 4 => ⟨((-2784850421/34359738368), (1410939531/68719476736)), (35/34359738368), by norm_num⟩
  | 5 => ⟨((1792817539/68719476736), (-908327829/137438953472)), (47/137438953472), by norm_num⟩
  | 6 => ⟨((-3847238023/549755813888), (974598163/549755813888)), (13/137438953472), by norm_num⟩
  | 7 => ⟨((884555819/549755813888), (-224079319/549755813888)), (49/2199023255552), by norm_num⟩
  | 8 => ⟨((-5694550683/17592186044416), (721283503/8796093022208)), (81/17592186044416), by norm_num⟩
  | 9 => ⟨((254584049/4398046511104), (-515938229/35184372088832)), (59/70368744177664), by norm_num⟩
  | 10 => ⟨((-5244636421/562949953421312), (664296437/281474976710656)), (39/281474976710656), by norm_num⟩
  | 11 => ⟨((767356063/562949953421312), (-777559179/2251799813685248)), (93/4503599627370496), by norm_num⟩
  | 12 => ⟨((-6586730347/36028797018963968), (1668577629/36028797018963968)), (51/18014398509481984), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (1884545503637/5070602400912917605986812821504)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222512096295427/79228162514264337593543950336), (4466909656153/633825300114114700748351602688)), (5791/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945617528108015/19807040628566084398385987584), (5024703611385/39614081257132168796771975168)), (1629/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891102471647529/2475880078570760549798248448), (5338086405035/2475880078570760549798248448)), (3463/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772767615287275/154742504910672534362390528), (5337342352835/154742504910672534362390528)), (433/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1551030620669983/9671406556917033397649408), (2501483884877/4835703278458516698824704)), (6497/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630040027658981/302231454903657293676544), (547100745707/75557863725914323419136)), (711/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889888323278743/75557863725914323419136), (7110826570891/75557863725914323419136)), (9247/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299109736953573/4722366482869645213696), (2665910942043/2361183241434822606848)), (6939/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811802063790511/295147905179352825856), (229035787077/18446744073709551616)), (2387/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228270618271133/9223372036854775808), (286195800293/2305843009213693952)), (1493/9223372036854775808), by norm_num⟩
  | 7 => ⟨((456419264211431/2305843009213693952), (2574673521113/2305843009213693952)), (6725/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596917495341315/1152921504606846976), (10293248208561/1152921504606846976)), (13467/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197136877079093/144115188075855872), (4500231094287/72057594037927936)), (11803/144115188075855872), by norm_num⟩
  | 4 => ⟨((747726733137963/18014398509481984), (13488424867159/36028797018963968)), (8871/18014398509481984), by norm_num⟩
  | 3 => ⟨((186749516591599/1125899906842624), (16839042478915/9007199254740992)), (22243/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118665164349637/2251799813685248), (16806772028963/2251799813685248)), (22343/2251799813685248), by norm_num⟩
  | 1 => ⟨((1114970635074625/1125899906842624), (6282337869123/281474976710656)), (33763/1125899906842624), by norm_num⟩
  | 0 => ⟨((551867387152955/562949953421312), (49934701674783/1125899906842624)), (34263/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((551867387152955/562949953421312), (49934701674783/1125899906842624)), (130702974559593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((539895673759347/562949953421312), (24475828778425/281474976710656)), (140433/1125899906842624), by norm_num⟩
  | 2 => ⟨((1027057812189355/1125899906842624), (187787834266063/1125899906842624)), (73447/281474976710656), by norm_num⟩
  | 3 => ⟨((452786021512373/562949953421312), (171302050071169/562949953421312)), (633995/1125899906842624), by norm_num⟩
  | 4 => ⟨((312054007378069/562949953421312), (551119496553823/1125899906842624)), (1405699/1125899906842624), by norm_num⟩
  | 5 => ⟨((152372540542537/2251799813685248), (152748078580171/281474976710656)), (5869141/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1305648071014427/4503599627370496), (330752141000115/4503599627370496)), (14328621/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-1070793601/67108864)), (1/268435456), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-90182207/67108864), (-2384192095/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((34220592525169/281474976710656), (64959561902831/281474976710656)), (19379135/4503599627370496), by norm_num⟩
  | 1 => ⟨((-467796865/2147483648), (-3551999211/8589934592)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((1676358925/8589934592), (3182164111/8589934592)), (63/8589934592), by norm_num⟩
  | 3 => ⟨((-2002421319/17179869184), (-3801115119/17179869184)), (77/17179869184), by norm_num⟩
  | 4 => ⟨((224241085/4294967296), (851335501/8589934592)), (35/17179869184), by norm_num⟩
  | 5 => ⟨((-160714435/8589934592), (-2440621513/68719476736)), (103/137438953472), by norm_num⟩
  | 6 => ⟨((1535795257/274877906944), (2915337805/274877906944)), (63/274877906944), by norm_num⟩
  | 7 => ⟨((-786221627/549755813888), (-1492452605/549755813888)), (33/549755813888), by norm_num⟩
  | 8 => ⟨((1408720045/4398046511104), (5348232175/8796093022208)), (15/1099511627776), by norm_num⟩
  | 9 => ⟨((-560908329/8796093022208), (-266187379/2199023255552)), (97/35184372088832), by norm_num⟩
  | 10 => ⟨((100501281/8796093022208), (763110011/35184372088832)), (71/140737488355328), by norm_num⟩
  | 11 => ⟨((-523851991/281474976710656), (-3977627893/1125899906842624)), (47/562949953421312), by norm_num⟩
  | 12 => ⟨((2502978041/9007199254740992), (1187825407/2251799813685248)), (57/4503599627370496), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646016907/5070602400912917605986812821504), (707279412121/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222486855739049/79228162514264337593543950336), (1676075885275/633825300114114700748351602688)), (5773/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236376057279347/4951760157141521099596496896), (471339760899/9903520314283042199192993792)), (12991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890862419250885/2475880078570760549798248448), (2002919140753/2475880078570760549798248448)), (3451/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886264179548885/77371252455336267181195264), (2002609991125/154742504910672534362390528)), (6903/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96925447728725/604462909807314587353088), (117319903009/604462909807314587353088)), (12945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259885375760821/604462909807314587353088), (1642150283141/604462909807314587353088)), (11329/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889573553263171/75557863725914323419136), (166742416471/4722366482869645213696)), (18413/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162359380618789/590295810358705651712), (2000370520917/4722366482869645213696)), (3453/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811641838085765/295147905179352825856), (687408669685/147573952589676412928)), (18997/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825767754676239/73786976294838206464), (1717865791061/36893488147419103232)), (23753/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825234850116649/9223372036854775808), (241462189089/576460752303423488)), (6683/2305843009213693952), by norm_num⟩
  | 6 => ⟨((399120268737919/288230376151711744), (482642785113/144115188075855872)), (26745/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196761510913649/144115188075855872), (1687983274009/72057594037927936)), (2927/18014398509481984), by norm_num⟩
  | 4 => ⟨((46715731265187/1125899906842624), (2529443699911/18014398509481984)), (2197/2251799813685248), by norm_num⟩
  | 3 => ⟨((1493331226783679/9007199254740992), (6314757822671/9007199254740992)), (43989/9007199254740992), by norm_num⟩
  | 2 => ⟨((279508545823499/562949953421312), (6301496297347/2251799813685248)), (88127/4503599627370496), by norm_num⟩
  | 1 => ⟨((139263582785885/140737488355328), (4709572624797/562949953421312)), (33141/562949953421312), by norm_num⟩
  | 0 => ⟨((137793367862215/140737488355328), (37412442240387/2251799813685248)), (133313/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((137793367862215/140737488355328), (37412442240387/2251799813685248)), (508548740867232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2157951790251203/2251799813685248), (36629802595581/1125899906842624)), (530957/2251799813685248), by norm_num⟩
  | 2 => ⟨((2065631647638891/2251799813685248), (17551593087291/281474976710656)), (526103/1125899906842624), by norm_num⟩
  | 3 => ⟨((235762429848443/281474976710656), (257608165182349/2251799813685248)), (515413/562949953421312), by norm_num⟩
  | 4 => ⟨((775159742222547/1125899906842624), (431543348413681/2251799813685248)), (30667/17592186044416), by norm_num⟩
  | 5 => ⟨((984661615484055/2251799813685248), (594218062691361/2251799813685248)), (6909635/2251799813685248), by norm_num⟩
  | 6 => ⟨((34220592525169/281474976710656), (64959561902831/281474976710656)), (19379135/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-90182207/67108864), (-2384192095/134217728)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-391763459/268435456), (-5178623219/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((236444978887261/1125899906842624), (-223968484428151/2251799813685248)), (11711499/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3510289643/8589934592), (831265539/4294967296)), (45/8589934592), by norm_num⟩
  | 2 => ⟨((3415354121/8589934592), (-1617568049/8589934592)), (45/8589934592), by norm_num⟩
  | 3 => ⟨((-1107662041/4294967296), (262303507/2147483648)), (61/17179869184), by norm_num⟩
  | 4 => ⟨((4310821615/34359738368), (-1020838113/17179869184)), (61/34359738368), by norm_num⟩
  | 5 => ⟨((-838847153/17179869184), (397291849/17179869184)), (49/68719476736), by norm_num⟩
  | 6 => ⟨((4352856503/274877906944), (-2061584643/274877906944)), (65/274877906944), by norm_num⟩
  | 7 => ⟨((-4840152941/1099511627776), (1146188137/549755813888)), (37/549755813888), by norm_num⟩
  | 8 => ⟨((4709251365/4398046511104), (-278797391/549755813888)), (37/2199023255552), by norm_num⟩
  | 9 => ⟨((-2036395561/8796093022208), (964470529/8796093022208)), (33/8796093022208), by norm_num⟩
  | 10 => ⟨((396264279/8796093022208), (-1501418393/70368744177664)), (53/70368744177664), by norm_num⟩
  | 11 => ⟨((-1121592265/140737488355328), (265602299/70368744177664)), (19/140737488355328), by norm_num⟩
  | 12 => ⟨((5820047391/4503599627370496), (-2756470449/4503599627370496)), (101/4503599627370496), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693180315/10141204801825835211973625643008), (-288084886361/5070602400912917605986812821504)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222464709161501/79228162514264337593543950336), (-21329976859/19807040628566084398385987584)), (5767/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472702309329491/9903520314283042199192993792), (-767779923893/39614081257132168796771975168)), (12977/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59082839681009/77371252455336267181195264), (-203911173921/618970019642690137449562112)), (3447/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772316947694315/154742504910672534362390528), (-815508070331/154742504910672534362390528)), (13789/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387652278024995/2417851639229258349412352), (-191098420731/2417851639229258349412352)), (101/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((19683003550285/9444732965739290427392), (-668699374903/604462909807314587353088)), (11313/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889292461578745/75557863725914323419136), (-271591125305/18889465931478580854784)), (1149/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((649332233210877/2361183241434822606848), (-814535465877/4722366482869645213696)), (13789/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405748630210331/147573952589676412928), (-1119599802503/590295810358705651712)), (9481/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912703447661205/36893488147419103232), (-174865038087/9223372036854775808)), (23705/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824829686788513/9223372036854775808), (-196623625131/1152921504606846976)), (1667/576460752303423488), by norm_num⟩
  | 6 => ⟨((798038457464667/576460752303423488), (-1571994173343/1152921504606846976)), (13339/576460752303423488), by norm_num⟩
  | 5 => ⟨((299102249559679/36028797018963968), (-687188272117/72057594037927936)), (23349/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494376882730071/36028797018963968), (-1029665079597/18014398509481984)), (35035/36028797018963968), by norm_num⟩
  | 3 => ⟨((93292313223309/562949953421312), (-160641042153/562949953421312)), (43813/9007199254740992), by norm_num⟩
  | 2 => ⟨((558692925326261/1125899906842624), (-5128813755255/4503599627370496)), (87687/4503599627370496), by norm_num⟩
  | 1 => ⟨((2226301631848793/2251799813685248), (-7664036230117/2251799813685248)), (131683/2251799813685248), by norm_num⟩
  | 0 => ⟨((1100489538433855/1125899906842624), (-15211721549325/2251799813685248)), (263981/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1100489538433855/1125899906842624), (-15211721549325/2251799813685248)), (1007007607466887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2151202549577099/2251799813685248), (-29736818210681/2251799813685248)), (259807/1125899906842624), by norm_num⟩
  | 2 => ⟨((2054706685217107/2251799813685248), (-56816701699993/2251799813685248)), (503263/1125899906842624), by norm_num⟩
  | 3 => ⟨((1873430932468081/2251799813685248), (-103687420263087/2251799813685248)), (1887649/2251799813685248), by norm_num⟩
  | 4 => ⟨((776932380121533/1125899906842624), (-86264870992585/1125899906842624)), (414347/281474976710656), by norm_num⟩
  | 5 => ⟨((529516248905131/1125899906842624), (-238109875074407/2251799813685248)), (5082701/2251799813685248), by norm_num⟩
  | 6 => ⟨((236444978887261/1125899906842624), (-223968484428151/2251799813685248)), (11711499/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-391763459/268435456), (-5178623219/268435456)), (1/134217728), by norm_num⟩, -3, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-418646879/268435456), (-2766994215/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-183786854198205/4503599627370496), (-1857510944049875/9007199254740992)), (39750339/9007199254740992), by norm_num⟩
  | 1 => ⟨((364469547/4294967296), (3683648511/8589934592)), (81/8589934592), by norm_num⟩
  | 2 => ⟨((-757893117/8589934592), (-1914982935/4294967296)), (43/4294967296), by norm_num⟩
  | 3 => ⟨((525331477/8589934592), (5309460089/17179869184)), (61/8589934592), by norm_num⟩
  | 4 => ⟨((-17068689/536870912), (-5520355937/34359738368)), (65/17179869184), by norm_num⟩
  | 5 => ⟨((908629529/68719476736), (573962873/8589934592)), (55/34359738368), by norm_num⟩
  | 6 => ⟨((-157453499/34359738368), (-6365451955/274877906944)), (155/274877906944), by norm_num⟩
  | 7 => ⟨((748377935/549755813888), (1890940747/274877906944)), (47/274877906944), by norm_num⟩
  | 8 => ⟨((-194526021/549755813888), (-1966050371/1099511627776)), (25/549755813888), by norm_num⟩
  | 9 => ⟨((719120869/8796093022208), (908508181/2199023255552)), (47/4398046511104), by norm_num⟩
  | 10 => ⟨((-1196295847/70368744177664), (-755675861/8796093022208)), (159/70368744177664), by norm_num⟩
  | 11 => ⟨((452295869/140737488355328), (2285649131/140737488355328)), (123/281474976710656), by norm_num⟩
  | 12 => ⟨((-627015213/1125899906842624), (-1584291251/562949953421312)), (173/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238520483/10141204801825835211973625643008), (-575154330333/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779559423854837/633825300114114700748351602688), (-681243814427/158456325028528675187087900672)), (11559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945315507254221/19807040628566084398385987584), (-3065168342461/39614081257132168796771975168)), (6503/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472615315640195/618970019642690137449562112), (-1628111203883/1237940039285380274899124224)), (6911/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886063532221215/77371252455336267181195264), (-813909661269/38685626227668133590597632)), (13825/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550430803429179/9671406556917033397649408), (-3051541067213/9671406556917033397649408)), (12963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259555914177295/604462909807314587353088), (-2669478367181/604462909807314587353088)), (11347/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((59032434498615/2361183241434822606848), (-2168369962793/37778931862957161709568)), (9221/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298473068246427/4722366482869645213696), (-812884507407/1180591620717411303424)), (13837/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811365284543811/295147905179352825856), (-2234606343467/295147905179352825856)), (19033/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825075787906739/73786976294838206464), (-2792019186119/36893488147419103232)), (23803/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824455587226709/9223372036854775808), (-784829714097/1152921504606846976)), (26795/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797850406783751/576460752303423488), (-6274382525045/1152921504606846976)), (419/18014398509481984), by norm_num⟩
  | 5 => ⟨((1196077661435951/144115188075855872), (-85707810443/2251799813685248)), (23487/144115188075855872), by norm_num⟩
  | 4 => ⟨((186734423884753/4503599627370496), (-8218385735575/36028797018963968)), (8819/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492042317688317/9007199254740992), (-5128128846419/4503599627370496)), (2761/562949953421312), by norm_num⟩
  | 2 => ⟨((558369728323317/1125899906842624), (-5115598137437/1125899906842624)), (44297/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112152127799021/1125899906842624), (-15284229477995/1125899906842624)), (33375/562949953421312), by norm_num⟩
  | 0 => ⟨((8581067893011/8796093022208), (-15159365723581/562949953421312)), (2105/17592186044416), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((8581067893011/8796093022208), (-15159365723581/562949953421312)), (8029937811249489/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((1070709857069205/1125899906842624), (-14788787039951/281474976710656)), (135055/562949953421312), by norm_num⟩
  | 2 => ⟨((1015117116117769/1125899906842624), (-56255444952217/562949953421312)), (542123/1125899906842624), by norm_num⟩
  | 3 => ⟨((1807983201530605/2251799813685248), (-405761575776015/2251799813685248)), (2171821/2251799813685248), by norm_num⟩
  | 4 => ⟨((1378524317204031/2251799813685248), (-651576670689045/2251799813685248)), (1067559/562949953421312), by norm_num⟩
  | 5 => ⟨((163844175486607/562949953421312), (-199443636065875/562949953421312)), (7699629/2251799813685248), by norm_num⟩
  | 6 => ⟨((-183786854198205/4503599627370496), (-1857510944049875/9007199254740992)), (39750339/9007199254740992), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-418646879/268435456), (-2766994215/134217728)), (1/134217728), by norm_num⟩, -3, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile022Terms0
