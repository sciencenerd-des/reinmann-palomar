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
namespace Reinmann.XiRectangle.Tile012Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (705/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (705/128))
  have he : value ((3/4), (705/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-55294967/33554432), (-12994317245/1073741824)), (3/2147483648), by norm_num⟩
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
  | 0 => ⟨((774897401525405/4503599627370496), (388245248363551/4503599627370496)), (927225/2251799813685248), by norm_num⟩
  | 1 => ⟨((-12989987301/34359738368), (-6508346571/34359738368)), (33/34359738368), by norm_num⟩
  | 2 => ⟨((7135479839/17179869184), (3575074761/17179869184)), (39/34359738368), by norm_num⟩
  | 3 => ⟨((-5226083891/17179869184), (-5236828087/34359738368)), (15/17179869184), by norm_num⟩
  | 4 => ⟨((358839999/2147483648), (2876621845/34359738368)), (35/68719476736), by norm_num⟩
  | 5 => ⟨((-20184372867/274877906944), (-2528233687/68719476736)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((14783200047/549755813888), (7406796259/549755813888)), (49/549755813888), by norm_num⟩
  | 7 => ⟨((-18561148843/2199023255552), (-581228385/137438953472)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((10195753105/4398046511104), (2554178585/2199023255552)), (73/8796093022208), by norm_num⟩
  | 9 => ⟨((-1244575517/2199023255552), (-4988536855/17592186044416)), (37/17592186044416), by norm_num⟩
  | 10 => ⟨((17501516251/140737488355328), (4384374313/70368744177664)), (67/140737488355328), by norm_num⟩
  | 11 => ⟨((-6991774845/281474976710656), (-218942159/17592186044416)), (7/70368744177664), by norm_num⟩
  | 12 => ⟨((20483332705/4503599627370496), (10262721979/4503599627370496)), (85/4503599627370496), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (605023541447/10141204801825835211973625643008)), (1821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779426833246469/633825300114114700748351602688), (716518132331/633825300114114700748351602688)), (541/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890482085798327/39614081257132168796771975168), (805965767427/39614081257132168796771975168)), (1217/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890303324525411/2475880078570760549798248448), (214048665687/618970019642690137449562112)), (1293/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771969462289707/154742504910672534362390528), (214008186609/38685626227668133590597632)), (1293/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550283408123543/9671406556917033397649408), (401179352963/4835703278458516698824704)), (2425/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259427299814305/604462909807314587353088), (701891921333/604462909807314587353088)), (1061/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888829573719585/75557863725914323419136), (570126036835/37778931862957161709568)), (431/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649158702385683/2361183241434822606848), (213726786237/1180591620717411303424)), (1293/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811258740204527/295147905179352825856), (1175039409131/590295810358705651712)), (3557/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824810848683571/73786976294838206464), (734056359689/36893488147419103232)), (2223/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824159483265421/9223372036854775808), (825341675569/4611686018427387904)), (5003/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595407147334923/1152921504606846976), (206188104205/144115188075855872)), (5003/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195823441665253/144115188075855872), (360498000897/36028797018963968)), (4379/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493499527143461/36028797018963968), (1080170658545/18014398509481984)), (6571/36028797018963968), by norm_num⟩
  | 3 => ⟨((93223876803951/562949953421312), (2695801152783/9007199254740992)), (8217/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116293431696665/2251799813685248), (168054707343/140737488355328)), (16445/4503599627370496), by norm_num⟩
  | 1 => ⟨((555759291610459/562949953421312), (8032083460637/2251799813685248)), (24697/2251799813685248), by norm_num⟩
  | 0 => ⟨((2194501148333897/2251799813685248), (7963257928391/1125899906842624)), (12379/562949953421312), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2194501148333897/2251799813685248), (7963257928391/1125899906842624)), (47222139598655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1069273921879045/1125899906842624), (31042508418603/2251799813685248)), (97213/2251799813685248), by norm_num⟩
  | 2 => ⟨((253820478119585/281474976710656), (58962514376267/2251799813685248)), (187329/2251799813685248), by norm_num⟩
  | 3 => ⟨((914760016428569/1125899906842624), (106339069746163/2251799813685248)), (86915/562949953421312), by norm_num⟩
  | 4 => ⟨((1481408574864275/2251799813685248), (172794630493909/2251799813685248)), (149441/562949953421312), by norm_num⟩
  | 5 => ⟨((240331463769325/562949953421312), (227355420982339/2251799813685248)), (219563/562949953421312), by norm_num⟩
  | 6 => ⟨((774897401525405/4503599627370496), (388245248363551/4503599627370496)), (927225/2251799813685248), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-12994317245/1073741824)), (3/2147483648), by norm_num⟩, -2, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-927143219/536870912), (-27234832061/2147483648)), (3/2147483648), by norm_num⟩
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
  | 0 => ⟨((1590997643966779/9007199254740992), (-185124092022649/9007199254740992)), (2570379/9007199254740992), by norm_num⟩
  | 1 => ⟨((-27949580825/68719476736), (3252136037/68719476736)), (47/68719476736), by norm_num⟩
  | 2 => ⟨((2011134005/4294967296), (-936039995/17179869184)), (29/34359738368), by norm_num⟩
  | 3 => ⟨((-24697638293/68719476736), (2873748985/68719476736)), (47/68719476736), by norm_num⟩
  | 4 => ⟨((14217103441/68719476736), (-3308525787/137438953472)), (57/137438953472), by norm_num⟩
  | 5 => ⟨((-26188872359/274877906944), (3047264863/274877906944)), (55/274877906944), by norm_num⟩
  | 6 => ⟨((20100702365/549755813888), (-292357777/68719476736)), (11/137438953472), by norm_num⟩
  | 7 => ⟨((-13223879321/1099511627776), (769347039/549755813888)), (15/549755813888), by norm_num⟩
  | 8 => ⟨((7612276849/2199023255552), (-3542974047/8796093022208)), (9/1099511627776), by norm_num⟩
  | 9 => ⟨((-15580369063/17592186044416), (1812888717/17592186044416)), (39/17592186044416), by norm_num⟩
  | 10 => ⟨((14350050219/70368744177664), (-834866107/35184372088832)), (37/70368744177664), by norm_num⟩
  | 11 => ⟨((-24030699431/562949953421312), (1398072911/281474976710656)), (1/8796093022208), by norm_num⟩
  | 12 => ⟨((4611060857/562949953421312), (-2146121229/2251799813685248)), (51/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239623/5070602400912917605986812821504), (-150889769661/10141204801825835211973625643008)), (1821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889652598528937/316912650057057350374175801344), (-178672661237/633825300114114700748351602688)), (1081/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890345280296523/39614081257132168796771975168), (-200976220659/39614081257132168796771975168)), (2433/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890158012704893/2475880078570760549798248448), (-26687452419/309485009821345068724781056)), (323/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771824199975837/154742504910672534362390528), (-213457315117/154742504910672534362390528)), (2585/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550147277285979/9671406556917033397649408), (-200071296527/9671406556917033397649408)), (2423/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629654118945803/302231454903657293676544), (-175017461403/604462909807314587353088)), (265/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888636196599803/75557863725914323419136), (-284319172377/75557863725914323419136)), (3445/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649086229038685/2361183241434822606848), (-213165730501/4722366482869645213696)), (323/590295810358705651712), by norm_num⟩
  | 9 => ⟨((811159159303089/295147905179352825856), (-292983253245/590295810358705651712)), (3553/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824562106132293/73786976294838206464), (-366049720103/73786976294838206464)), (4441/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823879935992769/9223372036854775808), (-411559484513/9223372036854775808)), (1249/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398781989954945/288230376151711744), (-205625823631/576460752303423488)), (4997/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195579556816137/144115188075855872), (-22468699059/9007199254740992)), (1093/36028797018963968), by norm_num⟩
  | 4 => ⟨((373283626768291/9007199254740992), (-134639385021/9007199254740992)), (6559/36028797018963968), by norm_num⟩
  | 3 => ⟨((372781790893289/2251799813685248), (-335994501269/4503599627370496)), (8199/9007199254740992), by norm_num⟩
  | 2 => ⟨((139480084437187/281474976710656), (-1340361198029/4503599627370496)), (16401/4503599627370496), by norm_num⟩
  | 1 => ⟨((277711175518903/281474976710656), (-2001524094969/2251799813685248)), (769/70368744177664), by norm_num⟩
  | 0 => ⟨((1095923707419499/1125899906842624), (-991780725405/562949953421312)), (1539/70368744177664), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1095923707419499/1125899906842624), (-991780725405/562949953421312)), (5870819360232331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((533371053087737/562949953421312), (-7723002749551/2251799813685248)), (6003/140737488355328), by norm_num⟩
  | 2 => ⟨((505339685605763/562949953421312), (-14634430945391/2251799813685248)), (182663/2251799813685248), by norm_num⟩
  | 3 => ⟨((453601267547233/562949953421312), (-26273592130235/2251799813685248)), (330315/2251799813685248), by norm_num⟩
  | 4 => ⟨((365416081514067/562949953421312), (-42340299065179/2251799813685248)), (540017/2251799813685248), by norm_num⟩
  | 5 => ⟨((1895967739376477/4503599627370496), (-109933936972563/4503599627370496)), (1442737/4503599627370496), by norm_num⟩
  | 6 => ⟨((1590997643966779/9007199254740992), (-185124092022649/9007199254740992)), (2570379/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-927143219/536870912), (-27234832061/2147483648)), (3/2147483648), by norm_num⟩, -2, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-1931040333/1073741824), (-28362154891/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((298852447092259/2251799813685248), (-891498033406499/9007199254740992)), (2410851/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2733676415/8589934592), (8154750519/34359738368)), (3/4294967296), by norm_num⟩
  | 2 => ⟨((6555069753/17179869184), (-2444279715/8589934592)), (31/34359738368), by norm_num⟩
  | 3 => ⟨((-10478913849/34359738368), (7814835699/34359738368)), (27/34359738368), by norm_num⟩
  | 4 => ⟨((12563668991/68719476736), (-4684789395/34359738368)), (35/68719476736), by norm_num⟩
  | 5 => ⟨((-12050544993/137438953472), (2246726869/34359738368)), (9/34359738368), by norm_num⟩
  | 6 => ⟨((19263963249/549755813888), (-14366441969/549755813888)), (15/137438953472), by norm_num⟩
  | 7 => ⟨((-13197990403/1099511627776), (1230329403/137438953472)), (43/1099511627776), by norm_num⟩
  | 8 => ⟨((15823699399/4398046511104), (-5900402119/2199023255552)), (27/2199023255552), by norm_num⟩
  | 9 => ⟨((-16863810661/17592186044416), (12576485643/17592186044416)), (15/4398046511104), by norm_num⟩
  | 10 => ⟨((8087530373/35184372088832), (-12062838189/70368744177664)), (15/17592186044416), by norm_num⟩
  | 11 => ⟨((-7052018491/140737488355328), (2629583879/70368744177664)), (27/140737488355328), by norm_num⟩
  | 12 => ⟨((1409166817/140737488355328), (-2101822251/281474976710656)), (45/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (-417348268749/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779194439357581/633825300114114700748351602688), (-988270231715/633825300114114700748351602688)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472555167044593/9903520314283042199192993792), (-1111628163497/39614081257132168796771975168)), (203/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890025598844301/2475880078570760549798248448), (-590444115053/1237940039285380274899124224)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885845885482877/77371252455336267181195264), (-1180644522419/154742504910672534362390528)), (1725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550023109009553/9671406556917033397649408), (-276648842145/2417851639229258349412352)), (809/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157399946823655/75557863725914323419136), (-968012153083/604462909807314587353088)), (177/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((236057448582543/9444732965739290427392), (-786267336143/37778931862957161709568)), (575/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162254996981135/590295810358705651712), (-1178976725307/4722366482869645213696)), (863/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622136112922989/590295810358705651712), (-810201924791/295147905179352825856)), (2373/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824334285231315/73786976294838206464), (-1012235812393/36893488147419103232)), (1483/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823623549972491/9223372036854775808), (-2276110813377/9223372036854775808)), (3337/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797435732368521/576460752303423488), (-1137168704355/576460752303423488)), (1669/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195355001364059/144115188075855872), (-1988051939813/144115188075855872)), (2923/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492797430485241/36028797018963968), (-1489047894275/18014398509481984)), (4385/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490705394339867/9007199254740992), (-1857830528607/4503599627370496)), (5485/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230836551882259/4503599627370496), (-7410486156229/4503599627370496)), (10979/4503599627370496), by norm_num⟩
  | 1 => ⟨((17347024126727/17592186044416), (-1382972419075/281474976710656)), (16495/2251799813685248), by norm_num⟩
  | 0 => ⟨((547323629781293/562949953421312), (-21920597212111/2251799813685248)), (16551/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((547323629781293/562949953421312), (-21920597212111/2251799813685248)), (63137058738326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2128310851507723/2251799813685248), (-21312126877693/1125899906842624)), (16253/562949953421312), by norm_num⟩
  | 2 => ⟨((2010787205025599/2251799813685248), (-80573469500861/2251799813685248)), (31339/562949953421312), by norm_num⟩
  | 3 => ⟨((224085922035225/281474976710656), (-8993700314311/140737488355328)), (116425/1125899906842624), by norm_num⟩
  | 4 => ⟨((1417986194184163/2251799813685248), (-229120090289243/2251799813685248)), (400511/2251799813685248), by norm_num⟩
  | 5 => ⟨((434805265375257/1125899906842624), (-288559509478481/2251799813685248)), (585919/2251799813685248), by norm_num⟩
  | 6 => ⟨((298852447092259/2251799813685248), (-891498033406499/9007199254740992)), (2410851/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-28362154891/2147483648)), (1/1073741824), by norm_num⟩, -2, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-2001111149/1073741824), (-459239375/33554432)), (3/2147483648), by norm_num⟩
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
  | 0 => ⟨((304310977637153/4503599627370496), (-628739828842681/4503599627370496)), (4426811/9007199254740992), by norm_num⟩
  | 1 => ⟨((-360576807/2147483648), (5959929587/17179869184)), (11/8589934592), by norm_num⟩
  | 2 => ⟨((1791999411/8589934592), (-14809868663/34359738368)), (7/4294967296), by norm_num⟩
  | 3 => ⟨((-5937268337/34359738368), (12267047041/34359738368)), (3/2147483648), by norm_num⟩
  | 4 => ⟨((3688389393/34359738368), (-15241233383/68719476736)), (31/34359738368), by norm_num⟩
  | 5 => ⟨((-916530333/17179869184), (7574608437/68719476736)), (1/2147483648), by norm_num⟩
  | 6 => ⟨((6073312851/274877906944), (-3137032479/68719476736)), (55/274877906944), by norm_num⟩
  | 7 => ⟨((-1077972535/137438953472), (8908837563/549755813888)), (5/68719476736), by norm_num⟩
  | 8 => ⟨((5357322241/2199023255552), (-11068814851/2199023255552)), (51/2199023255552), by norm_num⟩
  | 9 => ⟨((-1479160629/2199023255552), (12224431835/8796093022208)), (29/4398046511104), by norm_num⟩
  | 10 => ⟨((5880921733/35184372088832), (-12150628783/35184372088832)), (59/35184372088832), by norm_num⟩
  | 11 => ⟨((-10628030197/281474976710656), (5489668775/70368744177664)), (109/281474976710656), by norm_num⟩
  | 12 => ⟨((4401610485/562949953421312), (-18188419259/1125899906842624)), (23/281474976710656), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-364740801355/2535301200456458802993406410752)), (1821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779092724659477/633825300114114700748351602688), (-1727208180405/633825300114114700748351602688)), (2165/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472526549049461/9903520314283042199192993792), (-1942790041405/39614081257132168796771975168)), (2437/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944951957941093/1237940039285380274899124224), (-2063821842563/2475880078570760549798248448)), (1295/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885785012258989/77371252455336267181195264), (-2063380314805/154742504910672534362390528)), (1295/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549908904308515/9671406556917033397649408), (-966975019825/4835703278458516698824704)), (607/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629549789061389/302231454903657293676544), (-1691737411689/604462909807314587353088)), (2125/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888296968228337/75557863725914323419136), (-2748194438539/75557863725914323419136)), (3453/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162239737529465/590295810358705651712), (-515094277931/1180591620717411303424)), (2591/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405492019986489/147573952589676412928), (-1415884945267/295147905179352825856)), (3563/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824123975866917/73786976294838206464), (-1768920164247/36893488147419103232)), (4455/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823386583841269/9223372036854775808), (-248593613761/576460752303423488)), (2507/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594634039385235/1152921504606846976), (-1987142189837/576460752303423488)), (627/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195146738793623/144115188075855872), (-1736943399111/72057594037927936)), (549/18014398509481984), by norm_num⟩
  | 4 => ⟨((746242004469217/18014398509481984), (-5203613839835/36028797018963968)), (6593/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490311825872711/9007199254740992), (-6491906006427/9007199254740992)), (8251/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230044067984281/4503599627370496), (-6473023690055/2251799813685248)), (8265/2251799813685248), by norm_num⟩
  | 1 => ⟨((2219217091398043/2251799813685248), (-1207806342931/140737488355328)), (12433/1125899906842624), by norm_num⟩
  | 0 => ⟨((546709504450113/562949953421312), (-19137286848871/1125899906842624)), (50023/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((546709504450113/562949953421312), (-19137286848871/1125899906842624)), (190822609908293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2123099728515173/2251799813685248), (-37170396928111/1125899906842624)), (49431/1125899906842624), by norm_num⟩
  | 2 => ⟨((999650563124905/1125899906842624), (-140183792799451/2251799813685248)), (24119/281474976710656), by norm_num⟩
  | 3 => ⟨((1766388589912235/2251799813685248), (-124464711793021/1125899906842624)), (366657/2251799813685248), by norm_num⟩
  | 4 => ⟨((339524274544673/562949953421312), (-390537463271391/2251799813685248)), (656303/2251799813685248), by norm_num⟩
  | 5 => ⟨((93919772951197/281474976710656), (-471078994123303/2251799813685248)), (1019305/2251799813685248), by norm_num⟩
  | 6 => ⟨((304310977637153/4503599627370496), (-628739828842681/4503599627370496)), (4426811/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-459239375/33554432)), (3/2147483648), by norm_num⟩, -2, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-2065570051/1073741824), (-15169030063/1073741824)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((13033435842197/9007199254740992), (-1315560859190513/9007199254740992)), (1644569/4503599627370496), by norm_num⟩
  | 1 => ⟨((-63762861/17179869184), (25744224399/68719476736)), (33/34359738368), by norm_num⟩
  | 2 => ⟨((327097019/68719476736), (-33016315915/68719476736)), (87/68719476736), by norm_num⟩
  | 3 => ⟨((-139831215/34359738368), (28228392763/68719476736)), (77/68719476736), by norm_num⟩
  | 4 => ⟨((179329993/68719476736), (-9050549735/34359738368)), (13/17179869184), by norm_num⟩
  | 5 => ⟨((-45997235/34359738368), (9285680691/68719476736)), (55/137438953472), by norm_num⟩
  | 6 => ⟨((78653719/137438953472), (-15878200481/274877906944)), (3/17179869184), by norm_num⟩
  | 7 => ⟨((-230563207/1099511627776), (23272445783/1099511627776)), (9/137438953472), by norm_num⟩
  | 8 => ⟨((295691475/4398046511104), (-7461580607/1099511627776)), (95/4398046511104), by norm_num⟩
  | 9 => ⟨((-168540813/8796093022208), (2126508487/1099511627776)), (7/1099511627776), by norm_num⟩
  | 10 => ⟨((43229865/8796093022208), (-17454037047/35184372088832)), (59/35184372088832), by norm_num⟩
  | 11 => ⟨((-20160439/17592186044416), (32559069897/281474976710656)), (7/17592186044416), by norm_num⟩
  | 12 => ⟨((17236835/70368744177664), (-27837455137/1125899906842624)), (49/562949953421312), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418445/10141204801825835211973625643008), (-1016616435925/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111187415610801/39614081257132168796771975168), (-1203412335521/316912650057057350374175801344)), (723/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59062509187839/1237940039285380274899124224), (-2707217097671/39614081257132168796771975168)), (813/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889791305654967/2475880078570760549798248448), (-2875853264163/2475880078570760549798248448)), (27/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1771457314080187/154742504910672534362390528), (-2875217897801/154742504910672534362390528)), (27/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1549803131872455/9671406556917033397649408), (-2694841857909/9671406556917033397649408)), (1621/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259006920922847/604462909807314587353088), (-1178655939625/302231454903657293676544)), (1419/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888146201106189/75557863725914323419136), (-3829367025753/75557863725914323419136)), (2305/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648902325396487/2361183241434822606848), (-717729739995/1180591620717411303424)), (1729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810906039687489/295147905179352825856), (-3945716513597/590295810358705651712)), (2379/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911964275922225/36893488147419103232), (-2464725637819/36893488147419103232)), (1487/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455791537673811/2305843009213693952), (-1385482477589/2305843009213693952)), (837/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199301610153749/144115188075855872), (-5537304409433/1152921504606846976)), (1675/576460752303423488), by norm_num⟩
  | 5 => ⟨((597476205841845/72057594037927936), (-604992718547/18014398509481984)), (1467/72057594037927936), by norm_num⟩
  | 4 => ⟨((746095447798259/18014398509481984), (-906190449315/4503599627370496)), (2203/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489942605226415/9007199254740992), (-9043746611821/9007199254740992)), (1379/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114648591276153/2251799813685248), (-18033111182595/4503599627370496)), (5529/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218075802154961/2251799813685248), (-13457015987475/1125899906842624)), (8327/1125899906842624), by norm_num⟩
  | 0 => ⟨((2184472487002023/2251799813685248), (-53287444120179/2251799813685248)), (33577/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2184472487002023/2251799813685248), (-53287444120179/2251799813685248)), (128086098677825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2117897188632841/2251799813685248), (-25847092373785/562949953421312)), (4171/140737488355328), by norm_num⟩
  | 2 => ⟨((1987210106101157/2251799813685248), (-97240409986861/1125899906842624)), (8229/140737488355328), by norm_num⟩
  | 3 => ⟨((217114171999373/281474976710656), (-343258089414373/2251799813685248)), (127565/1125899906842624), by norm_num⟩
  | 4 => ⟨((1287433253232833/2251799813685248), (-264770235479575/1125899906842624)), (235685/1125899906842624), by norm_num⟩
  | 5 => ⟨((611542492710465/2251799813685248), (-605513871261629/2251799813685248)), (95087/281474976710656), by norm_num⟩
  | 6 => ⟨((13033435842197/9007199254740992), (-1315560859190513/9007199254740992)), (1644569/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2065570051/1073741824), (-15169030063/1073741824)), (1/1073741824), by norm_num⟩, -2, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2125249673/1073741824), (-15607302287/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-241320753107245/4503599627370496), (-573547986402741/4503599627370496)), (6835877/9007199254740992), by norm_num⟩
  | 1 => ⟨((2429425439/17179869184), (23096100119/68719476736)), (35/17179869184), by norm_num⟩
  | 2 => ⟨((-1602848253/8589934592), (-3809495769/8589934592)), (47/17179869184), by norm_num⟩
  | 3 => ⟨((705001405/4294967296), (13404636975/34359738368)), (85/34359738368), by norm_num⟩
  | 4 => ⟨((-7442156501/68719476736), (-8843901365/34359738368)), (57/34359738368), by norm_num⟩
  | 5 => ⟨((7856111065/137438953472), (145872267/1073741824)), (61/68719476736), by norm_num⟩
  | 6 => ⟨((-6910909163/274877906944), (-4106296271/68719476736)), (109/274877906944), by norm_num⟩
  | 7 => ⟨((5210938709/549755813888), (3096214649/137438953472)), (21/137438953472), by norm_num⟩
  | 8 => ⟨((-6875982997/2199023255552), (-16342175927/2199023255552)), (113/2199023255552), by norm_num⟩
  | 9 => ⟨((1008117407/1099511627776), (19167972961/8796093022208)), (135/8796093022208), by norm_num⟩
  | 10 => ⟨((-8513534823/35184372088832), (-20234151815/35184372088832)), (145/35184372088832), by norm_num⟩
  | 11 => ⟨((4085037541/70368744177664), (19417849693/140737488355328)), (141/140737488355328), by norm_num⟩
  | 12 => ⟨((-7187098843/562949953421312), (-8540803093/281474976710656)), (63/281474976710656), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (-2564923537471/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222363889670407/79228162514264337593543950336), (-3035931202317/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889901733087931/39614081257132168796771975168), (-3414822148463/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889686470384469/2475880078570760549798248448), (-3627515024143/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771352350344303/154742504910672534362390528), (-56667030907/2417851639229258349412352)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549704591970777/9671406556917033397649408), (-3399145421765/9671406556917033397649408)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258920562216667/604462909807314587353088), (-2973376012425/604462909807314587353088)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236000701611021/9444732965739290427392), (-4830093513101/75557863725914323419136)), (2307/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648849493225669/2361183241434822606848), (-3621133368315/4722366482869645213696)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621666428666701/590295810358705651712), (-1244181109207/147573952589676412928)), (2381/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823745945846143/73786976294838206464), (-6217406030813/73786976294838206464)), (5955/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822959974063685/9223372036854775808), (-6989772228929/9223372036854775808)), (6705/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594205775306409/1152921504606846976), (-3491881850363/576460752303423488)), (3355/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194770151036137/144115188075855872), (-1526009585355/36028797018963968)), (2939/72057594037927936), by norm_num⟩
  | 4 => ⟨((46622357028459/1125899906842624), (-9142559462083/36028797018963968)), (8829/36028797018963968), by norm_num⟩
  | 3 => ⟨((744797320663919/4503599627370496), (-5702302080743/4503599627370496)), (11059/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228590433851821/4503599627370496), (-22738528504441/4503599627370496)), (22185/4503599627370496), by norm_num⟩
  | 1 => ⟨((554247205336789/562949953421312), (-16965731530485/1125899906842624)), (33447/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182192257205001/2251799813685248), (-33579913098577/1125899906842624)), (67575/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2182192257205001/2251799813685248), (-33579913098577/1125899906842624)), (257778176314543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2112733368320463/2251799813685248), (-130167568033335/2251799813685248)), (33751/562949953421312), by norm_num⟩
  | 2 => ⟨((987365453807735/1125899906842624), (-15266086420393/140737488355328)), (134471/1125899906842624), by norm_num⟩
  | 3 => ⟨((426314593457491/562949953421312), (-428406290960181/2251799813685248)), (530047/2251799813685248), by norm_num⟩
  | 4 => ⟨((1209865173105375/2251799813685248), (-81106611988933/281474976710656)), (15695/35184372088832), by norm_num⟩
  | 5 => ⟨((231540044151181/1125899906842624), (-348620919346775/1125899906842624)), (1658271/2251799813685248), by norm_num⟩
  | 6 => ⟨((-241320753107245/4503599627370496), (-573547986402741/4503599627370496)), (6835877/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-15607302287/1073741824)), (1/536870912), by norm_num⟩, -2, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-272601259/134217728), (-16015323965/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-829634085029943/9007199254740992), (-420776897164151/4503599627370496)), (3356677/4503599627370496), by norm_num⟩
  | 1 => ⟨((1071305633/4294967296), (4346790165/17179869184)), (71/34359738368), by norm_num⟩
  | 2 => ⟨((-11604597739/34359738368), (-2942831495/8589934592)), (49/17179869184), by norm_num⟩
  | 3 => ⟨((10475277747/34359738368), (5312890281/17179869184)), (45/17179869184), by norm_num⟩
  | 4 => ⟨((-3545947251/17179869184), (-7193786797/34359738368)), (31/17179869184), by norm_num⟩
  | 5 => ⟨((7682082533/68719476736), (7792454313/68719476736)), (137/137438953472), by norm_num⟩
  | 6 => ⟨((-13868976765/274877906944), (-14068238313/274877906944)), (63/137438953472), by norm_num⟩
  | 7 => ⟨((1341353047/68719476736), (10884998741/549755813888)), (25/137438953472), by norm_num⟩
  | 8 => ⟨((-14529805555/2199023255552), (-14738561515/2199023255552)), (69/1099511627776), by norm_num⟩
  | 9 => ⟨((4371938095/2199023255552), (554343951/274877906944)), (85/4398046511104), by norm_num⟩
  | 10 => ⟨((-4735771135/8796093022208), (-9607623987/17592186044416)), (47/8796093022208), by norm_num⟩
  | 11 => ⟨((4663529445/35184372088832), (9461064753/70368744177664)), (95/70368744177664), by norm_num⟩
  | 12 => ⟨((-4209690617/140737488355328), (-4270173051/140737488355328)), (87/281474976710656), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (-1529957851859/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778829252708495/633825300114114700748351602688), (-3621511609097/633825300114114700748351602688)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889809533783441/39614081257132168796771975168), (-4073461927737/39614081257132168796771975168)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236198546851255/309485009821345068724781056), (-2163577471575/1237940039285380274899124224)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771254104358853/154742504910672534362390528), (-2163072209741/77371252455336267181195264)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549612326661875/9671406556917033397649408), (-4054686898523/9671406556917033397649408)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258839670502219/604462909807314587353088), (-1773388875599/302231454903657293676544)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887873864932715/75557863725914323419136), (-5761501882097/75557863725914323419136)), (2309/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648799957101385/2361183241434822606848), (-4319366389337/4722366482869645213696)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810764890126237/295147905179352825856), (-5936269585553/590295810358705651712)), (4767/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823574500112959/73786976294838206464), (-7416049646389/73786976294838206464)), (2981/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822766225643173/9223372036854775808), (-4168581572985/4611686018427387904)), (6713/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199251367387051/144115188075855872), (-8329800835131/1152921504606846976)), (105/18014398509481984), by norm_num⟩
  | 5 => ⟨((597299224287609/72057594037927936), (-7280298045181/144115188075855872)), (23/562949953421312), by norm_num⟩
  | 4 => ⟨((745827718560419/18014398509481984), (-10903903990131/36028797018963968)), (8847/36028797018963968), by norm_num⟩
  | 3 => ⟨((372316353417179/2251799813685248), (-13600957284403/9007199254740992)), (11085/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113959658322155/2251799813685248), (-13557628650113/2251799813685248)), (11125/2251799813685248), by norm_num⟩
  | 1 => ⟨((276993840539095/281474976710656), (-2528539451123/140737488355328)), (16789/1125899906842624), by norm_num⟩
  | 0 => ⟨((544997943677915/562949953421312), (-40025289032135/1125899906842624)), (33985/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((544997943677915/562949953421312), (-40025289032135/1125899906842624)), (129642490867232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1053813934506669/1125899906842624), (-19374457787105/281474976710656)), (17055/281474976710656), by norm_num⟩
  | 2 => ⟨((981008958269773/1125899906842624), (-72536016622715/562949953421312)), (137097/1125899906842624), by norm_num⟩
  | 3 => ⟨((418035686678123/562949953421312), (-63201428183469/281474976710656)), (548477/2251799813685248), by norm_num⟩
  | 4 => ⟨((564086211478557/1125899906842624), (-375457210988579/1125899906842624)), (265221/562949953421312), by norm_num⟩
  | 5 => ⟨((629630167370397/4503599627370496), (-1504860134949501/4503599627370496)), (885289/1125899906842624), by norm_num⟩
  | 6 => ⟨((-829634085029943/9007199254740992), (-420776897164151/4503599627370496)), (3356677/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-16015323965/1073741824)), (1/536870912), by norm_num⟩, -2, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile012Terms1
