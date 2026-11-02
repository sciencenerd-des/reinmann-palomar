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
namespace Reinmann.XiRectangle.Tile016Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4653/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4653/640))
  have he : value ((3/4), (4653/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-55294967/33554432), (-4288124691/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1672222471749385/9007199254740992), (228294452433227/4503599627370496)), (2330407/2251799813685248), by norm_num⟩
  | 1 => ⟨((14016144995/34359738368), (-3827012495/34359738368)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((-15398309131/34359738368), (1051100739/8589934592)), (45/17179869184), by norm_num⟩
  | 3 => ⟨((11277847757/34359738368), (-6158678339/68719476736)), (135/68719476736), by norm_num⟩
  | 4 => ⟨((-24779964271/137438953472), (6765999705/137438953472)), (151/137438953472), by norm_num⟩
  | 5 => ⟨((1361178663/17179869184), (-5946568337/274877906944)), (135/274877906944), by norm_num⟩
  | 6 => ⟨((-7975507233/274877906944), (4355315367/549755813888)), (101/549755813888), by norm_num⟩
  | 7 => ⟨((2503425787/274877906944), (-2734173133/1099511627776)), (129/2199023255552), by norm_num⟩
  | 8 => ⟨((-22002354667/8796093022208), (3003796203/4398046511104)), (145/8796093022208), by norm_num⟩
  | 9 => ⟨((21486273081/35184372088832), (-1466669965/8796093022208)), (9/2199023255552), by norm_num⟩
  | 10 => ⟨((-18884066915/140737488355328), (2578082635/70368744177664)), (129/140737488355328), by norm_num⟩
  | 11 => ⟨((15088194889/562949953421312), (-16092689/2199023255552)), (105/562949953421312), by norm_num⟩
  | 12 => ⟨((-5525358773/1125899906842624), (3017322819/2251799813685248)), (39/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (3745069212181/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779416592784073/633825300114114700748351602688), (4435215844567/633825300114114700748351602688)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945234987344509/19807040628566084398385987584), (4988864034859/39614081257132168796771975168)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890289702541131/2475880078570760549798248448), (5299773490221/2475880078570760549798248448)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110747187036937/9671406556917033397649408), (5298767001695/154742504910672534362390528)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((96891808908843/604462909807314587353088), (155203895919/302231454903657293676544)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629706871352183/302231454903657293676544), (4344639690149/604462909807314587353088)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888805857522061/75557863725914323419136), (7058034378293/75557863725914323419136)), (289/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1298298143557485/4722366482869645213696), (2645885652155/2361183241434822606848)), (1735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622488602928879/590295810358705651712), (3636667256793/295147905179352825856)), (2387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912385582722737/36893488147419103232), (4543695798959/36893488147419103232)), (1493/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456027478538073/2305843009213693952), (638589706539/576460752303423488)), (6725/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595351430099331/1152921504606846976), (638130313455/72057594037927936)), (3367/576460752303423488), by norm_num⟩
  | 5 => ⟨((18683871631611/2251799813685248), (1115694417983/18014398509481984)), (2951/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493402261879511/36028797018963968), (6685897518837/18014398509481984)), (4435/18014398509481984), by norm_num⟩
  | 3 => ⟨((745718200299037/4503599627370496), (8342901338263/4503599627370496)), (11121/9007199254740992), by norm_num⟩
  | 2 => ⟨((558055933896769/1125899906842624), (16642391906639/2251799813685248)), (11171/2251799813685248), by norm_num⟩
  | 1 => ⟨((555578433996969/562949953421312), (12427532575125/562949953421312)), (16879/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096172479412817/1125899906842624), (24638036470515/562949953421312)), (2141/70368744177664), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1096172479412817/1125899906842624), (24638036470515/562949953421312)), (8167267114138581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((133134167385757/140737488355328), (47975023999221/562949953421312)), (34851/562949953421312), by norm_num⟩
  | 2 => ⟨((249838995252331/281474976710656), (90766361544297/562949953421312)), (71877/562949953421312), by norm_num⟩
  | 3 => ⟨((857765633834571/1125899906842624), (322259219429625/1125899906842624)), (301551/1125899906842624), by norm_num⟩
  | 4 => ⟨((561249605084619/1125899906842624), (982051359745691/2251799813685248)), (632095/1125899906842624), by norm_num⟩
  | 5 => ⟨((262527425267403/4503599627370496), (1958170293754627/4503599627370496)), (4726091/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1672222471749385/9007199254740992), (228294452433227/4503599627370496)), (2330407/2251799813685248), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-4288124691/268435456)), (1/536870912), by norm_num⟩, -3, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-927143219/536870912), (-2246873645/134217728)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-51318596036027/562949953421312), (687630581777583/4503599627370496)), (2231235/2251799813685248), by norm_num⟩
  | 1 => ⟨((7212245741/34359738368), (-3019958357/8589934592)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((-8303404765/34359738368), (3476855547/8589934592)), (47/17179869184), by norm_num⟩
  | 3 => ⟨((12746197355/68719476736), (-2668585251/8589934592)), (147/68719476736), by norm_num⟩
  | 4 => ⟨((-7337301005/68719476736), (3072322309/17179869184)), (87/68719476736), by norm_num⟩
  | 5 => ⟨((6757903967/137438953472), (-11318853679/137438953472)), (41/68719476736), by norm_num⟩
  | 6 => ⟨((-2593441489/137438953472), (4343770625/137438953472)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((3412354121/549755813888), (-5715372279/549755813888)), (43/549755813888), by norm_num⟩
  | 8 => ⟨((-7857235731/4398046511104), (6580065505/2199023255552)), (101/4398046511104), by norm_num⟩
  | 9 => ⟨((8040868385/17592186044416), (-6733849219/8796093022208)), (105/17592186044416), by norm_num⟩
  | 10 => ⟨((-7405913471/70368744177664), (1550526083/8796093022208)), (49/35184372088832), by norm_num⟩
  | 11 => ⟨((3100499265/140737488355328), (-324565295/8796093022208)), (167/562949953421312), by norm_num⟩
  | 12 => ⟨((-4759442259/1125899906842624), (15943236479/2251799813685248)), (65/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239623/5070602400912917605986812821504), (1373631821281/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27801555559835/9903520314283042199192993792), (3253109254777/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945169304939469/19807040628566084398385987584), (3659180553649/39614081257132168796771975168)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890150510196669/2475880078570760549798248448), (1943596551399/1237940039285380274899124224)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771816230670175/154742504910672534362390528), (3886421155541/154742504910672534362390528)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193767413794085/1208925819614629174706176), (1821349874729/4835703278458516698824704)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259300771411605/604462909807314587353088), (398317790081/75557863725914323419136)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888623135298231/75557863725914323419136), (647074263605/9444732965739290427392)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298161850491771/4722366482869645213696), (3881100827817/4722366482869645213696)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202787801935995/73786976294838206464), (1333582226717/147573952589676412928)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912270126380771/36893488147419103232), (3332317450339/36893488147419103232)), (2979/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911926319697023/4611686018427387904), (7493210848063/9223372036854775808)), (1677/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595097278786919/1152921504606846976), (7487583688009/1152921504606846976)), (6713/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597774455154307/72057594037927936), (409081754623/9007199254740992)), (5881/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493080953296799/36028797018963968), (9805314066581/36028797018963968)), (8835/36028797018963968), by norm_num⟩
  | 3 => ⟨((372761746989189/2251799813685248), (6117262431325/4503599627370496)), (2767/2251799813685248), by norm_num⟩
  | 2 => ⟨((1115740726916691/2251799813685248), (6100690520671/1125899906842624)), (11105/2251799813685248), by norm_num⟩
  | 1 => ⟨((555322808077925/562949953421312), (18219326870521/1125899906842624)), (4187/281474976710656), by norm_num⟩
  | 0 => ⟨((547665247419005/562949953421312), (36108365762645/1125899906842624)), (33859/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((547665247419005/562949953421312), (36108365762645/1125899906842624)), (129161839011764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064433056225083/1125899906842624), (70255968400427/1125899906842624)), (17013/281474976710656), by norm_num⟩
  | 2 => ⟨((500968968570343/562949953421312), (16605111766159/140737488355328)), (8573/70368744177664), by norm_num⟩
  | 3 => ⟨((1751901604636197/2251799813685248), (59107532837913/281474976710656)), (69125/281474976710656), by norm_num⟩
  | 4 => ⟨((631841779848551/1125899906842624), (367885567786269/1125899906842624)), (1092721/2251799813685248), by norm_num⟩
  | 5 => ⟨((468752581242809/2251799813685248), (825812207703333/2251799813685248)), (970267/1125899906842624), by norm_num⟩
  | 6 => ⟨((-51318596036027/562949953421312), (687630581777583/4503599627370496)), (2231235/2251799813685248), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-927143219/536870912), (-2246873645/134217728)), (1/536870912), by norm_num⟩, -3, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-1931040333/1073741824), (-4679755557/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((229757429815503/9007199254740992), (736713110569641/4503599627370496)), (3549003/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4203294791/68719476736), (-13477789957/34359738368)), (33/17179869184), by norm_num⟩
  | 2 => ⟨((2519765177/34359738368), (16159164413/34359738368)), (81/34359738368), by norm_num⟩
  | 3 => ⟨((-4028088671/68719476736), (-12915994653/34359738368)), (33/17179869184), by norm_num⟩
  | 4 => ⟨((18865107/536870912), (15485601261/68719476736)), (81/68719476736), by norm_num⟩
  | 5 => ⟨((-1158055703/68719476736), (-1856642503/17179869184)), (79/137438953472), by norm_num⟩
  | 6 => ⟨((3702528395/549755813888), (23744182833/549755813888)), (129/549755813888), by norm_num⟩
  | 7 => ⟨((-158540631/68719476736), (-2033430849/137438953472)), (45/549755813888), by norm_num⟩
  | 8 => ⟨((3041310637/4398046511104), (9751908441/2199023255552)), (55/2199023255552), by norm_num⟩
  | 9 => ⟨((-3241219733/17592186044416), (-20785826801/17592186044416)), (15/2199023255552), by norm_num⟩
  | 10 => ⟨((1554421095/35184372088832), (19936894331/70368744177664)), (117/70368744177664), by norm_num⟩
  | 11 => ⟨((-2710791997/281474976710656), (-135814161/2199023255552)), (13/35184372088832), by norm_num⟩
  | 12 => ⟨((4333463543/2251799813685248), (13895173745/1125899906842624)), (169/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (922319354387/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889596205350231/316912650057057350374175801344), (2184029095907/633825300114114700748351602688)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890218269836657/39614081257132168796771975168), (1228320656859/19807040628566084398385987584)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890022901345041/2475880078570760549798248448), (2609702182525/2475880078570760549798248448)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771688905662045/154742504910672534362390528), (652290796895/38685626227668133590597632)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550020244593435/9671406556917033397649408), (305689741439/1208925819614629174706176)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259196890141893/604462909807314587353088), (1069627887069/302231454903657293676544)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236056861595291/9444732965739290427392), (868804413119/18889465931478580854784)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1298036162198257/4722366482869645213696), (2605474680741/4722366482869645213696)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811065197768179/295147905179352825856), (3581003089365/590295810358705651712)), (2377/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912163214421293/36893488147419103232), (559245993549/9223372036854775808)), (5945/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823613737008663/9223372036854775808), (2515036202935/4611686018427387904)), (1673/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594860435487887/1152921504606846976), (5026147877049/1152921504606846976)), (837/144115188075855872), by norm_num⟩
  | 5 => ⟨((597671992511139/72057594037927936), (549183448017/18014398509481984)), (733/18014398509481984), by norm_num⟩
  | 4 => ⟨((1492778180896939/36028797018963968), (3290692986091/18014398509481984)), (8803/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490676577897675/9007199254740992), (8211323975239/9007199254740992)), (11021/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230764713210935/4503599627370496), (1023531018301/281474976710656)), (22089/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110138008377919/1125899906842624), (12224811693233/1125899906842624)), (4157/281474976710656), by norm_num⟩
  | 0 => ⟨((547217081039851/562949953421312), (48440309095385/2251799813685248)), (67001/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((547217081039851/562949953421312), (48440309095385/2251799813685248)), (255588540084075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2126653554130061/2251799813685248), (94173076618079/2251799813685248)), (133141/2251799813685248), by norm_num⟩
  | 2 => ⟨((2004524000535881/2251799813685248), (177878607926019/2251799813685248)), (65655/562949953421312), by norm_num⟩
  | 3 => ⟨((442587707546091/562949953421312), (316690619301611/2251799813685248)), (254527/1125899906842624), by norm_num⟩
  | 4 => ⟨((1347299655654423/2251799813685248), (248980170166483/1125899906842624)), (943617/2251799813685248), by norm_num⟩
  | 5 => ⟨((86999955105749/281474976710656), (297940248055257/1125899906842624)), (773257/1125899906842624), by norm_num⟩
  | 6 => ⟨((229757429815503/9007199254740992), (736713110569641/4503599627370496)), (3549003/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-4679755557/268435456)), (1/536870912), by norm_num⟩, -3, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-2001111149/1073741824), (-606195975/33554432)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((989710451349685/9007199254740992), (30811755132091/281474976710656)), (2471813/4503599627370496), by norm_num⟩
  | 1 => ⟨((-586351891/2147483648), (-9346232327/34359738368)), (49/34359738368), by norm_num⟩
  | 2 => ⟨((11656237705/34359738368), (5806128715/17179869184)), (63/34359738368), by norm_num⟩
  | 3 => ⟨((-1206860941/4294967296), (-9618458569/34359738368)), (27/17179869184), by norm_num⟩
  | 4 => ⟨((11995747111/68719476736), (11950485829/68719476736)), (69/68719476736), by norm_num⟩
  | 5 => ⟨((-5961662353/68719476736), (-5939168341/68719476736)), (35/68719476736), by norm_num⟩
  | 6 => ⟨((9876116283/274877906944), (9838852603/274877906944)), (15/68719476736), by norm_num⟩
  | 7 => ⟨((-3505889575/274877906944), (-13970645863/1099511627776)), (11/137438953472), by norm_num⟩
  | 8 => ⟨((4355904159/1099511627776), (4339468851/1099511627776)), (57/2199023255552), by norm_num⟩
  | 9 => ⟨((-4810673427/4398046511104), (-299532639/274877906944)), (65/8796093022208), by norm_num⟩
  | 10 => ⟨((9563259511/35184372088832), (9527176275/35184372088832)), (33/17592186044416), by norm_num⟩
  | 11 => ⟨((-8641384419/140737488355328), (-33628045/549755813888)), (61/140737488355328), by norm_num⟩
  | 12 => ⟨((14315355737/1125899906842624), (14261342317/1125899906842624)), (13/140737488355328), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (255151676761/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779093539530533/633825300114114700748351602688), (604127728113/316912650057057350374175801344)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472526789852007/9903520314283042199192993792), (1359064744693/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944952499615155/1237940039285380274899124224), (721865870377/1237940039285380274899124224)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885785587623477/77371252455336267181195264), (1443422965059/154742504910672534362390528)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774955027334091/4835703278458516698824704), (1352881043609/9671406556917033397649408)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259100656192711/604462909807314587353088), (591721513039/302231454903657293676544)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472074713516629/18889465931478580854784), (1922480339521/75557863725914323419136)), (4601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297919431744375/4722366482869645213696), (1441322709357/4722366482869645213696)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405492593980893/147573952589676412928), (990472804249/295147905179352825856)), (2373/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824127130748635/73786976294838206464), (2474873024871/73786976294838206464)), (2967/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823390524314289/9223372036854775808), (347804177183/1152921504606846976)), (1669/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99664904257393/72057594037927936), (2780186676809/1152921504606846976)), (6679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195151162157987/144115188075855872), (2430138065457/144115188075855872)), (5847/144115188075855872), by norm_num⟩
  | 4 => ⟨((746245868880377/18014398509481984), (1820081152781/18014398509481984)), (8775/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490323395011095/9007199254740992), (4541387442165/9007199254740992)), (5489/4503599627370496), by norm_num⟩
  | 2 => ⟨((2230072906657139/4503599627370496), (9056380280901/4503599627370496)), (10991/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109637258431157/1125899906842624), (1689845573655/281474976710656)), (33039/2251799813685248), by norm_num⟩
  | 0 => ⟨((1093504519620889/1125899906842624), (13387693639217/1125899906842624)), (66351/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1093504519620889/1125899906842624), (13387693639217/1125899906842624)), (253108986861418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((530941026295621/562949953421312), (26004982170817/1125899906842624)), (130463/2251799813685248), by norm_num⟩
  | 2 => ⟨((2001807136973505/2251799813685248), (24526357696027/562949953421312)), (126059/1125899906842624), by norm_num⟩
  | 3 => ⟨((221911774405599/281474976710656), (174427718064407/2251799813685248)), (235113/1125899906842624), by norm_num⟩
  | 4 => ⟨((693055490961369/1125899906842624), (137516893592221/1125899906842624)), (203573/562949953421312), by norm_num⟩
  | 5 => ⟨((819637722188649/2251799813685248), (84649476942679/562949953421312)), (600701/1125899906842624), by norm_num⟩
  | 6 => ⟨((989710451349685/9007199254740992), (30811755132091/281474976710656)), (2471813/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-606195975/33554432)), (1/536870912), by norm_num⟩, -3, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-2065570051/1073741824), (-20023119683/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((322246971287829/2251799813685248), (8231304373941/281474976710656)), (1525241/4503599627370496), by norm_num⟩
  | 1 => ⟨((-6306054397/17179869184), (-2577255721/34359738368)), (31/34359738368), by norm_num⟩
  | 2 => ⟨((16174710173/34359738368), (3305265203/34359738368)), (21/17179869184), by norm_num⟩
  | 3 => ⟨((-13829104155/34359738368), (-2825945953/34359738368)), (37/34359738368), by norm_num⟩
  | 4 => ⟨((4433868977/17179869184), (113256379/2147483648)), (49/68719476736), by norm_num⟩
  | 5 => ⟨((-18196239013/137438953472), (-929590005/34359738368)), (53/137438953472), by norm_num⟩
  | 6 => ⟨((3889369297/68719476736), (397391881/34359738368)), (47/274877906944), by norm_num⟩
  | 7 => ⟨((-1425147897/68719476736), (-582451457/137438953472)), (71/1099511627776), by norm_num⟩
  | 8 => ⟨((14621728731/2199023255552), (2987916981/2199023255552)), (3/137438953472), by norm_num⟩
  | 9 => ⟨((-8334220825/4398046511104), (-3406158107/8796093022208)), (7/1099511627776), by norm_num⟩
  | 10 => ⟨((2137685435/4398046511104), (3494649219/35184372088832)), (59/35184372088832), by norm_num⟩
  | 11 => ⟨((-7975352557/70368744177664), (-407436285/17592186044416)), (57/140737488355328), by norm_num⟩
  | 12 => ⟨((13637583611/562949953421312), (5573618333/1125899906842624)), (25/281474976710656), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418445/10141204801825835211973625643008), (262570747551/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444750424338913/158456325028528675187087900672), (310816218767/633825300114114700748351602688)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890003895839669/39614081257132168796771975168), (349609356961/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944897678348119/1237940039285380274899124224), (371387061055/2475880078570760549798248448)), (1723/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442865404260951/38685626227668133590597632), (371305098363/154742504910672534362390528)), (1723/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549807433410445/9671406556917033397649408), (87002867469/2417851639229258349412352)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((629505476050257/302231454903657293676544), (304423005021/604462909807314587353088)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888153252639897/75557863725914323419136), (247262130405/37778931862957161709568)), (2297/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648905188663683/2361183241434822606848), (370750524527/4722366482869645213696)), (1723/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621820664214787/590295810358705651712), (509550244991/590295810358705651712)), (2369/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823940347941029/73786976294838206464), (318295208375/36893488147419103232)), (5923/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113948805233563/576460752303423488), (178921720715/2305843009213693952)), (6663/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797214719653425/576460752303423488), (89386337419/144115188075855872)), (833/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194968949036791/144115188075855872), (312517161891/72057594037927936)), (729/18014398509481984), by norm_num⟩
  | 4 => ⟨((746109894695679/18014398509481984), (468106539151/18014398509481984)), (2187/9007199254740992), by norm_num⟩
  | 3 => ⟨((744992926455389/4503599627370496), (583963942549/4503599627370496)), (5469/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114702488428515/2251799813685248), (2328855357509/4503599627370496)), (10941/2251799813685248), by norm_num⟩
  | 1 => ⟨((277286302315975/281474976710656), (3475834307811/2251799813685248)), (32841/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185111492276045/2251799813685248), (3441093315491/1125899906842624)), (32877/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2185111492276045/2251799813685248), (3441093315491/1125899906842624)), (125415806296920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((33130892953981/35184372088832), (13356733585243/2251799813685248)), (8001/140737488355328), by norm_num⟩
  | 2 => ⟨((1996545529748429/2251799813685248), (25154378740099/2251799813685248)), (242609/2251799813685248), by norm_num⟩
  | 3 => ⟨((884972386392099/1125899906842624), (44605974404937/2251799813685248)), (435637/2251799813685248), by norm_num⟩
  | 4 => ⟨((1390316664352961/2251799813685248), (70121785030043/2251799813685248)), (702093/2251799813685248), by norm_num⟩
  | 5 => ⟨((856232135167609/2251799813685248), (173179668403813/4503599627370496)), (1821413/4503599627370496), by norm_num⟩
  | 6 => ⟨((322246971287829/2251799813685248), (8231304373941/281474976710656)), (1525241/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2065570051/1073741824), (-20023119683/1073741824)), (1/536870912), by norm_num⟩, -3, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2125249673/1073741824), (-10300819509/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1174406108727505/9007199254740992), (-411755128845987/9007199254740992)), (3235919/9007199254740992), by norm_num⟩
  | 1 => ⟨((-23645973581/68719476736), (4145223201/34359738368)), (67/68719476736), by norm_num⟩
  | 2 => ⟨((7800384987/17179869184), (-1367435209/8589934592)), (23/17179869184), by norm_num⟩
  | 3 => ⟨((-13723775449/34359738368), (4811653215/34359738368)), (21/17179869184), by norm_num⟩
  | 4 => ⟨((9054457547/34359738368), (-3174557171/34359738368)), (29/34359738368), by norm_num⟩
  | 5 => ⟨((-4779046511/34359738368), (837783837/17179869184)), (63/137438953472), by norm_num⟩
  | 6 => ⟨((16816236965/274877906944), (-2947946101/137438953472)), (29/137438953472), by norm_num⟩
  | 7 => ⟨((-1584964765/68719476736), (8891198589/1099511627776)), (45/549755813888), by norm_num⟩
  | 8 => ⟨((16731251521/2199023255552), (-5866095701/2199023255552)), (61/2199023255552), by norm_num⟩
  | 9 => ⟨((-4906081329/2199023255552), (215013373/274877906944)), (37/4398046511104), by norm_num⟩
  | 10 => ⟨((10357943913/17592186044416), (-3631568755/17592186044416)), (5/2199023255552), by norm_num⟩
  | 11 => ⟨((-9940075565/70368744177664), (1742530571/35184372088832)), (79/140737488355328), by norm_num⟩
  | 12 => ⟨((17488286185/562949953421312), (-3065758717/281474976710656)), (9/70368744177664), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (-109815232561/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444728976208173/158456325028528675187087900672), (-259962128423/316912650057057350374175801344)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889907390446741/39614081257132168796771975168), (-292406766795/19807040628566084398385987584)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472423208316789/618970019642690137449562112), (-621238945891/2475880078570760549798248448)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13838743037951/1208925819614629174706176), (-621097882819/154742504910672534362390528)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193713918522431/1208925819614629174706176), (-582129430551/9671406556917033397649408)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((629463446857159/302231454903657293676544), (-63651683461/75557863725914323419136)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236002086014369/9444732965739290427392), (-413595573639/37778931862957161709568)), (1149/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297707980486841/4722366482869645213696), (-620147822279/4722366482869645213696)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621679911697933/590295810358705651712), (-852304457219/590295810358705651712)), (1185/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823764471985663/73786976294838206464), (-532391362835/36893488147419103232)), (5925/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822983112208335/9223372036854775808), (-299264774893/2305843009213693952)), (6667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594231778886659/1152921504606846976), (-1196033122261/1152921504606846976)), (1667/288230376151711744), by norm_num⟩
  | 5 => ⟨((74674757569197/9007199254740992), (-1045375933695/144115188075855872)), (5835/144115188075855872), by norm_num⟩
  | 4 => ⟨((745980398612697/18014398509481984), (-391440185305/9007199254740992)), (8755/36028797018963968), by norm_num⟩
  | 3 => ⟨((372415637349021/2251799813685248), (-976588498807/4503599627370496)), (10947/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228759678577089/4503599627370496), (-486788570463/562949953421312)), (21905/4503599627370496), by norm_num⟩
  | 1 => ⟨((554331434582171/562949953421312), (-2905720655249/1125899906842624)), (32887/2251799813685248), by norm_num⟩
  | 0 => ⟨((272899396603647/281474976710656), (-11503347150705/2251799813685248)), (65893/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((272899396603647/281474976710656), (-11503347150705/2251799813685248)), (251361855513762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2116621915812609/2251799813685248), (-11152879495845/1125899906842624)), (128445/2251799813685248), by norm_num⟩
  | 2 => ⟨((497334483330785/562949953421312), (-20966720950819/1125899906842624)), (244015/2251799813685248), by norm_num⟩
  | 3 => ⟨((439171698941439/562949953421312), (-74091654278279/2251799813685248)), (110059/562949953421312), by norm_num⟩
  | 4 => ⟨((1367998570060565/2251799813685248), (-115601600067711/2251799813685248)), (357925/1125899906842624), by norm_num⟩
  | 5 => ⟨((1650285559539753/4503599627370496), (-280918086284995/4503599627370496)), (943277/2251799813685248), by norm_num⟩
  | 6 => ⟨((1174406108727505/9007199254740992), (-411755128845987/9007199254740992)), (3235919/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-10300819509/536870912)), (1/536870912), by norm_num⟩, -3, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-272601259/134217728), (-21140227633/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((394904178710679/4503599627370496), (-879038259883605/9007199254740992)), (4330253/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4079514849/17179869184), (9080809541/34359738368)), (47/34359738368), by norm_num⟩
  | 2 => ⟨((11047531007/34359738368), (-3073911013/8589934592)), (33/17179869184), by norm_num⟩
  | 3 => ⟨((-9972422855/34359738368), (5549536891/17179869184)), (61/34359738368), by norm_num⟩
  | 4 => ⟨((13502910859/68719476736), (-15028424493/68719476736)), (85/68719476736), by norm_num⟩
  | 5 => ⟨((-14626624187/137438953472), (4069772797/34359738368)), (47/68719476736), by norm_num⟩
  | 6 => ⟨((13203210857/274877906944), (-3673716347/68719476736)), (87/274877906944), by norm_num⟩
  | 7 => ⟨((-10215702233/549755813888), (355307439/17179869184)), (69/549755813888), by norm_num⟩
  | 8 => ⟨((13832317243/2199023255552), (-7697523053/1099511627776)), (95/2199023255552), by norm_num⟩
  | 9 => ⟨((-4162067721/2199023255552), (4632284189/2199023255552)), (59/4398046511104), by norm_num⟩
  | 10 => ⟨((9016870663/17592186044416), (-1254445813/2199023255552)), (33/8796093022208), by norm_num⟩
  | 11 => ⟨((-8879323059/70368744177664), (77206869/549755813888)), (67/70368744177664), by norm_num⟩
  | 12 => ⟨((16030435063/562949953421312), (-8920749957/281474976710656)), (31/140737488355328), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (-1092650589739/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889417688561315/316912650057057350374175801344), (-323297043005/158456325028528675187087900672)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944908385041545/19807040628566084398385987584), (-727288977821/19807040628566084398385987584)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889596513477735/2475880078570760549798248448), (-193146109485/309485009821345068724781056)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771262749001999/154742504910672534362390528), (-772404385117/77371252455336267181195264)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549620968278287/9671406556917033397649408), (-1447875721971/9671406556917033397649408)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629423884401351/302231454903657293676544), (-633254441377/302231454903657293676544)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1887888030531005/75557863725914323419136), (-2057360251261/75557863725914323419136)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297611417727941/4722366482869645213696), (-771196679251/2361183241434822606848)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621547025003995/590295810358705651712), (-2119772771303/590295810358705651712)), (4747/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823598194533889/73786976294838206464), (-2648189697241/73786976294838206464)), (5935/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911397909008205/4611686018427387904), (-2977116218415/9223372036854775808)), (3339/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797022097634509/576460752303423488), (-743624216785/288230376151711744)), (6681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194631660726953/144115188075855872), (-649935231269/36028797018963968)), (731/18014398509481984), by norm_num⟩
  | 4 => ⟨((372928364861121/9007199254740992), (-3893731054107/36028797018963968)), (8777/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489352249532967/9007199254740992), (-607111214333/1125899906842624)), (10981/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228135715811523/4503599627370496), (-9683022940915/4503599627370496)), (21991/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216381455886783/2251799813685248), (-225748017233/35184372088832)), (16529/1125899906842624), by norm_num⟩
  | 0 => ⟨((2181273668638663/2251799813685248), (-28590476780651/2251799813685248)), (66409/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2181273668638663/2251799813685248), (-28590476780651/2251799813685248)), (253330239302825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2112593390061791/2251799813685248), (-13847512953071/562949953421312)), (65173/1125899906842624), by norm_num⟩
  | 2 => ⟨((990315113001517/1125899906842624), (-12991458723667/281474976710656)), (125495/1125899906842624), by norm_num⟩
  | 3 => ⟨((1737318866622153/2251799813685248), (-182831711214005/2251799813685248)), (116175/562949953421312), by norm_num⟩
  | 4 => ⟨((331384853968313/562949953421312), (-282118312097261/2251799813685248)), (792517/2251799813685248), by norm_num⟩
  | 5 => ⟨((1489887325523571/4503599627370496), (-664284525386007/4503599627370496)), (1131625/2251799813685248), by norm_num⟩
  | 6 => ⟨((394904178710679/4503599627370496), (-879038259883605/9007199254740992)), (4330253/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-21140227633/1073741824)), (1/536870912), by norm_num⟩, -3, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile016Terms1
