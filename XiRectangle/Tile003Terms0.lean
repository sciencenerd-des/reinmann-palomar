/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile003Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/640))
  have he : value ((3/4), (987/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-381061692393/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((-142898134647/274877906944), (-293834289369/274877906944)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((-381061692393/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((644069576382391/2251799813685248), (-2292658501537/4398046511104)), (5355/562949953421312), by norm_num⟩
  | 1 => ⟨((-27248230649/137438953472), (198643722041/549755813888)), (5/549755813888), by norm_num⟩
  | 2 => ⟨((151096273997/2199023255552), (-275378671737/2199023255552)), (9/2199023255552), by norm_num⟩
  | 3 => ⟨((-139642608419/8796093022208), (254503933201/8796093022208)), (5/4398046511104), by norm_num⟩
  | 4 => ⟨((193585760623/70368744177664), (-352817367479/70368744177664)), (17/70368744177664), by norm_num⟩
  | 5 => ⟨((-53673369669/140737488355328), (195643490817/281474976710656)), (11/281474976710656), by norm_num⟩
  | 6 => ⟨((99209452953/2251799813685248), (-45203244685/562949953421312)), (3/562949953421312), by norm_num⟩
  | 7 => ⟨((-78590574399/18014398509481984), (71617146527/9007199254740992)), (21/36028797018963968), by norm_num⟩
  | 8 => ⟨((108949670127/288230376151711744), (-49641223195/72057594037927936)), (17/288230376151711744), by norm_num⟩
  | 9 => ⟨((-134254500749/4611686018427387904), (244683903269/4611686018427387904)), (23/4611686018427387904), by norm_num⟩
  | 10 => ⟨((148893005875/73786976294838206464), (-271363132287/73786976294838206464)), (27/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-75058012529/590295810358705651712), (136796065493/590295810358705651712)), (29/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((69368333017/9444732965739290427392), (-252852818955/18889465931478580854784)), (29/18889465931478580854784), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395824647727665/2535301200456458802993406410752), (-1392443550401/10141204801825835211973625643008)), (11/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781167481464039/633825300114114700748351602688), (-1652112895319/633825300114114700748351602688)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892440053199373/39614081257132168796771975168), (-1858538202669/39614081257132168796771975168)), (7/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892383347278447/2475880078570760549798248448), (-987295927791/1237940039285380274899124224)), (7/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((887024563892421/77371252455336267181195264), (-987236871041/77371252455336267181195264)), (15/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552232714996791/9671406556917033397649408), (-1850943633577/9671406556917033397649408)), (7/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261132563865287/604462909807314587353088), (-1619450175219/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945799958223955/37778931862957161709568), (-2631371204801/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300394539521193/4722366482869645213696), (-1973322480293/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625372529718575/590295810358705651712), (-678245941753/147573952589676412928)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828378144318475/73786976294838206464), (-847681928047/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1828170607091535/9223372036854775808), (-3813878379819/9223372036854775808)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799707833783101/576460752303423488), (-1906507716405/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199327969347977/144115188075855872), (-3335417583317/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((1498750467438213/36028797018963968), (-1250296068075/9007199254740992)), (9/9007199254740992), by norm_num⟩
  | 3 => ⟨((749067736574419/4503599627370496), (-1562020268287/2251799813685248)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((140353943310673/281474976710656), (-3121490500751/1125899906842624)), (11/562949953421312), by norm_num⟩
  | 1 => ⟨((1121287491563705/1125899906842624), (-9351717244581/1125899906842624)), (33/562949953421312), by norm_num⟩
  | 0 => ⟨((34894865454809/35184372088832), (-18652393141109/1125899906842624)), (131/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((34894865454809/35184372088832), (-18652393141109/1125899906842624)), (499729636764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((276784675752751/281474976710656), (-18498916150213/562949953421312)), (265/1125899906842624), by norm_num⟩
  | 2 => ⟨((135934293611357/140737488355328), (-72762652911451/1125899906842624)), (135/281474976710656), by norm_num⟩
  | 3 => ⟨((1045657832176587/1125899906842624), (-70279354423565/562949953421312)), (557/562949953421312), by norm_num⟩
  | 4 => ⟨((476793516383841/562949953421312), (-130541191000537/562949953421312)), (2349/1125899906842624), by norm_num⟩
  | 5 => ⟨((747103906625417/1125899906842624), (-110562569748539/281474976710656)), (5069/1125899906842624), by norm_num⟩
  | 6 => ⟨((644069576382391/2251799813685248), (-2292658501537/4398046511104)), (5355/562949953421312), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-142898134647/274877906944), (-293834289369/274877906944)), (1/137438953472), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-28311023105/34359738368), (-116429082519/68719476736)), (3/137438953472), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-243318765602177/4503599627370496), (-1960649771488837/4503599627370496)), (59281/2251799813685248), by norm_num⟩
  | 1 => ⟨((32630979731/549755813888), (65734678123/137438953472)), (9/274877906944), by norm_num⟩
  | 2 => ⟨((-8962198831/274877906944), (-144433850355/549755813888)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((52511902769/4398046511104), (211569070533/2199023255552)), (35/4398046511104), by norm_num⟩
  | 4 => ⟨((-57690221683/17592186044416), (-464864761579/17592186044416)), (41/17592186044416), by norm_num⟩
  | 5 => ⟨((25351674591/35184372088832), (12767653491/2199023255552)), (39/70368744177664), by norm_num⟩
  | 6 => ⟨((-37135548325/281474976710656), (-74809072121/70368744177664)), (31/281474976710656), by norm_num⟩
  | 7 => ⟨((728528031/35184372088832), (733805053/4398046511104)), (41/2251799813685248), by norm_num⟩
  | 8 => ⟨((-1600739695/562949953421312), (-412757631341/18014398509481984)), (3/1125899906842624), by norm_num⟩
  | 9 => ⟨((50022180975/144115188075855872), (403076094251/144115188075855872)), (25/72057594037927936), by norm_num⟩
  | 10 => ⟨((-10990996545/288230376151711744), (-177129740165/576460752303423488)), (23/576460752303423488), by norm_num⟩
  | 11 => ⟨((1097713079/288230376151711744), (283050049795/9223372036854775808)), (39/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-51454339329/147573952589676412928), (-103654087671/36893488147419103232)), (59/147573952589676412928), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197862808528795/1267650600228229401496703205376), (-2206970811757/10141204801825835211973625643008)), (15/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445173851912099/158456325028528675187087900672), (-2617226171109/633825300114114700748351602688)), (35/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891908871353895/39614081257132168796771975168), (-2944155708307/39614081257132168796771975168)), (39/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891818842775707/2475880078570760549798248448), (-1563950817603/1237940039285380274899124224)), (21/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443371121016635/38685626227668133590597632), (-390950603385/19342813113834066795298816)), (41/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775851606825351/4835703278458516698824704), (-1465907075417/4835703278458516698824704)), (39/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630334551195327/302231454903657293676544), (-2565021989523/604462909807314587353088)), (17/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890846514567283/75557863725914323419136), (-4167569334123/75557863725914323419136)), (55/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299829245884069/4722366482869645213696), (-781289872165/1180591620717411303424)), (21/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624594857601659/590295810358705651712), (-4296253269009/590295810358705651712)), (57/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827405464565245/73786976294838206464), (-2684527460197/36893488147419103232)), (35/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228384441547139/1152921504606846976), (-3019225896903/4611686018427387904)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((1598319581438107/1152921504606846976), (-3018141376729/576460752303423488)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((1198367757625257/144115188075855872), (-2639653413297/72057594037927936)), (35/72057594037927936), by norm_num⟩
  | 4 => ⟨((748653940415687/18014398509481984), (-7914078047723/36028797018963968)), (13/4503599627370496), by norm_num⟩
  | 3 => ⟨((748164138709901/4503599627370496), (-4942025711919/4503599627370496)), (65/4503599627370496), by norm_num⟩
  | 2 => ⟨((560509211841743/1125899906842624), (-9871227648021/2251799813685248)), (131/2251799813685248), by norm_num⟩
  | 1 => ⟨((559276523933737/562949953421312), (-7387383075657/562949953421312)), (49/281474976710656), by norm_num⟩
  | 0 => ⟨((555554059054589/562949953421312), (-29421136700939/1125899906842624)), (395/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((555554059054589/562949953421312), (-29421136700939/1125899906842624)), (1506809714889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1095741850004245/1125899906842624), (-29034609234569/562949953421312)), (801/1125899906842624), by norm_num⟩
  | 2 => ⟨((1063396630944443/1125899906842624), (-3532111984765/35184372088832)), (1643/1125899906842624), by norm_num⟩
  | 3 => ⟨((496508238998193/562949953421312), (-106752963367785/562949953421312)), (3435/1125899906842624), by norm_num⟩
  | 4 => ⟨((835329090184029/1125899906842624), (-94153530926593/281474976710656)), (7363/1125899906842624), by norm_num⟩
  | 5 => ⟨((987541587584955/2251799813685248), (-1117672117722531/2251799813685248)), (3963/281474976710656), by norm_num⟩
  | 6 => ⟨((-243318765602177/4503599627370496), (-1960649771488837/4503599627370496)), (59281/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/34359738368), (-116429082519/68719476736)), (3/137438953472), by norm_num⟩, 0, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-381061692393/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-142898134647/137438953472), (-293834289369/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-381061692393/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-427692296136501/2251799813685248), (-1342988607461323/4503599627370496)), (69417/4503599627370496), by norm_num⟩
  | 1 => ⟨((72376393851/274877906944), (227267765329/549755813888)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((-50167493337/274877906944), (-78765005385/274877906944)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((185458434999/2199023255552), (291177287517/2199023255552)), (11/1099511627776), by norm_num⟩
  | 4 => ⟨((-128549991331/4398046511104), (-100914357943/2199023255552)), (17/4398046511104), by norm_num⟩
  | 5 => ⟨((142566502483/17592186044416), (55958802149/4398046511104)), (21/17592186044416), by norm_num⟩
  | 6 => ⟨((-131759425651/70368744177664), (-206867658331/70368744177664)), (21/70368744177664), by norm_num⟩
  | 7 => ⟨((6523476743/17592186044416), (163873981853/281474976710656)), (9/140737488355328), by norm_num⟩
  | 8 => ⟨((-36173836095/562949953421312), (-227177576977/2251799813685248)), (27/2251799813685248), by norm_num⟩
  | 9 => ⟨((178302524439/18014398509481984), (2187048569/140737488355328)), (9/4503599627370496), by norm_num⟩
  | 10 => ⟨((-197743827363/144115188075855872), (-310465853307/144115188075855872)), (21/72057594037927936), by norm_num⟩
  | 11 => ⟨((99684055571/576460752303423488), (78254011229/288230376151711744)), (45/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-92127629421/4611686018427387904), (-289288252005/9223372036854775808)), (11/2305843009213693952), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414715939/10141204801825835211973625643008), (-2784887100803/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((445090001334489/158456325028528675187087900672), (-206337384317/39614081257132168796771975168)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891531448745581/39614081257132168796771975168), (-3713715936387/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891417709718545/2475880078570760549798248448), (-3945403051243/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886541607175385/77371252455336267181195264), (-246558146299/9671406556917033397649408)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551326878168331/9671406556917033397649408), (-1848934953919/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260339663805115/604462909807314587353088), (-1617566923477/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890310905100057/75557863725914323419136), (-5256150570939/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299427301170013/4722366482869645213696), (-1970644331715/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812020898918849/295147905179352825856), (-169310385635/18446744073709551616)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913356780891023/36893488147419103232), (-6770405820307/73786976294838206464)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1826296347855035/9223372036854775808), (-7613942940231/9223372036854775808)), (27/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399384851500479/288230376151711744), (-1902621957959/288230376151711744)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197683991332905/144115188075855872), (-1663822258943/36028797018963968)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496280010801659/36028797018963968), (-9975155879067/36028797018963968)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495039565049221/9007199254740992), (-3113832338663/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 2 => ⟨((1119723921454277/2251799813685248), (-12434897054265/2251799813685248)), (11/281474976710656), by norm_num⟩
  | 1 => ⟨((279149224549703/281474976710656), (-18601233430013/1125899906842624)), (33/281474976710656), by norm_num⟩
  | 0 => ⟨((276784675752751/281474976710656), (-18498916150213/562949953421312)), (133/562949953421312), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276784675752751/281474976710656), (-18498916150213/562949953421312)), (507356883811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((135934293611357/140737488355328), (-72762652911451/1125899906842624)), (271/562949953421312), by norm_num⟩
  | 2 => ⟨((1045657832176587/1125899906842624), (-70279354423565/562949953421312)), (559/562949953421312), by norm_num⟩
  | 3 => ⟨((476793516383841/562949953421312), (-130541191000537/562949953421312)), (2357/1125899906842624), by norm_num⟩
  | 4 => ⟨((747103906625417/1125899906842624), (-110562569748539/281474976710656)), (5087/1125899906842624), by norm_num⟩
  | 5 => ⟨((644069576382391/2251799813685248), (-2292658501537/4398046511104)), (2687/281474976710656), by norm_num⟩
  | 6 => ⟨((-427692296136501/2251799813685248), (-1342988607461323/4503599627370496)), (69417/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-142898134647/137438953472), (-293834289369/137438953472)), (1/68719476736), by norm_num⟩, 0, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-221199462363/137438953472), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-41474899193/34359738368), (-341131045863/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-221199462363/137438953472), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-532207352104511/2251799813685248), (-412654577801675/2251799813685248)), (29675/2251799813685248), by norm_num⟩
  | 1 => ⟨((209119797303/549755813888), (40536005997/137438953472)), (13/549755813888), by norm_num⟩
  | 2 => ⟨((-84141332505/274877906944), (-32620092435/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((5642510439/34359738368), (140000035925/1099511627776)), (15/1099511627776), by norm_num⟩
  | 4 => ⟨((-145300323549/2199023255552), (-28165170695/549755813888)), (27/4398046511104), by norm_num⟩
  | 5 => ⟨((187081479527/8796093022208), (145056299285/8796093022208)), (19/8796093022208), by norm_num⟩
  | 6 => ⟨((-100365341955/17592186044416), (-38909851251/8796093022208)), (11/17592186044416), by norm_num⟩
  | 7 => ⟨((23075969491/17592186044416), (143138262333/140737488355328)), (11/70368744177664), by norm_num⟩
  | 8 => ⟨((-37139340165/140737488355328), (-230372146119/1125899906842624)), (19/562949953421312), by norm_num⟩
  | 9 => ⟨((53131966315/1125899906842624), (10299157387/281474976710656)), (29/4503599627370496), by norm_num⟩
  | 10 => ⟨((-136820161519/18014398509481984), (-212170935869/36028797018963968)), (39/36028797018963968), by norm_num⟩
  | 11 => ⟨((160148040097/144115188075855872), (62086536019/72057594037927936)), (25/144115188075855872), by norm_num⟩
  | 12 => ⟨((-171832218223/1152921504606846976), (-133232566561/1152921504606846976)), (7/288230376151711744), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673669/10141204801825835211973625643008), (-404144225027/1267650600228229401496703205376)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111256223987177/39614081257132168796771975168), (-3831747734969/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891238387216503/39614081257132168796771975168), (-1077558571005/9903520314283042199192993792)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945553109192835/1237940039285380274899124224), (-2289528790121/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772771595456343/154742504910672534362390528), (-1144605083265/38685626227668133590597632)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551034600006027/9671406556917033397649408), (-536448992203/1208925819614629174706176)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630041892530139/302231454903657293676544), (-3754465765111/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889894848557037/75557863725914323419136), (-95308391205/1180591620717411303424)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324778759270443/1180591620717411303424), (-4573691557713/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811806037433469/295147905179352825856), (-3143509969383/295147905179352825856)), (39/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228271983620387/9223372036854775808), (-7856065609281/73786976294838206464)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((456422675812489/2305843009213693952), (-2208586970171/2305843009213693952)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596932837796157/1152921504606846976), (-8829689538045/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197152207341307/144115188075855872), (-7720736436971/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495480266787051/36028797018963968), (-1446327209059/4503599627370496)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((373509069642077/2251799813685248), (-7222456398925/4503599627370496)), (11/1125899906842624), by norm_num⟩
  | 2 => ⟨((1118715250434685/2251799813685248), (-14417359837373/2251799813685248)), (11/281474976710656), by norm_num⟩
  | 1 => ⟨((557535259149983/562949953421312), (-10778554417929/562949953421312)), (33/281474976710656), by norm_num⟩
  | 0 => ⟨((552016488532091/562949953421312), (-42838207315893/1125899906842624)), (267/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((552016488532091/562949953421312), (-42838207315893/1125899906842624)), (1018528464889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1080960834122601/1125899906842624), (-42006214999775/562949953421312)), (545/1125899906842624), by norm_num⟩
  | 2 => ⟨((1031546613916667/1125899906842624), (-10082395630493/70368744177664)), (1129/1125899906842624), by norm_num⟩
  | 3 => ⟨((460993382605233/562949953421312), (-147799441276721/562949953421312)), (2393/1125899906842624), by norm_num⟩
  | 4 => ⟨((677396712817227/1125899906842624), (-121031299438313/281474976710656)), (5177/1125899906842624), by norm_num⟩
  | 5 => ⟨((398772747153869/2251799813685248), (-291273509800443/562949953421312)), (5341/562949953421312), by norm_num⟩
  | 6 => ⟨((-532207352104511/2251799813685248), (-412654577801675/2251799813685248)), (29675/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/34359738368), (-341131045863/137438953472)), (1/68719476736), by norm_num⟩, 0, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-492515092649/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-2885830621/2147483648), (-189887654861/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-492515092649/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-272915645888121/1125899906842624), (-433953889468587/4503599627370496)), (25183/1125899906842624), by norm_num⟩
  | 1 => ⟨((7461535535/17179869184), (2966083491/17179869184)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((-213908431197/549755813888), (-10629016363/68719476736)), (23/549755813888), by norm_num⟩
  | 3 => ⟨((127757485715/549755813888), (101571417157/1099511627776)), (29/1099511627776), by norm_num⟩
  | 4 => ⟨((-228910684795/2199023255552), (-90995774247/2199023255552)), (27/2199023255552), by norm_num⟩
  | 5 => ⟨((328122309671/8796093022208), (65217016067/4398046511104)), (41/8796093022208), by norm_num⟩
  | 6 => ⟨((-391944170279/35184372088832), (-155804274791/35184372088832)), (51/35184372088832), by norm_num⟩
  | 7 => ⟨((200648479573/70368744177664), (77891681/68719476736)), (7/17592186044416), by norm_num⟩
  | 8 => ⟨((-359513813261/562949953421312), (-71456336387/281474976710656)), (13/140737488355328), by norm_num⟩
  | 9 => ⟨((71573586581/562949953421312), (28451681635/562949953421312)), (43/2251799813685248), by norm_num⟩
  | 10 => ⟨((-205188242405/9007199254740992), (-10195713997/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 11 => ⟨((267380346403/72057594037927936), (106288099489/72057594037927936)), (43/72057594037927936), by norm_num⟩
  | 12 => ⟨((-159693755851/288230376151711744), (-126961805817/576460752303423488)), (53/576460752303423488), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (-1799707181077/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779886633141549/633825300114114700748351602688), (-4264857360575/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945499368951359/19807040628566084398385987584), (-4797366467739/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236356435735273/309485009821345068724781056), (-2548249933197/1237940039285380274899124224)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772516744790867/154742504910672534362390528), (-2547854975977/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550795552049855/9671406556917033397649408), (-597048590983/1208925819614629174706176)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157484311592785/75557863725914323419136), (-2089250354121/302231454903657293676544)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889554513711611/75557863725914323419136), (-6788489559899/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298859580687039/4722366482869645213696), (-5089989678415/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623260489177585/590295810358705651712), (-3498248540723/295147905179352825856)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912867943917413/36893488147419103232), (-8742262734299/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825195039475449/9223372036854775808), (-2457606655587/2305843009213693952)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596436319478519/1152921504606846976), (-9824651653863/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((149589599350925/18014398509481984), (-4295035805939/72057594037927936)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((186853154482417/4503599627370496), (-804506619419/2251799813685248)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((746607078460565/4503599627370496), (-502105314673/281474976710656)), (175/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117888155757537/2251799813685248), (-1002075463637/140737488355328)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((556908768104613/562949953421312), (-5850668517/274877906944)), (265/1125899906842624), by norm_num⟩
  | 0 => ⟨((1101478206938141/1125899906842624), (-11896598563109/281474976710656)), (67/140737488355328), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1101478206938141/1125899906842624), (-11896598563109/281474976710656)), (255585253667787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1075574985024831/1125899906842624), (-93108412030717/1125899906842624)), (1095/1125899906842624), by norm_num⟩
  | 2 => ⟨((509899843246357/562949953421312), (-177893395792993/1125899906842624)), (1137/562949953421312), by norm_num⟩
  | 3 => ⟨((895590570863081/1125899906842624), (-322258893808003/1125899906842624)), (4839/1125899906842624), by norm_num⟩
  | 4 => ⟨((155038576639233/281474976710656), (-512677947510579/1125899906842624)), (10469/1125899906842624), by norm_num⟩
  | 5 => ⟨((216276216629029/2251799813685248), (-564773893475231/1125899906842624)), (42135/2251799813685248), by norm_num⟩
  | 6 => ⟨((-272915645888121/1125899906842624), (-433953889468587/4503599627370496)), (25183/1125899906842624), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-189887654861/68719476736)), (1/34359738368), by norm_num⟩, 0, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-534887708873/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-50145722707/34359738368), (-25778035579/8589934592)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-534887708873/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-518080533777057/2251799813685248), (-9168011149053/281474976710656)), (42779/4503599627370496), by norm_num⟩
  | 1 => ⟨((123063741297/274877906944), (8710998995/137438953472)), (3/137438953472), by norm_num⟩
  | 2 => ⟨((-478941966341/1099511627776), (-67803285411/1099511627776)), (25/1099511627776), by norm_num⟩
  | 3 => ⟨((155329672185/549755813888), (43979700407/1099511627776)), (9/549755813888), by norm_num⟩
  | 4 => ⟨((-151128792777/1099511627776), (-42790272687/2199023255552)), (19/2199023255552), by norm_num⟩
  | 5 => ⟨((235266441343/4398046511104), (33306410361/4398046511104)), (1/274877906944), by norm_num⟩
  | 6 => ⟨((-305204903961/17592186044416), (-10801880325/4398046511104)), (11/8796093022208), by norm_num⟩
  | 7 => ⟨((84843045737/17592186044416), (48044545265/70368744177664)), (13/35184372088832), by norm_num⟩
  | 8 => ⟨((-330193887553/281474976710656), (-46745184119/281474976710656)), (27/281474976710656), by norm_num⟩
  | 9 => ⟨((142783919321/562949953421312), (40427523643/1125899906842624)), (25/1125899906842624), by norm_num⟩
  | 10 => ⟨((-444551484365/9007199254740992), (-31467331423/4503599627370496)), (41/9007199254740992), by norm_num⟩
  | 11 => ⟨((314566270983/36028797018963968), (22266399847/18014398509481984)), (31/36028797018963968), by norm_num⟩
  | 12 => ⟨((-408078466171/288230376151711744), (-57771217927/288230376151711744)), (21/144115188075855872), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693182021/10141204801825835211973625643008), (-977270813725/2535301200456458802993406410752)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889853233060549/316912650057057350374175801344), (-4630893701943/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890795976720683/39614081257132168796771975168), (-5209049246103/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945317977288427/1237940039285380274899124224), (-5533786756561/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772301103829045/154742504910672534362390528), (-2766427483605/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550593272229803/9671406556917033397649408), (-5186061418779/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259697381584391/604462909807314587353088), (-4536813530721/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236158311275951/9444732965739290427392), (-7370465135167/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40582605394983/147573952589676412928), (-2763111949523/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811481447045249/295147905179352825856), (-7595916927475/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825363431161077/73786976294838206464), (-9490934085369/73786976294838206464)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1824775390512777/9223372036854775808), (-10671851904557/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596015878258045/1152921504606846976), (-1333129887619/144115188075855872)), (27/576460752303423488), by norm_num⟩
  | 5 => ⟨((598174009926059/72057594037927936), (-9324242585315/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494270301655475/36028797018963968), (-3492756275117/9007199254740992)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492517402067825/9007199254740992), (-17436926197235/9007199254740992)), (11/1125899906842624), by norm_num⟩
  | 2 => ⟨((279296699309497/562949953421312), (-17396619057897/2251799813685248)), (89/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112754083609431/1125899906842624), (-12997038310805/562949953421312)), (133/1125899906842624), by norm_num⟩
  | 0 => ⟨((4294164874219/4398046511104), (-25792125068973/562949953421312)), (269/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((4294164874219/4398046511104), (-25792125068973/562949953421312)), (1026157859420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1070977265667373/1125899906842624), (-100731665500141/1125899906842624)), (551/1125899906842624), by norm_num⟩
  | 2 => ⟨((1009721582027661/1125899906842624), (-191635727168669/1125899906842624)), (1147/1125899906842624), by norm_num⟩
  | 3 => ⟨((872913671376965/1125899906842624), (-171861395878787/562949953421312)), (2449/1125899906842624), by norm_num⟩
  | 4 => ⟨((1143677011056339/2251799813685248), (-532978681791441/1125899906842624)), (5293/1125899906842624), by norm_num⟩
  | 5 => ⟨((76264330247519/2251799813685248), (-541394010287617/1125899906842624)), (20777/2251799813685248), by norm_num⟩
  | 6 => ⟨((-518080533777057/2251799813685248), (-9168011149053/281474976710656)), (42779/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50145722707/34359738368), (-25778035579/8589934592)), (1/68719476736), by norm_num⟩, 0, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-285796269295/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-53586800493/34359738368), (-220375717027/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-285796269295/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-472373803878717/2251799813685248), (15444038534943/1125899906842624)), (75647/4503599627370496), by norm_num⟩
  | 1 => ⟨((479625835443/1099511627776), (-31362280567/1099511627776)), (41/1099511627776), by norm_num⟩
  | 2 => ⟨((-249338471671/549755813888), (16304007263/549755813888)), (23/549755813888), by norm_num⟩
  | 3 => ⟨((43207064661/137438953472), (-5650538333/274877906944)), (17/549755813888), by norm_num⟩
  | 4 => ⟨((-359386260601/2199023255552), (23499928285/2199023255552)), (37/2199023255552), by norm_num⟩
  | 5 => ⟨((298929087921/4398046511104), (-19546690841/4398046511104)), (33/4398046511104), by norm_num⟩
  | 6 => ⟨((-12950115905/549755813888), (27097467291/17592186044416)), (3/1099511627776), by norm_num⟩
  | 7 => ⟨((492416164251/70368744177664), (-32198628091/70368744177664)), (15/17592186044416), by norm_num⟩
  | 8 => ⟨((-255987656935/140737488355328), (33477582419/281474976710656)), (65/281474976710656), by norm_num⟩
  | 9 => ⟨((236582830217/562949953421312), (-30939855821/1125899906842624)), (63/1125899906842624), by norm_num⟩
  | 10 => ⟨((-196784066081/2251799813685248), (25735048595/4503599627370496)), (55/4503599627370496), by norm_num⟩
  | 11 => ⟨((297600699455/18014398509481984), (-19459828773/18014398509481984)), (11/4503599627370496), by norm_num⟩
  | 12 => ⟨((-3223141965/1125899906842624), (1686065681/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521203/10141204801825835211973625643008), (4007219732677/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444887838350703/158456325028528675187087900672), (2373183606527/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945310733860599/19807040628566084398385987584), (2669445972833/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890450524714255/2475880078570760549798248448), (5671665890579/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110757228638427/9671406556917033397649408), (5670645520113/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550419400278021/9671406556917033397649408), (5315145958831/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629772613495827/302231454903657293676544), (4649668415819/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889019207917615/75557863725914323419136), (7553677943219/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298457883843397/4722366482869645213696), (707934900773/590295810358705651712)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405676950801543/147573952589676412928), (7784392302593/590295810358705651712)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825044502243403/73786976294838206464), (1215769050927/9223372036854775808)), (95/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912208253140295/4611686018427387904), (10935955840327/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595656883432067/1152921504606846976), (5464248732221/576460752303423488)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196033776205637/144115188075855872), (9554042761979/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((186724836618077/4503599627370496), (7157137265397/18014398509481984)), (35/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491927472484721/9007199254740992), (17863451170179/9007199254740992)), (175/9007199254740992), by norm_num⟩
  | 2 => ⟨((279149063384589/562949953421312), (17819343130879/2251799813685248)), (11/140737488355328), by norm_num⟩
  | 1 => ⟨((555933390686719/562949953421312), (6654668937283/281474976710656)), (265/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097525947139425/1125899906842624), (52795593181619/1125899906842624)), (269/562949953421312), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1097525947139425/1125899906842624), (52795593181619/1125899906842624)), (1026155711936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1067391357509789/1125899906842624), (102930168231275/1125899906842624)), (275/281474976710656), by norm_num⟩
  | 2 => ⟨((501256676412641/562949953421312), (97581295929931/562949953421312)), (143/70368744177664), by norm_num⟩
  | 3 => ⟨((858819313737351/1125899906842624), (86887432498407/281474976710656)), (4869/1125899906842624), by norm_num⟩
  | 4 => ⟨((1095621014054961/2251799813685248), (1060422578556801/2251799813685248)), (20869/2251799813685248), by norm_num⟩
  | 5 => ⟨((67403293014371/4503599627370496), (515952285715739/1125899906842624)), (79927/4503599627370496), by norm_num⟩
  | 6 => ⟨((-472373803878717/2251799813685248), (15444038534943/1125899906842624)), (75647/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-53586800493/34359738368), (-220375717027/68719476736)), (1/34359738368), by norm_num⟩, -1, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile003Terms0
