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
namespace Reinmann.XiRectangle.Tile028Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨28,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7473/640))
  have he : value ((7/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-516086359/268435456), (-1721747035/67108864)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((570434635041421/4503599627370496), (-658209856180433/9007199254740992)), (23627107/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1195309639/4294967296), (689618527/4294967296)), (51/8589934592), by norm_num⟩
  | 2 => ⟨((5252727433/17179869184), (-3030493553/17179869184)), (115/17179869184), by norm_num⟩
  | 3 => ⟨((-3847140605/17179869184), (2219558305/17179869184)), (87/17179869184), by norm_num⟩
  | 4 => ⟨((4226515945/34359738368), (-2438434029/34359738368)), (49/17179869184), by norm_num⟩
  | 5 => ⟨((-928660471/17179869184), (267889359/8589934592)), (89/68719476736), by norm_num⟩
  | 6 => ⟨((680158537/34359738368), (-3139269779/274877906944)), (133/274877906944), by norm_num⟩
  | 7 => ⟨((-3415910981/549755813888), (985382959/274877906944)), (43/274877906944), by norm_num⟩
  | 8 => ⟨((3752761781/2199023255552), (-270638457/274877906944)), (97/2199023255552), by norm_num⟩
  | 9 => ⟨((-916184491/2199023255552), (1057161723/4398046511104)), (97/8796093022208), by norm_num⟩
  | 10 => ⟨((1610450465/17592186044416), (-58070543/1099511627776)), (87/35184372088832), by norm_num⟩
  | 11 => ⟨((-2573470067/140737488355328), (2969460929/281474976710656)), (71/140737488355328), by norm_num⟩
  | 12 => ⟨((58900955/17592186044416), (-271857189/140737488355328)), (53/562949953421312), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403062135/10141204801825835211973625643008), (-681642184993/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779003159328117/633825300114114700748351602688), (-201722628239/158456325028528675187087900672)), (17303/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890005523355787/39614081257132168796771975168), (-907598883675/39614081257132168796771975168)), (19467/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472449265926401/618970019642690137449562112), (-964134707047/2475880078570760549798248448)), (20685/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110716456191711/9671406556917033397649408), (-963922032459/154742504910672534362390528)), (10343/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549808983775623/9671406556917033397649408), (-451725501741/4835703278458516698824704)), (19395/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39344133817361/18889465931478580854784), (-790293799013/604462909807314587353088)), (16971/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888155364301675/75557863725914323419136), (-1283804148841/75557863725914323419136)), (27581/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324452979410685/1180591620717411303424), (-481241450607/2361183241434822606848)), (1293/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621822711642423/590295810358705651712), (-661406343695/295147905179352825856)), (28449/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823942801587755/73786976294838206464), (-1652614414051/73786976294838206464)), (35567/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455795874758577/2305843009213693952), (-928976276409/4611686018427387904)), (10005/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797215936789917/576460752303423488), (-1856405459393/1152921504606846976)), (40029/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149371359472257/18014398509481984), (-50706749811/4503599627370496)), (8759/36028797018963968), by norm_num⟩
  | 4 => ⟨((46631946063073/1125899906842624), (-1215225331609/18014398509481984)), (26287/18014398509481984), by norm_num⟩
  | 3 => ⟨((93124265710283/562949953421312), (-3031994529681/9007199254740992)), (65753/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114703830413415/2251799813685248), (-755727587207/562949953421312)), (131615/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218289193720739/2251799813685248), (-4511721499223/1125899906842624)), (197697/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185088228309807/2251799813685248), (-4466632194793/562949953421312)), (24781/140737488355328), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2185088228309807/2251799813685248), (-4466632194793/562949953421312)), (94532013476324037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2120211274391203/2251799813685248), (-34674433738615/2251799813685248)), (48487/140737488355328), by norm_num⟩
  | 2 => ⟨((1995778445485141/2251799813685248), (-65296324210477/2251799813685248)), (1484807/2251799813685248), by norm_num⟩
  | 3 => ⟨((441743085833633/562949953421312), (-115744743948091/2251799813685248)), (679523/562949953421312), by norm_num⟩
  | 4 => ⟨((1380582055946497/2251799813685248), (-45412065539677/562949953421312)), (1136291/562949953421312), by norm_num⟩
  | 5 => ⟨((1663567703197247/4503599627370496), (-222737678283893/2251799813685248)), (3153297/1125899906842624), by norm_num⟩
  | 6 => ⟨((570434635041421/4503599627370496), (-658209856180433/9007199254740992)), (23627107/9007199254740992), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516086359/268435456), (-1721747035/67108864)), (3/268435456), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-67604193/33554432), (-225538453/8388608)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-218276191327739/9007199254740992), (-1181129613940791/9007199254740992)), (37984307/9007199254740992), by norm_num⟩
  | 1 => ⟨((958632477/17179869184), (5187323459/17179869184)), (169/17179869184), by norm_num⟩
  | 2 => ⟨((-551833213/8589934592), (-2986063417/8589934592)), (197/17179869184), by norm_num⟩
  | 3 => ⟨((847095287/17179869184), (1145944185/4294967296)), (153/17179869184), by norm_num⟩
  | 4 => ⟨((-487627245/17179869184), (-5277267995/34359738368)), (89/17179869184), by norm_num⟩
  | 5 => ⟨((224560645/17179869184), (2430271723/34359738368)), (83/34359738368), by norm_num⟩
  | 6 => ⟨((-344713329/68719476736), (-3730604961/137438953472)), (129/137438953472), by norm_num⟩
  | 7 => ⟨((453561013/274877906944), (613573955/68719476736)), (43/137438953472), by norm_num⟩
  | 8 => ⟨((-1044362827/2199023255552), (-5651224969/2199023255552)), (201/2199023255552), by norm_num⟩
  | 9 => ⟨((534385395/4398046511104), (5783300609/8796093022208)), (13/549755813888), by norm_num⟩
  | 10 => ⟨((-984374275/35184372088832), (-1331654177/8796093022208)), (97/17592186044416), by norm_num⟩
  | 11 => ⟨((824220193/140737488355328), (4459995719/140737488355328)), (41/35184372088832), by norm_num⟩
  | 12 => ⟨((-1265224753/1125899906842624), (-3423173219/562949953421312)), (127/562949953421312), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314710245/10141204801825835211973625643008), (-2284178403013/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222357181621975/79228162514264337593543950336), (-2703473424391/633825300114114700748351602688)), (8669/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472460357416037/9903520314283042199192993792), (-3040865655037/39614081257132168796771975168)), (19509/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944811243189627/1237940039285380274899124224), (-3230255110299/2475880078570760549798248448)), (5183/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771288465708867/154742504910672534362390528), (-1614753775885/77371252455336267181195264)), (20735/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549644805649755/9671406556917033397649408), (-378358654059/1208925819614629174706176)), (4861/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258868354647841/604462909807314587353088), (-661929171897/151115727451828646838272)), (8509/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943960486598583/37778931862957161709568), (-4301051510757/75557863725914323419136)), (13831/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297635679457401/4722366482869645213696), (-3224486978475/4722366482869645213696)), (20755/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405394915514769/147573952589676412928), (-4431555229033/590295810358705651712)), (28549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227954738489283/9223372036854775808), (-1384068481387/18446744073709551616)), (4463/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911419504316473/4611686018427387904), (-3111975800753/4611686018427387904)), (40191/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594085530367887/1152921504606846976), (-6218509400953/1152921504606846976)), (20111/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194665745810981/144115188075855872), (-2717539034283/72057594037927936)), (8807/36028797018963968), by norm_num⟩
  | 4 => ⟨((372940107906159/9007199254740992), (-1017549228701/4503599627370496)), (52911/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489403717005241/9007199254740992), (-10154128639121/9007199254740992)), (16565/2251799813685248), by norm_num⟩
  | 2 => ⟨((2228217004392037/4503599627370496), (-20244274592387/4503599627370496)), (8305/281474976710656), by norm_num⟩
  | 1 => ⟨((2216449611013527/2251799813685248), (-15103416895305/1125899906842624)), (100115/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090598444601653/1125899906842624), (-59777624596191/2251799813685248)), (101027/562949953421312), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090598444601653/1125899906842624), (-59777624596191/2251799813685248)), (385387422801780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1055610378013009/1125899906842624), (-115806714274291/2251799813685248)), (804331/2251799813685248), by norm_num⟩
  | 2 => ⟨((1973462231676521/2251799813685248), (-108576942487141/1125899906842624)), (795483/1125899906842624), by norm_num⟩
  | 3 => ⟨((1708587658064365/2251799813685248), (-380624412395901/2251799813685248)), (3095477/2251799813685248), by norm_num⟩
  | 4 => ⟨((154009962670573/281474976710656), (-577609225673859/2251799813685248)), (5743947/2251799813685248), by norm_num⟩
  | 5 => ⟨((131493479763721/562949953421312), (-316040794545137/1125899906842624)), (577025/140737488355328), by norm_num⟩
  | 6 => ⟨((-218276191327739/9007199254740992), (-1181129613940791/9007199254740992)), (37984307/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67604193/33554432), (-225538453/8388608)), (3/268435456), by norm_num⟩, -4, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-563220097/268435456), (-3757985523/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1063453637595221/9007199254740992), (-75058879576819/2251799813685248)), (5995201/2251799813685248), by norm_num⟩
  | 1 => ⟨((607979405/2147483648), (1373163853/17179869184)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((-5831483765/17179869184), (-411587889/4294967296)), (17/2147483648), by norm_num⟩
  | 3 => ⟨((4661095785/17179869184), (1315926205/17179869184)), (111/17179869184), by norm_num⟩
  | 4 => ⟨((-5588409775/34359738368), (-1577726613/34359738368)), (17/4294967296), by norm_num⟩
  | 5 => ⟨((5360168553/68719476736), (1513289275/68719476736)), (133/68719476736), by norm_num⟩
  | 6 => ⟨((-2142187139/68719476736), (-1209569733/137438953472)), (27/34359738368), by norm_num⟩
  | 7 => ⟨((5870560473/549755813888), (414345935/137438953472)), (75/274877906944), by norm_num⟩
  | 8 => ⟨((-1759623651/549755813888), (-993558159/1099511627776)), (23/274877906944), by norm_num⟩
  | 9 => ⟨((937642941/1099511627776), (1058865961/4398046511104)), (25/1099511627776), by norm_num⟩
  | 10 => ⟨((-3597391321/17592186044416), (-1015619873/17592186044416)), (49/8796093022208), by norm_num⟩
  | 11 => ⟨((1568394117/35184372088832), (221395463/17592186044416)), (87/70368744177664), by norm_num⟩
  | 12 => ⟨((-5014459785/562949953421312), (-707844179/281474976710656)), (71/281474976710656), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581242681576647/10141204801825835211973625643008), (-3733848751071/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778722346994351/633825300114114700748351602688), (-2209322104167/316912650057057350374175801344)), (2895/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944844546885781/19807040628566084398385987584), (-4970036180485/39614081257132168796771975168)), (13031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944730090667117/1237940039285380274899124224), (-659941267453/309485009821345068724781056)), (6925/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885562828444143/77371252455336267181195264), (-5278255208515/154742504910672534362390528)), (6927/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774745818743193/4835703278458516698824704), (-4947009811693/9671406556917033397649408)), (12993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258733798023933/604462909807314587353088), (-2163639663737/302231454903657293676544)), (5687/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943850658704521/37778931862957161709568), (-439330629679/4722366482869645213696)), (18491/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648735031189229/2361183241434822606848), (-1317436619835/1180591620717411303424)), (13877/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405337629489459/147573952589676412928), (-1810573228221/147573952589676412928)), (19093/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227918668717025/9223372036854775808), (-4523727358703/36893488147419103232)), (23885/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822511459280623/9223372036854775808), (-10170947998875/9223372036854775808)), (13449/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398438584065225/288230376151711744), (-1270206628887/144115188075855872)), (26931/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298592965057901/36028797018963968), (-8880994014261/144115188075855872)), (11801/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491311445790747/36028797018963968), (-6650298700589/18014398509481984)), (17739/18014398509481984), by norm_num⟩
  | 3 => ⟨((93051766443245/562949953421312), (-4147302023751/2251799813685248)), (44479/9007199254740992), by norm_num⟩
  | 2 => ⟨((139188977944323/281474976710656), (-4133612665989/562949953421312)), (44677/2251799813685248), by norm_num⟩
  | 1 => ⟨((276819275466983/281474976710656), (-24664960233541/1125899906842624)), (67511/1125899906842624), by norm_num⟩
  | 0 => ⟨((544247272463805/562949953421312), (-48784131289809/1125899906842624)), (137013/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544247272463805/562949953421312), (-48784131289809/1125899906842624)), (522663120750045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1050218119466229/1125899906842624), (-94326787781521/1125899906842624)), (276797/1125899906842624), by norm_num⟩
  | 2 => ⟨((242930243823825/281474976710656), (-175972484014151/1125899906842624)), (562763/1125899906842624), by norm_num⟩
  | 3 => ⟨((405575723538271/562949953421312), (-607500374596865/2251799813685248)), (2294625/2251799813685248), by norm_num⟩
  | 4 => ⟨((502444746973061/1125899906842624), (-875343900392857/2251799813685248)), (4544421/2251799813685248), by norm_num⟩
  | 5 => ⟨((216338903314573/4503599627370496), (-1562525911493045/4503599627370496)), (7589105/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1063453637595221/9007199254740992), (-75058879576819/2251799813685248)), (5995201/2251799813685248), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-563220097/268435456), (-3757985523/134217728)), (1/134217728), by norm_num⟩, -4, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-291828709/134217728), (-973587475/33554432)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-755626572653945/9007199254740992), (345555544716123/4503599627370496)), (17495461/4503599627370496), by norm_num⟩
  | 1 => ⟨((3581355085/17179869184), (-3275578579/17179869184)), (169/17179869184), by norm_num⟩
  | 2 => ⟨((-4449666533/17179869184), (508719187/2147483648)), (213/17179869184), by norm_num⟩
  | 3 => ⟨((921417163/4294967296), (-1685492921/8589934592)), (179/17179869184), by norm_num⟩
  | 4 => ⟨((-2289635635/17179869184), (523536571/4294967296)), (113/17179869184), by norm_num⟩
  | 5 => ⟨((1137906163/17179869184), (-2081503211/34359738368)), (57/17179869184), by norm_num⟩
  | 6 => ⟨((-942530197/34359738368), (3448227447/137438953472)), (191/137438953472), by norm_num⟩
  | 7 => ⟨((2676685205/274877906944), (-1224074759/137438953472)), (69/137438953472), by norm_num⟩
  | 8 => ⟨((-3325656433/1099511627776), (760427877/274877906944)), (87/549755813888), by norm_num⟩
  | 9 => ⟨((3672864793/4398046511104), (-3359275179/4398046511104)), (97/2199023255552), by norm_num⟩
  | 10 => ⟨((-3650690459/17592186044416), (834748523/4398046511104)), (195/17592186044416), by norm_num⟩
  | 11 => ⟨((1649386363/35184372088832), (-3017123135/70368744177664)), (179/70368744177664), by norm_num⟩
  | 12 => ⟨((-2732380761/281474976710656), (624772445/70368744177664)), (75/140737488355328), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581143507299009/10141204801825835211973625643008), (1563628148131/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889304055740505/316912650057057350374175801344), (462542054605/79228162514264337593543950336)), (4339/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889560780851359/39614081257132168796771975168), (4162073574235/39614081257132168796771975168)), (19531/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889324108813303/2475880078570760549798248448), (2210610340831/1237940039285380274899124224)), (5189/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885494938323247/77371252455336267181195264), (4420115550523/154742504910672534362390528)), (10381/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774682326940989/4835703278458516698824704), (2071342180317/4835703278458516698824704)), (19471/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258622997546487/604462909807314587353088), (1811837555173/302231454903657293676544)), (17043/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235940230974731/9444732965739290427392), (2943135957763/37778931862957161709568)), (27705/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297335968273131/4722366482869645213696), (4412779373785/4722366482869645213696)), (10395/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621166963450717/590295810358705651712), (6064445271851/590295810358705651712)), (28601/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823121142569707/73786976294838206464), (3787934436385/36893488147419103232)), (35775/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455564105864405/2305843009213693952), (8516409851319/9223372036854775808)), (40281/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398375354666181/288230376151711744), (8508361035061/1152921504606846976)), (40323/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194152935774445/144115188075855872), (7435767138457/144115188075855872)), (17665/72057594037927936), by norm_num⟩
  | 4 => ⟨((745493902288621/18014398509481984), (5567784278695/18014398509481984)), (1659/1125899906842624), by norm_num⟩
  | 3 => ⟨((23256749851669/140737488355328), (13887851565729/9007199254740992)), (33263/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113127918129523/2251799813685248), (13840507177051/2251799813685248)), (66775/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106731982532283/1125899906842624), (10321321283205/562949953421312)), (100785/1125899906842624), by norm_num⟩
  | 0 => ⟨((271881547188623/281474976710656), (40814270511561/1125899906842624)), (204071/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((271881547188623/281474976710656), (40814270511561/1125899906842624)), (778469089988326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1048980819140049/1125899906842624), (78846419271331/1125899906842624)), (102257/281474976710656), by norm_num⟩
  | 2 => ⟨((1943590179628205/2251799813685248), (293839198212355/2251799813685248)), (819457/1125899906842624), by norm_num⟩
  | 3 => ⟨((819611337008723/1125899906842624), (507241342293837/2251799813685248)), (3256911/2251799813685248), by norm_num⟩
  | 4 => ⟨((539514476578707/1125899906842624), (738503933106129/2251799813685248)), (1552279/562949953421312), by norm_num⟩
  | 5 => ⟨((274853660959257/2251799813685248), (176940046135363/562949953421312)), (1252917/281474976710656), by norm_num⟩
  | 6 => ⟨((-755626572653945/9007199254740992), (345555544716123/4503599627370496)), (17495461/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-291828709/134217728), (-973587475/33554432)), (3/268435456), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-150614483/67108864), (-4019792967/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((199485891274329/18014398509481984), (1899049782078681/18014398509481984)), (74491141/18014398509481984), by norm_num⟩
  | 1 => ⟨((-243983845/8589934592), (-4645315665/17179869184)), (23/2147483648), by norm_num⟩
  | 2 => ⟨((312903103/8589934592), (5957499715/17179869184)), (119/8589934592), by norm_num⟩
  | 3 => ⟨((-267526871/8589934592), (-5093561689/17179869184)), (205/17179869184), by norm_num⟩
  | 4 => ⟨((171548219/8589934592), (6532363891/34359738368)), (265/34359738368), by norm_num⟩
  | 5 => ⟨((-704019991/68719476736), (-3351036513/34359738368)), (137/34359738368), by norm_num⟩
  | 6 => ⟨((75240651/17179869184), (1432539825/34359738368)), (237/137438953472), by norm_num⟩
  | 7 => ⟨((-441116479/274877906944), (-4199305261/274877906944)), (11/17179869184), by norm_num⟩
  | 8 => ⟨((565720715/1099511627776), (5385502665/1099511627776)), (57/274877906944), by norm_num⟩
  | 9 => ⟨((-322454441/2199023255552), (-3069675911/2199023255552)), (131/2199023255552), by norm_num⟩
  | 10 => ⟨((661663449/17592186044416), (1574712651/4398046511104)), (271/17592186044416), by norm_num⟩
  | 11 => ⟨((-617139359/70368744177664), (-5874993749/70368744177664)), (255/70368744177664), by norm_num⟩
  | 12 => ⟨((263821867/140737488355328), (78484695/4398046511104)), (55/70368744177664), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275801731/10141204801825835211973625643008), (238725575059/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889252382582981/316912650057057350374175801344), (2259521414085/633825300114114700748351602688)), (11553/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944722399095651/19807040628566084398385987584), (158841373515/2475880078570760549798248448)), (12999/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889201244007969/2475880078570760549798248448), (2699684928649/2475880078570760549798248448)), (27627/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770867424141123/154742504910672534362390528), (2698989432601/154742504910672534362390528)), (1727/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387312573112679/2417851639229258349412352), (632390961603/2417851639229258349412352)), (12955/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258523368776021/604462909807314587353088), (1106314932033/302231454903657293676544)), (22677/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887360770664587/75557863725914323419136), (3594139359403/75557863725914323419136)), (18429/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297215876930139/4722366482869645213696), (2694393891575/4722366482869645213696)), (6913/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810501500471087/295147905179352825856), (1851412653017/295147905179352825856)), (19017/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113932370744067/4611686018427387904), (289098993545/4611686018427387904)), (23781/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822030203848617/9223372036854775808), (5199731518687/9223372036854775808)), (26767/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398319546070741/288230376151711744), (649334089653/144115188075855872)), (53569/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596980478424121/72057594037927936), (1134913296225/36028797018963968)), (46911/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490706520470035/36028797018963968), (849765394029/4503599627370496)), (70443/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488092042355437/9007199254740992), (4238905949137/4503599627370496)), (22047/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112805374591183/2251799813685248), (1056014106909/281474976710656)), (176781/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212582792938243/2251799813685248), (12598145368335/1125899906842624)), (66547/562949953421312), by norm_num⟩
  | 0 => ⟨((1086816245671763/1125899906842624), (3112691777659/140737488355328)), (536457/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086816245671763/1125899906842624), (3112691777659/140737488355328)), (2046421059615325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((524269279300379/562949953421312), (12018560339757/281474976710656)), (132425/281474976710656), by norm_num⟩
  | 2 => ⟨((974440063030987/1125899906842624), (44771027543451/562949953421312)), (2063687/2251799813685248), by norm_num⟩
  | 3 => ⟨((836233888189007/1125899906842624), (309986226209009/2251799813685248)), (1950197/1125899906842624), by norm_num⟩
  | 4 => ⟨((299877567509323/562949953421312), (230234486789091/1125899906842624)), (6867709/2251799813685248), by norm_num⟩
  | 5 => ⟨((544805628298303/2251799813685248), (490574037251221/2251799813685248)), (20250921/4503599627370496), by norm_num⟩
  | 6 => ⟨((199485891274329/18014398509481984), (1899049782078681/18014398509481984)), (74491141/18014398509481984), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-150614483/67108864), (-4019792967/134217728)), (1/67108864), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-77483061/33554432), (-2067967553/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((369052241124063/4503599627370496), (252920598078223/4503599627370496)), (22719447/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3715324485/17179869184), (-2546203453/17179869184)), (117/17179869184), by norm_num⟩
  | 2 => ⟨((4902477157/17179869184), (1679894221/8589934592)), (157/17179869184), by norm_num⟩
  | 3 => ⟨((-67384991/268435456), (-369444763/2147483648)), (141/17179869184), by norm_num⟩
  | 4 => ⟨((1422662835/8589934592), (1949971819/17179869184)), (95/17179869184), by norm_num⟩
  | 5 => ⟨((-1501795513/17179869184), (-257304371/4294967296)), (103/34359738368), by norm_num⟩
  | 6 => ⟨((165138519/4294967296), (1810775963/68719476736)), (23/17179869184), by norm_num⟩
  | 7 => ⟨((-3984548745/274877906944), (-2730709473/274877906944)), (141/274877906944), by norm_num⟩
  | 8 => ⟨((1314431571/274877906944), (225203089/68719476736)), (95/549755813888), by norm_num⟩
  | 9 => ⟨((-385428919/274877906944), (-264143939/274877906944)), (57/1099511627776), by norm_num⟩
  | 10 => ⟨((813735211/2199023255552), (1115345597/4398046511104)), (61/4398046511104), by norm_num⟩
  | 11 => ⟨((-3123627451/35184372088832), (-2140698889/35184372088832)), (119/35184372088832), by norm_num⟩
  | 12 => ⟨((171738165/8796093022208), (470785591/35184372088832)), (107/140737488355328), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634167/10141204801825835211973625643008), (48913774553/633825300114114700748351602688)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444601777808171/158456325028528675187087900672), (925832014215/633825300114114700748351602688)), (11537/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889335087067587/39614081257132168796771975168), (520676039843/19807040628566084398385987584)), (25959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889084870727553/2475880078570760549798248448), (553088019933/1237940039285380274899124224)), (27583/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55335977181641/4835703278458516698824704), (276470762401/38685626227668133590597632)), (27585/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549141630255963/9671406556917033397649408), (1036454164261/9671406556917033397649408)), (25863/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((19662945651209/9444732965739290427392), (906586319859/604462909807314587353088)), (22633/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943603539689441/37778931862957161709568), (23009683797/1180591620717411303424)), (36781/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297100988955785/4722366482869645213696), (275988736987/1180591620717411303424)), (13795/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25325713243927/9223372036854775808), (1517109988549/590295810358705651712)), (37941/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227840270691809/9223372036854775808), (1895146229337/73786976294838206464)), (47433/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910905618539951/4611686018427387904), (1065167073035/4611686018427387904)), (26687/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593060802695993/1152921504606846976), (1064102245083/576460752303423488)), (13347/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193772527422593/144115188075855872), (464946469257/36028797018963968)), (46731/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490427425607709/36028797018963968), (1392449865295/18014398509481984)), (70127/36028797018963968), by norm_num⟩
  | 3 => ⟨((743874681672097/4503599627370496), (3472777032711/9007199254740992)), (43857/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112471936709965/2251799813685248), (1730143531495/1125899906842624)), (43899/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211628383421659/2251799813685248), (10318631131995/2251799813685248)), (32977/281474976710656), by norm_num⟩
  | 0 => ⟨((2171905487792953/2251799813685248), (20389656469015/2251799813685248)), (264667/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2171905487792953/2251799813685248), (20389656469015/2251799813685248)), (1009624485496139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((523665301101397/562949953421312), (39332454430567/2251799813685248)), (1030693/2251799813685248), by norm_num⟩
  | 2 => ⟨((1947801262178899/2251799813685248), (18293847852071/562949953421312)), (976771/1125899906842624), by norm_num⟩
  | 3 => ⟨((1682465331071173/2251799813685248), (126593064693639/2251799813685248)), (3506585/2251799813685248), by norm_num⟩
  | 4 => ⟨((1249961816819535/2251799813685248), (23646467284377/281474976710656)), (5634265/2251799813685248), by norm_num⟩
  | 5 => ⟨((169488711614907/562949953421312), (420032807939827/4503599627370496)), (14403519/4503599627370496), by norm_num⟩
  | 6 => ⟨((369052241124063/4503599627370496), (252920598078223/4503599627370496)), (22719447/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77483061/33554432), (-2067967553/67108864)), (1/67108864), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-159017401/67108864), (-4244060851/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((824780786787833/9007199254740992), (-342618358650979/18014398509481984)), (15779849/9007199254740992), by norm_num⟩
  | 1 => ⟨((-532519287/2147483648), (442422731/8589934592)), (83/17179869184), by norm_num⟩
  | 2 => ⟨((5768355849/17179869184), (-599051483/8589934592)), (115/17179869184), by norm_num⟩
  | 3 => ⟨((-162718721/536870912), (1081507659/17179869184)), (53/8589934592), by norm_num⟩
  | 4 => ⟨((3525203721/17179869184), (-1464388517/34359738368)), (73/17179869184), by norm_num⟩
  | 5 => ⟨((-1909285729/17179869184), (198281881/8589934592)), (81/34359738368), by norm_num⟩
  | 6 => ⟨((6893922137/137438953472), (-1431886101/137438953472)), (149/137438953472), by norm_num⟩
  | 7 => ⟨((-5334024923/274877906944), (553945635/137438953472)), (117/274877906944), by norm_num⟩
  | 8 => ⟨((451400227/68719476736), (-375028147/274877906944)), (81/549755813888), by norm_num⟩
  | 9 => ⟨((-1086590645/549755813888), (902751155/2199023255552)), (25/549755813888), by norm_num⟩
  | 10 => ⟨((588508403/1099511627776), (-977878179/8796093022208)), (55/4398046511104), by norm_num⟩
  | 11 => ⟨((-4636248143/35184372088832), (962961163/35184372088832)), (55/17592186044416), by norm_num⟩
  | 12 => ⟨((4185064239/140737488355328), (-869249057/140737488355328)), (101/140737488355328), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790444585791105/5070602400912917605986812821504), (-133381501399/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111144655929093/39614081257132168796771975168), (-315546482517/633825300114114700748351602688)), (11529/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944615468753917/19807040628566084398385987584), (-354916905959/39614081257132168796771975168)), (25941/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944487134063711/1237940039285380274899124224), (-47126013069/309485009821345068724781056)), (27563/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770640730511927/154742504910672534362390528), (-188452826877/77371252455336267181195264)), (6891/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549038066881043/9671406556917033397649408), (-88310058935/2417851639229258349412352)), (12921/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629168985451365/302231454903657293676544), (-308976435869/604462909807314587353088)), (5653/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943530030121299/37778931862957161709568), (-501882857767/75557863725914323419136)), (18373/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296990834655083/4722366482869645213696), (-47029233507/590295810358705651712)), (27561/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202586795514835/73786976294838206464), (-517032047287/590295810358705651712)), (18949/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822533328890105/73786976294838206464), (-645856084997/73786976294838206464)), (47375/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113849947719355/576460752303423488), (-725991881025/9223372036854775808)), (53301/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796424594000777/576460752303423488), (-725247361785/1152921504606846976)), (26653/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193587879849301/144115188075855872), (-79219360769/18014398509481984)), (5831/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490151482443317/36028797018963968), (-237240446701/9007199254740992)), (69983/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487406228402755/9007199254740992), (-591642276857/4503599627370496)), (43749/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224262964323439/4503599627370496), (-73682471835/140737488355328)), (10941/281474976710656), by norm_num⟩
  | 1 => ⟨((552655086900749/562949953421312), (-878753505489/562949953421312)), (131367/1125899906842624), by norm_num⟩
  | 0 => ⟨((2169942284656439/2251799813685248), (-867941278015/281474976710656)), (65761/281474976710656), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2169942284656439/2251799813685248), (-867941278015/281474976710656)), (250858307958507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2091039033537371/2251799813685248), (-6691118698269/1125899906842624)), (254293/562949953421312), by norm_num⟩
  | 2 => ⟨((1941675778160585/2251799813685248), (-12426850993663/1125899906842624)), (1901199/2251799813685248), by norm_num⟩
  | 3 => ⟨((836994278550893/1125899906842624), (-2678847762861/140737488355328)), (1660345/1125899906842624), by norm_num⟩
  | 4 => ⟨((310906919722859/562949953421312), (-15931648893453/562949953421312)), (5063619/2251799813685248), by norm_num⟩
  | 5 => ⟨((1370058488633561/4503599627370496), (-140780113144091/4503599627370496)), (11759383/4503599627370496), by norm_num⟩
  | 6 => ⟨((824780786787833/9007199254740992), (-342618358650979/18014398509481984)), (15779849/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-159017401/67108864), (-4244060851/134217728)), (1/67108864), by norm_num⟩, -5, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile028Terms1
