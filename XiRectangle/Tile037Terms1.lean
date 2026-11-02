/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile037Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (3525/256))
  have he : value ((5/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-46079139/33554432), (-1015181035/33554432)), (3/67108864), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((454284627727667/4503599627370496), (523149756945143/2251799813685248)), (29231921/1125899906842624), by norm_num⟩
  | 1 => ⟨((-475962329/2147483648), (-1096227173/2147483648)), (125/2147483648), by norm_num⟩
  | 2 => ⟨((32681129/134217728), (301082161/536870912)), (35/536870912), by norm_num⟩
  | 3 => ⟨((-191487413/1073741824), (-882060165/2147483648)), (105/2147483648), by norm_num⟩
  | 4 => ⟨((210370425/2147483648), (969042137/4294967296)), (117/4294967296), by norm_num⟩
  | 5 => ⟨((-369784855/8589934592), (-103965/1048576)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((541666915/34359738368), (623778347/17179869184)), (39/8589934592), by norm_num⟩
  | 7 => ⟨((-340046817/68719476736), (-783189209/68719476736)), (25/17179869184), by norm_num⟩
  | 8 => ⟨((93394903/68719476736), (430210645/137438953472)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((-364817025/1099511627776), (-840239469/1099511627776)), (7/68719476736), by norm_num⟩
  | 10 => ⟨((641267947/8796093022208), (738477925/4398046511104)), (199/8796093022208), by norm_num⟩
  | 11 => ⟨((-256183581/17592186044416), (-1180074071/35184372088832)), (81/17592186044416), by norm_num⟩
  | 12 => ⟨((375261907/140737488355328), (432147959/70368744177664)), (121/140737488355328), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791093467826773/5070602400912917605986812821504), (756279422259/5070602400912917605986812821504)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((889924592214917/316912650057057350374175801344), (896053352351/316912650057057350374175801344)), (69283/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890957082778923/39614081257132168796771975168), (2015872701133/39614081257132168796771975168)), (77951/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472701956129587/618970019642690137449562112), (2141564418033/2475880078570760549798248448)), (82833/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772473755023891/154742504910672534362390528), (1070613301351/77371252455336267181195264)), (20711/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387688990605615/2417851639229258349412352), (2007041068821/9671406556917033397649408)), (38839/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314960141192163/151115727451828646838272), (1755802128767/604462909807314587353088)), (16995/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944750358418849/37778931862957161709568), (2852505834753/75557863725914323419136)), (110489/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649410200702917/2361183241434822606848), (1069395483609/2361183241434822606848)), (82887/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811604257482149/295147905179352825856), (2939881673487/590295810358705651712)), (7125/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1825673763723951/73786976294838206464), (3673418683525/73786976294838206464)), (142547/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825129056153599/9223372036854775808), (2065312907887/4611686018427387904)), (80215/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399093803362617/288230376151711744), (2064082080729/576460752303423488)), (80255/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196668806310601/144115188075855872), (3609375791847/144115188075855872)), (70269/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494764192479205/36028797018963968), (5408531766989/36028797018963968)), (210989/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493156953417545/9007199254740992), (6750992344963/9007199254740992)), (264055/9007199254740992), by norm_num⟩
  | 2 => ⟨((558929758514957/1125899906842624), (6736500786791/2251799813685248)), (264533/2251799813685248), by norm_num⟩
  | 1 => ⟨((2227691376227259/2251799813685248), (20137163412517/2251799813685248)), (397999/1125899906842624), by norm_num⟩
  | 0 => ⟨((2203634280216215/2251799813685248), (39985683535533/2251799813685248)), (1601613/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2203634280216215/2251799813685248), (39985683535533/2251799813685248)), (6109668740279387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1077894481683879/1125899906842624), (78260796027487/2251799813685248)), (3191591/2251799813685248), by norm_num⟩
  | 2 => ⟨((515287957012875/562949953421312), (74923960520415/1125899906842624)), (6332867/2251799813685248), by norm_num⟩
  | 3 => ⟨((1876673242957497/2251799813685248), (274322179534735/2251799813685248)), (6218123/1125899906842624), by norm_num⟩
  | 4 => ⟨((765309993743895/1125899906842624), (457245880520869/2251799813685248)), (2969881/281474976710656), by norm_num⟩
  | 5 => ⟨((947563694550543/2251799813685248), (310804574930799/1125899906842624)), (41948491/2251799813685248), by norm_num⟩
  | 6 => ⟨((454284627727667/4503599627370496), (523149756945143/2251799813685248)), (29231921/1125899906842624), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-46079139/33554432), (-1015181035/33554432)), (3/67108864), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-48288709/33554432), (-265965157/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((127937784739479/562949953421312), (-304970193549395/4503599627370496)), (84753005/4503599627370496), by norm_num⟩
  | 1 => ⟨((-561881325/1073741824), (41855563/268435456)), (95/2147483648), by norm_num⟩
  | 2 => ⟨((1293779563/2147483648), (-192751991/1073741824)), (7/134217728), by norm_num⟩
  | 3 => ⟨((-31031641/67108864), (295885241/2147483648)), (11/268435456), by norm_num⟩
  | 4 => ⟨((35726497/134217728), (-340650473/4294967296)), (13/536870912), by norm_num⟩
  | 5 => ⟨((-1052970233/8589934592), (39218835/1073741824)), (49/4294967296), by norm_num⟩
  | 6 => ⟨((1616369041/34359738368), (-481625093/34359738368)), (77/17179869184), by norm_num⟩
  | 7 => ⟨((-1063379217/68719476736), (316852217/68719476736)), (103/68719476736), by norm_num⟩
  | 8 => ⟨((1224260567/274877906944), (-91197399/68719476736)), (121/274877906944), by norm_num⟩
  | 9 => ⟨((-313218237/274877906944), (373315149/1099511627776)), (63/549755813888), by norm_num⟩
  | 10 => ⟨((576969315/2199023255552), (-343835959/4398046511104)), (59/2199023255552), by norm_num⟩
  | 11 => ⟨((-483098525/8796093022208), (143947555/8796093022208)), (101/17592186044416), by norm_num⟩
  | 12 => ⟨((1483167283/140737488355328), (-220967663/70368744177664)), (157/140737488355328), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395525289565701/2535301200456458802993406410752), (-23576528007/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889874583931169/316912650057057350374175801344), (-446893739915/633825300114114700748351602688)), (23061/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472711168114897/9903520314283042199192993792), (-502691394151/39614081257132168796771975168)), (51889/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890688524568581/2475880078570760549798248448), (-267015592165/1237940039285380274899124224)), (110267/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886177304010657/77371252455336267181195264), (-533942980631/154742504910672534362390528)), (110271/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775322212274989/4835703278458516698824704), (-500477848269/9671406556917033397649408)), (103383/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259743131500713/604462909807314587353088), (-13682013877/18889465931478580854784)), (2827/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1889342692069113/75557863725914323419136), (-355644566531/37778931862957161709568)), (147011/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298702148931957/4722366482869645213696), (-133328314615/1180591620717411303424)), (110265/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811523174971527/295147905179352825856), (-366528117811/295147905179352825856)), (18953/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912735852571047/36893488147419103232), (-915946211855/73786976294838206464)), (94773/36893488147419103232), by norm_num⟩
  | 7 => ⟨((57028207187997/288230376151711744), (-128740672959/1152921504606846976)), (213261/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596149898302279/1152921504606846976), (-257320785285/288230376151711744)), (213287/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299118225936063/36028797018963968), (-899900759205/144115188075855872)), (186657/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494472830823329/36028797018963968), (-674204246527/18014398509481984)), (280047/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492797103286415/9007199254740992), (-841494491103/4503599627370496)), (350165/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117506176035381/2251799813685248), (-839606257841/1125899906842624)), (175163/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113331883892871/1125899906842624), (-2509398520775/1125899906842624)), (525893/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100853968364295/1125899906842624), (-4981241250813/1125899906842624)), (2106827/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1100853968364295/1125899906842624), (-4981241250813/1125899906842624)), (8036907204634856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2152686290378045/2251799813685248), (-9740864467633/1125899906842624)), (4138563/2251799813685248), by norm_num⟩
  | 2 => ⟨((2057766724581037/2251799813685248), (-9312117919393/562949953421312)), (3992209/1125899906842624), by norm_num⟩
  | 3 => ⟨((939918463982593/1125899906842624), (-68077690648855/2251799813685248)), (14856985/2251799813685248), by norm_num⟩
  | 4 => ⟨((1567258458025081/2251799813685248), (-113664594938275/2251799813685248)), (25704007/2251799813685248), by norm_num⟩
  | 5 => ⟨((1085078442257213/2251799813685248), (-39555425112027/562949953421312)), (38375045/2251799813685248), by norm_num⟩
  | 6 => ⟨((127937784739479/562949953421312), (-304970193549395/4503599627370496)), (84753005/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-48288709/33554432), (-265965157/8388608)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-50287509/33554432), (-1107896675/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-3919945314497/562949953421312), (-2011445714762455/9007199254740992)), (80924919/2251799813685248), by norm_num⟩
  | 1 => ⟨((17928349/1073741824), (1149949115/2147483648)), (187/2147483648), by norm_num⟩
  | 2 => ⟨((-42990303/2147483648), (-1378728773/2147483648)), (227/2147483648), by norm_num⟩
  | 3 => ⟨((34362081/2147483648), (137751967/268435456)), (23/268435456), by norm_num⟩
  | 4 => ⟨((-160931/16777216), (-660629581/2147483648)), (111/2147483648), by norm_num⟩
  | 5 => ⟨((19757859/4294967296), (1267296439/8589934592)), (215/8589934592), by norm_num⟩
  | 6 => ⟨((-31584851/17179869184), (-1012948047/17179869184)), (347/34359738368), by norm_num⟩
  | 7 => ⟨((10819595/17179869184), (1387967619/68719476736)), (15/4294967296), by norm_num⟩
  | 8 => ⟨((-51888511/274877906944), (-104006281/17179869184)), (145/137438953472), by norm_num⟩
  | 9 => ⟨((55299207/1099511627776), (55421371/34359738368)), (39/137438953472), by norm_num⟩
  | 10 => ⟨((-53040683/4398046511104), (-1701051437/4398046511104)), (151/2199023255552), by norm_num⟩
  | 11 => ⟨((2890591/1099511627776), (1483252073/17592186044416)), (133/8796093022208), by norm_num⟩
  | 12 => ⟨((-36967117/70368744177664), (-1185561045/70368744177664)), (215/70368744177664), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791011781571557/5070602400912917605986812821504), (-2086741327065/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889827044205931/316912650057057350374175801344), (-1235948593611/316912650057057350374175801344)), (23111/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890737538029637/39614081257132168796771975168), (-347563859909/4951760157141521099596496896)), (52007/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890574478030275/2475880078570760549798248448), (-1476920256165/1237940039285380274899124224)), (110533/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772240318385283/154742504910672534362390528), (-2953331739637/154742504910672534362390528)), (55277/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775268509924225/4835703278458516698824704), (-2768208012073/9671406556917033397649408)), (51833/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259648894358149/604462909807314587353088), (-2421641603481/604462909807314587353088)), (90729/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889189073203895/75557863725914323419136), (-3934154526737/75557863725914323419136)), (73737/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298586512008249/4722366482869645213696), (-2949729635375/4722366482869645213696)), (55321/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622886662717127/590295810358705651712), (-4054438422399/590295810358705651712)), (76095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456317766848385/18446744073709551616), (-1266472223433/18446744073709551616)), (47581/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912337749817721/4611686018427387904), (-1424039294805/2305843009213693952)), (214233/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595921004135457/1152921504606846976), (-2846224435855/576460752303423488)), (107191/576460752303423488), by norm_num⟩
  | 5 => ⟨((598135320162191/72057594037927936), (-2488361472805/72057594037927936)), (23469/18014398509481984), by norm_num⟩
  | 4 => ⟨((93385342607919/2251799813685248), (-7456749857101/36028797018963968)), (140981/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492406015632809/9007199254740992), (-9306363255751/9007199254740992)), (22065/562949953421312), by norm_num⟩
  | 2 => ⟨((1117104772718063/2251799813685248), (-9284524996921/2251799813685248)), (176961/1125899906842624), by norm_num⟩
  | 1 => ⟨((1112704116410031/1125899906842624), (-1734033976851/140737488355328)), (266545/562949953421312), by norm_num⟩
  | 0 => ⟨((68718533825791/70368744177664), (-13763480463243/562949953421312)), (537517/562949953421312), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((68718533825791/70368744177664), (-13763480463243/562949953421312)), (2050464632274436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1073039355646395/1125899906842624), (-26881428930607/562949953421312)), (2152215/1125899906842624), by norm_num⟩
  | 2 => ⟨((1020093355457719/1125899906842624), (-6404839143171/70368744177664)), (538485/140737488355328), by norm_num⟩
  | 3 => ⟨((228725667505939/281474976710656), (-371388401431673/2251799813685248)), (8590285/1125899906842624), by norm_num⟩
  | 4 => ⟨((1425641044216349/2251799813685248), (-150894514699159/562949953421312)), (16794461/1125899906842624), by norm_num⟩
  | 5 => ⟨((740805600815605/2251799813685248), (-764264788352265/2251799813685248)), (60537605/2251799813685248), by norm_num⟩
  | 6 => ⟨((-3919945314497/562949953421312), (-2011445714762455/9007199254740992)), (80924919/2251799813685248), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50287509/33554432), (-1107896675/33554432)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-52112269/33554432), (-1148098437/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-224479254815075/1125899906842624), (-319162236468459/4503599627370496)), (2595355/70368744177664), by norm_num⟩
  | 1 => ⟨((1063938127/2147483648), (378174001/2147483648)), (199/2147483648), by norm_num⟩
  | 2 => ⟨((-1321893463/2147483648), (-469863545/2147483648)), (249/2147483648), by norm_num⟩
  | 3 => ⟨((1094927285/2147483648), (48648627/268435456)), (13/134217728), by norm_num⟩
  | 4 => ⟨((-1360396045/4294967296), (-483549187/4294967296)), (261/4294967296), by norm_num⟩
  | 5 => ⟨((1352182871/8589934592), (120157459/2147483648)), (261/8589934592), by norm_num⟩
  | 6 => ⟨((-1120016069/17179869184), (-199053379/8589934592)), (109/8589934592), by norm_num⟩
  | 7 => ⟨((24849423/1073741824), (70661295/8589934592)), (39/8589934592), by norm_num⟩
  | 8 => ⟨((-987975943/137438953472), (-87793361/34359738368)), (49/34359738368), by norm_num⟩
  | 9 => ⟨((1091123551/549755813888), (387836989/549755813888)), (219/549755813888), by norm_num⟩
  | 10 => ⟨((-1084536067/2199023255552), (-385495485/2199023255552)), (55/549755813888), by norm_num⟩
  | 11 => ⟨((244997353/2199023255552), (87083663/2199023255552)), (201/8796093022208), by norm_num⟩
  | 12 => ⟨((-405863701/17592186044416), (-72131591/8796093022208)), (21/4398046511104), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197744090550571/1267650600228229401496703205376), (-3647407994141/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444890867356423/158456325028528675187087900672), (-4320233188975/633825300114114700748351602688)), (92625/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236329402015097/4951760157141521099596496896), (-2429784373803/19807040628566084398385987584)), (52115/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890465282523499/2475880078570760549798248448), (-5162470504397/2475880078570760549798248448)), (13847/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((443032646213771/38685626227668133590597632), (-1290386607269/38685626227668133590597632)), (27703/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775216786648603/4835703278458516698824704), (-2418983965339/4835703278458516698824704)), (25981/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629778903788719/302231454903657293676544), (-2116120036997/302231454903657293676544)), (90971/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889039987145853/75557863725914323419136), (-6875549083223/75557863725914323419136)), (147899/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20288652529007/73786976294838206464), (-80547669781/73786976294838206464)), (110987/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811365056081295/295147905179352825856), (-1771394270127/147573952589676412928)), (152707/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825073102774509/73786976294838206464), (-4426522217863/36893488147419103232)), (191035/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824449662956579/9223372036854775808), (-9954275283279/9223372036854775808)), (107561/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797845632378291/576460752303423488), (-9947525357439/1152921504606846976)), (215383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299016308814235/36028797018963968), (-8696490629435/144115188075855872)), (188753/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493848626462291/36028797018963968), (-6514773439065/18014398509481984)), (70929/9007199254740992), by norm_num⟩
  | 3 => ⟨((745997339938373/4503599627370496), (-4065087669615/2251799813685248)), (355673/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116670620364391/2251799813685248), (-8110236199025/1125899906842624)), (357217/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111996138093447/1125899906842624), (-24231000164237/1125899906842624)), (539693/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097855333691647/1125899906842624), (-6007887197195/140737488355328)), (136863/140737488355328), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1097855333691647/1125899906842624), (-6007887197195/140737488355328)), (522090912402105287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1068457564527179/1125899906842624), (-11716478460603/140737488355328)), (278593/140737488355328), by norm_num⟩
  | 2 => ⟨((1006142646241959/1125899906842624), (-177899437984067/1125899906842624)), (4601161/1125899906842624), by norm_num⟩
  | 3 => ⟨((108876775878533/140737488355328), (-317954038739015/1125899906842624)), (9677537/1125899906842624), by norm_num⟩
  | 4 => ⟨((584040352164749/1125899906842624), (-245974338607355/562949953421312)), (40878535/2251799813685248), by norm_num⟩
  | 5 => ⟨((88009272708175/1125899906842624), (-127594769722111/281474976710656)), (1220825/35184372088832), by norm_num⟩
  | 6 => ⟨((-224479254815075/1125899906842624), (-319162236468459/4503599627370496)), (2595355/70368744177664), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-52112269/33554432), (-1148098437/33554432)), (1/16777216), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-53790887/33554432), (-592540237/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-656635333788313/4503599627370496), (156222326777381/1125899906842624)), (163712987/4503599627370496), by norm_num⟩
  | 1 => ⟨((100388311/268435456), (-191069773/536870912)), (101/1073741824), by norm_num⟩
  | 2 => ⟨((-1029963735/2147483648), (980168583/2147483648)), (131/1073741824), by norm_num⟩
  | 3 => ⟨((880601607/2147483648), (-838027593/2147483648)), (113/1073741824), by norm_num⟩
  | 4 => ⟨((-70584329/268435456), (67171823/268435456)), (147/2147483648), by norm_num⟩
  | 5 => ⟨((289672367/2147483648), (-275667719/2147483648)), (153/4294967296), by norm_num⟩
  | 6 => ⟨((-30958123/536870912), (942764985/17179869184)), (33/2147483648), by norm_num⟩
  | 7 => ⟨((181499469/8589934592), (-172724603/8589934592)), (195/34359738368), by norm_num⟩
  | 8 => ⟨((-931073893/137438953472), (886059719/137438953472)), (63/34359738368), by norm_num⟩
  | 9 => ⟨((530701641/274877906944), (-1010088137/549755813888)), (145/274877906944), by norm_num⟩
  | 10 => ⟨((-1088978267/2199023255552), (1036329967/2199023255552)), (75/549755813888), by norm_num⟩
  | 11 => ⟨((1015699675/8796093022208), (-966594139/8796093022208)), (141/4398046511104), by norm_num⟩
  | 12 => ⟨((-217101519/8796093022208), (103302709/4398046511104)), (243/35184372088832), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581887559023027/10141204801825835211973625643008), (3101468191523/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444872262156591/158456325028528675187087900672), (1836641325581/316912650057057350374175801344)), (46281/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472637916484783/9903520314283042199192993792), (2065921046009/19807040628566084398385987584)), (104155/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890376728872455/2475880078570760549798248448), (274335144331/154742504910672534362390528)), (27673/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772042276832577/154742504910672534362390528), (2194276199877/77371252455336267181195264)), (55361/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387587761348775/2417851639229258349412352), (4113407403411/9671406556917033397649408)), (103833/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629742928203513/302231454903657293676544), (899592767803/151115727451828646838272)), (45443/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944461777561515/37778931862957161709568), (2922869932731/37778931862957161709568)), (73875/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298386865124011/4722366482869645213696), (136965423505/147573952589676412928)), (55433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622611322994735/590295810358705651712), (6024185454037/590295810358705651712)), (76263/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456231414050349/18446744073709551616), (940849062593/9223372036854775808)), (95393/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456071303497177/2305843009213693952), (4231456620691/4611686018427387904)), (214811/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595528599196189/1152921504606846976), (1057125493749/144115188075855872)), (215033/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597962453150701/72057594037927936), (7393232036117/144115188075855872)), (94201/72057594037927936), by norm_num⟩
  | 4 => ⟨((186705266567379/4503599627370496), (11076559060597/36028797018963968)), (141551/18014398509481984), by norm_num⟩
  | 3 => ⟨((745871772583657/4503599627370496), (3455612945759/2251799813685248)), (354751/9007199254740992), by norm_num⟩
  | 2 => ⟨((558214963398835/1125899906842624), (1723449839179/281474976710656)), (11127/70368744177664), by norm_num⟩
  | 1 => ⟨((277915271359667/281474976710656), (20594327086023/1125899906842624)), (268691/562949953421312), by norm_num⟩
  | 0 => ⟨((548644244046193/562949953421312), (40840744035917/1125899906842624)), (1087949/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((548644244046193/562949953421312), (40840744035917/1125899906842624)), (4150196079734420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1067922692256455/1125899906842624), (1243840538227/17592186044416)), (2199533/1125899906842624), by norm_num⟩
  | 2 => ⟨((1007302502855023/1125899906842624), (151013129689215/1125899906842624)), (4483573/1125899906842624), by norm_num⟩
  | 3 => ⟨((110117844500597/140737488355328), (270212125563625/1125899906842624)), (9225319/1125899906842624), by norm_num⟩
  | 4 => ⟨((624429882517033/1125899906842624), (845692989770187/2251799813685248)), (37729007/2251799813685248), by norm_num⟩
  | 5 => ⟨((187506472520861/1125899906842624), (469025684288905/1125899906842624)), (70188653/2251799813685248), by norm_num⟩
  | 6 => ⟨((-656635333788313/4503599627370496), (156222326777381/1125899906842624)), (163712987/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-53790887/33554432), (-592540237/16777216)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-13836261/8388608), (-1219320491/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((361264793606871/9007199254740992), (1692729673341853/9007199254740992)), (64441855/2251799813685248), by norm_num⟩
  | 1 => ⟨((-56826979/536870912), (-33283313/67108864)), (41/536870912), by norm_num⟩
  | 2 => ⟨((299939311/2147483648), (702692569/1073741824)), (219/2147483648), by norm_num⟩
  | 3 => ⟨((-131926173/1073741824), (-309074329/536870912)), (195/2147483648), by norm_num⟩
  | 4 => ⟨((174080367/2147483648), (815664873/2147483648)), (65/1073741824), by norm_num⟩
  | 5 => ⟨((-367526455/8589934592), (-1722069089/8589934592)), (277/8589934592), by norm_num⟩
  | 6 => ⟨((323307795/17179869184), (1514879683/17179869184)), (123/8589934592), by norm_num⟩
  | 7 => ⟨((-243779373/34359738368), (-571122047/17179869184)), (187/34359738368), by norm_num⟩
  | 8 => ⟨((160836935/68719476736), (94201489/8589934592)), (249/137438953472), by norm_num⟩
  | 9 => ⟨((-11790497/17179869184), (-13811285/4294967296)), (295/549755813888), by norm_num⟩
  | 10 => ⟨((12446319/68719476736), (466544293/549755813888)), (157/1099511627776), by norm_num⟩
  | 11 => ⟨((-47776799/1099511627776), (-447722595/2199023255552)), (153/4398046511104), by norm_num⟩
  | 12 => ⟨((84057141/8796093022208), (787710397/17592186044416)), (271/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581827225323591/10141204801825835211973625643008), (1772241546881/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222427806340331/79228162514264337593543950336), (1049413775467/316912650057057350374175801344)), (92407/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890477035873269/39614081257132168796771975168), (2360834830279/39614081257132168796771975168)), (103971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890297806277925/2475880078570760549798248448), (2507964594865/2475880078570760549798248448)), (110485/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885981886178657/77371252455336267181195264), (313436184151/19342813113834066795298816)), (110501/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775138945744567/4835703278458516698824704), (1175133331557/4835703278458516698824704)), (51807/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259422290540395/604462909807314587353088), (2055978723261/604462909807314587353088)), (11335/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888821092210099/75557863725914323419136), (3340019523203/75557863725914323419136)), (73695/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324577686275139/1180591620717411303424), (1252093606995/2361183241434822606848)), (27643/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202813479831251/73786976294838206464), (3441913290341/590295810358705651712)), (76043/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912399035070375/36893488147419103232), (4300376193407/73786976294838206464)), (47545/18446744073709551616), by norm_num⟩
  | 7 => ⟨((228018013732069/1152921504606846976), (4835153272907/9223372036854775808)), (107027/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797695264375759/576460752303423488), (603961590911/144115188075855872)), (214181/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195807502001911/144115188075855872), (2111920306947/72057594037927936)), (93775/72057594037927936), by norm_num⟩
  | 4 => ⟨((746736413440753/18014398509481984), (6327986351679/36028797018963968)), (140805/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491543783260439/9007199254740992), (7896392007131/9007199254740992)), (1377/35184372088832), by norm_num⟩
  | 2 => ⟨((1116247907763451/2251799813685248), (15752069436111/4503599627370496)), (353261/2251799813685248), by norm_num⟩
  | 1 => ⟨((277858049013625/281474976710656), (5881630329613/562949953421312)), (1063537/2251799813685248), by norm_num⟩
  | 0 => ⟨((2194011920583981/2251799813685248), (23323965844239/1125899906842624)), (1071067/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2194011920583981/2251799813685248), (23323965844239/1125899906842624)), (4085796360496139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((267092585722539/281474976710656), (90901613520973/2251799813685248)), (2131537/1125899906842624), by norm_num⟩
  | 2 => ⟨((2023891123549593/2251799813685248), (172513715324865/2251799813685248)), (1054335/281474976710656), by norm_num⟩
  | 3 => ⟨((902916474478409/1125899906842624), (310106586753061/2251799813685248)), (16454369/2251799813685248), by norm_num⟩
  | 4 => ⟨((702741541489625/1125899906842624), (497380529693471/2251799813685248)), (30923221/2251799813685248), by norm_num⟩
  | 5 => ⟨((383692034860483/1125899906842624), (620889935276587/2251799813685248)), (52262793/2251799813685248), by norm_num⟩
  | 6 => ⟨((361264793606871/9007199254740992), (1692729673341853/9007199254740992)), (64441855/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13836261/8388608), (-1219320491/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-56791929/33554432), (-1251197185/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1520054568758099/9007199254740992), (661621121685785/9007199254740992)), (72713559/4503599627370496), by norm_num⟩
  | 1 => ⟨((-981422443/2147483648), (-213587667/1073741824)), (3/67108864), by norm_num⟩
  | 2 => ⟨((664435311/1073741824), (144601531/536870912)), (33/536870912), by norm_num⟩
  | 3 => ⟨((-299887363/536870912), (-522117607/2147483648)), (61/1073741824), by norm_num⟩
  | 4 => ⟨((406055017/1073741824), (353480173/2147483648)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((-109961737/536870912), (-382896821/4294967296)), (47/2147483648), by norm_num⟩
  | 6 => ⟨((794085077/8589934592), (86408651/2147483648)), (87/8589934592), by norm_num⟩
  | 7 => ⟨((-307203179/8589934592), (-66856847/4294967296)), (137/34359738368), by norm_num⟩
  | 8 => ⟨((831921631/68719476736), (90525849/17179869184)), (95/68719476736), by norm_num⟩
  | 9 => ⟨((-500641231/137438953472), (-435819633/274877906944)), (29/68719476736), by norm_num⟩
  | 10 => ⟨((1084609269/1099511627776), (236044289/549755813888)), (127/1099511627776), by norm_num⟩
  | 11 => ⟨((-1068064127/4398046511104), (-116221779/1099511627776)), (127/4398046511104), by norm_num⟩
  | 12 => ⟨((482061879/8796093022208), (419645883/17592186044416)), (117/17592186044416), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581771056014629/10141204801825835211973625643008), (534761115491/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444839518316963/158456325028528675187087900672), (633261051273/633825300114114700748351602688)), (92263/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472601186424387/9903520314283042199192993792), (712312493725/39614081257132168796771975168)), (12975/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890221169105367/2475880078570760549798248448), (47293834417/154742504910672534362390528)), (110291/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221485915950503/19342813113834066795298816), (94569298079/19342813113834066795298816)), (110297/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387551607219821/2417851639229258349412352), (709113623811/9671406556917033397649408)), (103409/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157419995623953/75557863725914323419136), (620318353647/604462909807314587353088)), (90489/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236090024487103/9444732965739290427392), (1007724793433/75557863725914323419136)), (147053/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((5071232060525/18446744073709551616), (188884431233/1180591620717411303424)), (27575/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811202396384849/295147905179352825856), (1038448760281/590295810358705651712)), (37919/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824670077006707/73786976294838206464), (648718921771/36893488147419103232)), (94809/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456000308967085/2305843009213693952), (729380653153/4611686018427387904)), (106675/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797624525367291/576460752303423488), (728845863747/576460752303423488)), (213389/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195685276611127/144115188075855872), (1274278023801/144115188075855872)), (186759/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493292618067173/36028797018963968), (1909015153813/36028797018963968)), (8757/1125899906842624), by norm_num⟩
  | 3 => ⟨((1491323983918443/9007199254740992), (1191035739019/4503599627370496)), (10951/281474976710656), by norm_num⟩
  | 2 => ⟨((1116036271889927/2251799813685248), (593946730857/562949953421312)), (87665/562949953421312), by norm_num⟩
  | 1 => ⟨((1111135049500025/1125899906842624), (7096019341725/2251799813685248)), (526563/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096492289659259/1125899906842624), (14067159857269/2251799813685248)), (1055433/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1096492289659259/1125899906842624), (14067159857269/2251799813685248)), (4026157383445357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((533904418469607/562949953421312), (6849868370695/562949953421312)), (2068919/1125899906842624), by norm_num⟩
  | 2 => ⟨((506274146809235/562949953421312), (25985791218725/1125899906842624)), (7949389/2251799813685248), by norm_num⟩
  | 3 => ⟨((910008766620873/1125899906842624), (93478535336707/2251799813685248)), (7332545/1125899906842624), by norm_num⟩
  | 4 => ⟨((733574442244017/1125899906842624), (75554040044141/1125899906842624)), (12461851/1125899906842624), by norm_num⟩
  | 5 => ⟨((945773325161221/2251799813685248), (196907424710925/2251799813685248)), (35822861/2251799813685248), by norm_num⟩
  | 6 => ⟨((1520054568758099/9007199254740992), (661621121685785/9007199254740992)), (72713559/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56791929/33554432), (-1251197185/33554432)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile037Terms1
