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
namespace Reinmann.XiRectangle.Tile036Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8601/640))
  have he : value ((7/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-64510795/33554432), (-495408345/16777216)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-409935302415067/9007199254740992), (1251709207883725/9007199254740992)), (171075403/9007199254740992), by norm_num⟩
  | 1 => ⟨((53687091/536870912), (-1311438673/4294967296)), (181/4294967296), by norm_num⟩
  | 2 => ⟨((-471850383/4294967296), (720381321/2147483648)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((172793543/2147483648), (-1055226363/4294967296)), (75/2147483648), by norm_num⟩
  | 4 => ⟨((-94916555/2147483648), (579642325/4294967296)), (167/8589934592), by norm_num⟩
  | 5 => ⟨((83421195/4294967296), (-509441745/8589934592)), (149/17179869184), by norm_num⟩
  | 6 => ⟨((-488786933/68719476736), (1492477231/68719476736)), (221/68719476736), by norm_num⟩
  | 7 => ⟨((19178119/8589934592), (-234236261/34359738368)), (141/137438953472), by norm_num⟩
  | 8 => ⟨((-337109075/549755813888), (1029339339/549755813888)), (157/549755813888), by norm_num⟩
  | 9 => ⟨((329201931/2199023255552), (-251298855/549755813888)), (155/2199023255552), by norm_num⟩
  | 10 => ⟨((-144666115/4398046511104), (883456033/8796093022208)), (69/4398046511104), by norm_num⟩
  | 11 => ⟨((231173777/35184372088832), (-1411746407/70368744177664)), (223/70368744177664), by norm_num⟩
  | 12 => ⟨((-5291049/4398046511104), (516987317/140737488355328)), (83/140737488355328), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403057283/10141204801825835211973625643008), (153650217783/633825300114114700748351602688)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1778998976685749/633825300114114700748351602688), (1455061388763/316912650057057350374175801344)), (69365/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890000580027177/39614081257132168796771975168), (1636664405919/19807040628566084398385987584)), (39025/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889791503860587/2475880078570760549798248448), (1738614463039/1237940039285380274899124224)), (81/2417851639229258349412352), by norm_num⟩
  | 14 => ⟨((442864348367993/38685626227668133590597632), (1738230381245/77371252455336267181195264)), (41481/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549803080136885/9671406556917033397649408), (3258365954777/9671406556917033397649408)), (19449/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78687921848279/37778931862957161709568), (2850254384485/604462909807314587353088)), (34045/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888145686436107/75557863725914323419136), (2315067046185/37778931862957161709568)), (55341/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297804058270423/4722366482869645213696), (867815709595/1180591620717411303424)), (83043/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621810929394125/590295810358705651712), (4770813323575/590295810358705651712)), (114235/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455981653014155/18446744073709551616), (2980129159635/36893488147419103232)), (71435/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455790819674981/2305843009213693952), (6700812484037/9223372036854775808)), (80417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199301143560369/144115188075855872), (6695217956089/1152921504606846976)), (80483/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194948179129117/144115188075855872), (5852026169035/144115188075855872)), (140993/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492182618818917/36028797018963968), (1095683865147/4503599627370496)), (105893/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489928896259499/9007199254740992), (5467434130599/4503599627370496)), (265253/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229259719194003/4503599627370496), (10901961052927/2251799813685248)), (532067/4503599627370496), by norm_num⟩
  | 1 => ⟨((277249330707043/281474976710656), (4067710713171/281474976710656)), (802013/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092105618937443/1125899906842624), (64428612695695/2251799813685248)), (809863/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1092105618937443/1125899906842624), (64428612695695/2251799813685248)), (3089382175925826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((529201980628563/562949953421312), (62494764870025/1125899906842624)), (3234907/2251799813685248), by norm_num⟩
  | 2 => ⟨((991485426710007/1125899906842624), (234993204260075/2251799813685248)), (1610269/562949953421312), by norm_num⟩
  | 3 => ⟨((107607023277081/140737488355328), (413877532067901/2251799813685248)), (12688585/2251799813685248), by norm_num⟩
  | 4 => ⟨((1240340666548111/2251799813685248), (316448231011829/1125899906842624)), (24067517/2251799813685248), by norm_num⟩
  | 5 => ⟨((126330838840055/562949953421312), (697226471724091/2251799813685248)), (40042785/2251799813685248), by norm_num⟩
  | 6 => ⟨((-409935302415067/9007199254740992), (1251709207883725/9007199254740992)), (171075403/9007199254740992), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/33554432), (-495408345/16777216)), (3/67108864), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-67604193/33554432), (-259581993/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((535079037008795/4503599627370496), (136352795452525/2251799813685248)), (110842599/9007199254740992), by norm_num⟩
  | 1 => ⟨((-146873595/536870912), (-598838643/4294967296)), (31/1073741824), by norm_num⟩
  | 2 => ⟨((676377901/2147483648), (344719233/2147483648)), (145/4294967296), by norm_num⟩
  | 3 => ⟨((-64892403/268435456), (-264581789/2147483648)), (113/4294967296), by norm_num⟩
  | 4 => ⟨((1195362239/8589934592), (609222083/8589934592)), (133/8589934592), by norm_num⟩
  | 5 => ⟨((-1100969309/17179869184), (-561114275/17179869184)), (125/17179869184), by norm_num⟩
  | 6 => ⟨((845025173/34359738368), (215335561/17179869184)), (49/17179869184), by norm_num⟩
  | 7 => ⟨((-1111852781/137438953472), (-566661089/137438953472)), (131/137438953472), by norm_num⟩
  | 8 => ⟨((320016955/137438953472), (40774543/34359738368)), (153/549755813888), by norm_num⟩
  | 9 => ⟨((-40937015/68719476736), (-667639857/2199023255552)), (159/2199023255552), by norm_num⟩
  | 10 => ⟨((603270147/4398046511104), (614919033/8796093022208)), (149/8796093022208), by norm_num⟩
  | 11 => ⟨((-1010240617/35184372088832), (-514873963/35184372088832)), (127/35184372088832), by norm_num⟩
  | 12 => ⟨((96923541/17592186044416), (395180371/140737488355328)), (25/35184372088832), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314710245/10141204801825835211973625643008), (613975020735/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778861081882617/633825300114114700748351602688), (726679295105/633825300114114700748351602688)), (5767/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((944922858785463/19807040628566084398385987584), (817370204777/39614081257132168796771975168)), (103811/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236203413626063/309485009821345068724781056), (868277384325/2475880078570760549798248448)), (3447/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((442823397042905/38685626227668133590597632), (868076690103/154742504910672534362390528)), (55155/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549649926334803/9671406556917033397649408), (406804361929/4835703278458516698824704)), (103423/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629436576700967/302231454903657293676544), (177923633209/151115727451828646838272)), (90501/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117995585452629/4722366482869645213696), (578052103251/37778931862957161709568)), (147075/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324410624020411/1180591620717411303424), (433364412889/2361183241434822606848)), (110317/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810794940404243/295147905179352825856), (595592382215/295147905179352825856)), (151703/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823651948646921/73786976294838206464), (744065202035/36893488147419103232)), (189655/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455714136121905/2305843009213693952), (52280563015/288230376151711744)), (53349/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398526309378103/288230376151711744), (1671518385655/1152921504606846976)), (3335/18014398509481984), by norm_num⟩
  | 5 => ⟨((597342713558075/72057594037927936), (1460938191505/144115188075855872)), (93405/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491794815840535/36028797018963968), (547032678141/9007199254740992)), (280315/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489455177368641/9007199254740992), (341179857613/1125899906842624)), (43821/1125899906842624), by norm_num⟩
  | 2 => ⟨((557086312557323/1125899906842624), (1360435493081/1125899906842624)), (701663/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216704890630865/2251799813685248), (8119905738131/2251799813685248)), (1053817/2251799813685248), by norm_num⟩
  | 0 => ⟨((545489172455611/562949953421312), (8034886614427/1125899906842624)), (2112967/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((545489172455611/562949953421312), (8034886614427/1125899906842624)), (8060329445845793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2114165180100121/2251799813685248), (31142687718091/2251799813685248)), (4125019/2251799813685248), by norm_num⟩
  | 2 => ⟨((992256175391553/1125899906842624), (7309795656365/281474976710656)), (7859879/2251799813685248), by norm_num⟩
  | 3 => ⟨((1747433109859151/2251799813685248), (51537013809469/1125899906842624)), (3565517/562949953421312), by norm_num⟩
  | 4 => ⟨((168914783175291/281474976710656), (79987114100119/1125899906842624)), (11720429/1125899906842624), by norm_num⟩
  | 5 => ⟨((99946123639599/281474976710656), (384005887640309/4503599627370496)), (31464603/2251799813685248), by norm_num⟩
  | 6 => ⟨((535079037008795/4503599627370496), (136352795452525/2251799813685248)), (110842599/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67604193/33554432), (-259581993/8388608)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-4400157/2097152), (-1081307155/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((762281136467351/9007199254740992), (-100000194050709/1125899906842624)), (63764965/4503599627370496), by norm_num⟩
  | 1 => ⟨((-871596495/4294967296), (914726229/4294967296)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((522499279/2147483648), (-548354425/2147483648)), (45/1073741824), by norm_num⟩
  | 3 => ⟨((-835265701/4294967296), (109574707/536870912)), (73/2147483648), by norm_num⟩
  | 4 => ⟨((500719919/4294967296), (-513181/4194304)), (177/8589934592), by norm_num⟩
  | 5 => ⟨((-960539141/17179869184), (504035039/8589934592)), (173/17179869184), by norm_num⟩
  | 6 => ⟨((383878711/17179869184), (-805748825/34359738368)), (35/8589934592), by norm_num⟩
  | 7 => ⟨((-526000541/68719476736), (276014471/34359738368)), (49/34359738368), by norm_num⟩
  | 8 => ⟨((630647105/274877906944), (-661853795/274877906944)), (15/34359738368), by norm_num⟩
  | 9 => ⟨((-168025079/274877906944), (705358261/1099511627776)), (65/549755813888), by norm_num⟩
  | 10 => ⟨((161162617/1099511627776), (-42284381/274877906944)), (127/4398046511104), by norm_num⟩
  | 11 => ⟨((-281055329/8796093022208), (589925919/17592186044416)), (7/1099511627776), by norm_num⟩
  | 12 => ⟨((449294163/70368744177664), (-943053715/140737488355328)), (181/140737488355328), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581242681581499/10141204801825835211973625643008), (-1054513496913/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778731965318319/633825300114114700748351602688), (-1247913417607/633825300114114700748351602688)), (92323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889700456407609/39614081257132168796771975168), (-1403645132335/39614081257132168796771975168)), (1623/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1889472960765081/2475880078570760549798248448), (-745526887051/1237940039285380274899124224)), (110373/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771139230665193/154742504910672534362390528), (-1490694825355/154742504910672534362390528)), (110383/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549505206350181/9671406556917033397649408), (-698572566027/4835703278458516698824704)), (103495/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314686628403777/151115727451828646838272), (-1222120854715/604462909807314587353088)), (90569/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887723559259793/75557863725914323419136), (-992616018625/37778931862957161709568)), (147195/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297488124104157/4722366482869645213696), (-744149624069/2361183241434822606848)), (55207/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621377593442103/590295810358705651712), (-2045396719831/590295810358705651712)), (151849/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823386550746209/73786976294838206464), (-1277612345583/36893488147419103232)), (189855/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911278959447781/4611686018427387904), (-179533599687/576460752303423488)), (213647/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796903273050361/576460752303423488), (-2869927084039/1152921504606846976)), (106861/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194423998595201/144115188075855872), (-2508252419733/144115188075855872)), (46773/36028797018963968), by norm_num⟩
  | 4 => ⟨((372850631815839/9007199254740992), (-3756518678923/36028797018963968)), (35101/4503599627370496), by norm_num⟩
  | 3 => ⟨((744482282183693/4503599627370496), (-1171352632059/2251799813685248)), (351309/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113681639400609/2251799813685248), (-583760991051/281474976710656)), (703517/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215230109705191/2251799813685248), (-3483472300217/562949953421312)), (1057529/2251799813685248), by norm_num⟩
  | 0 => ⟨((544750017545049/562949953421312), (-3445463319251/281474976710656)), (2124119/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((544750017545049/562949953421312), (-3445463319251/281474976710656)), (8102870949752043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1054108255777187/1125899906842624), (-13336291741075/562949953421312)), (4162897/2251799813685248), by norm_num⟩
  | 2 => ⟨((1972524877992063/2251799813685248), (-99887353327121/2251799813685248)), (7992149/2251799813685248), by norm_num⟩
  | 3 => ⟨((1723455560905987/2251799813685248), (-174998051103019/2251799813685248)), (3677731/562949953421312), by norm_num⟩
  | 4 => ⟨((326369459516575/562949953421312), (-66968955785553/562949953421312)), (12402527/1125899906842624), by norm_num⟩
  | 5 => ⟨((1449964529827723/4503599627370496), (-77650319611139/562949953421312)), (34663049/2251799813685248), by norm_num⟩
  | 6 => ⟨((762281136467351/9007199254740992), (-100000194050709/1125899906842624)), (63764965/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4400157/2097152), (-1081307155/33554432)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-72957177/33554432), (-1120544075/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-406390029095519/9007199254740992), (-29372559990319/281474976710656)), (90408189/4503599627370496), by norm_num⟩
  | 1 => ⟨((481529849/4294967296), (556854779/2147483648)), (217/4294967296), by norm_num⟩
  | 2 => ⟨((-299139181/2147483648), (-1383732143/4294967296)), (17/268435456), by norm_num⟩
  | 3 => ⟨((495555293/4294967296), (1146148401/4294967296)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((-615704321/8589934592), (-1424035891/8589934592)), (285/8589934592), by norm_num⟩
  | 5 => ⟨((19124597/536870912), (707719251/8589934592)), (143/8589934592), by norm_num⟩
  | 6 => ⟨((-506910275/34359738368), (-36637839/1073741824)), (239/34359738368), by norm_num⟩
  | 7 => ⟨((359892775/68719476736), (52023777/4294967296)), (171/68719476736), by norm_num⟩
  | 8 => ⟨((-447149975/274877906944), (-1034193835/274877906944)), (107/137438953472), by norm_num⟩
  | 9 => ⟨((246916877/549755813888), (142770841/137438953472)), (239/1099511627776), by norm_num⟩
  | 10 => ⟨((-61356539/549755813888), (-1135271079/4398046511104)), (15/274877906944), by norm_num⟩
  | 11 => ⟨((55441917/2199023255552), (256458423/4398046511104)), (219/17592186044416), by norm_num⟩
  | 12 => ⟨((-183690651/35184372088832), (-849700321/70368744177664)), (183/70368744177664), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790571753654357/5070602400912917605986812821504), (-2577724175159/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111163153865085/39614081257132168796771975168), (-381262590349/79228162514264337593543950336)), (92501/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236195444616479/4951760157141521099596496896), (-3430704380795/39614081257132168796771975168)), (52041/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889327231009175/2475880078570760549798248448), (-1779450239/1208925819614629174706176)), (55305/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885496596436403/77371252455336267181195264), (-3643403822885/154742504910672534362390528)), (110635/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774683984431783/4835703278458516698824704), (-213420259973/604462909807314587353088)), (103747/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258626104019703/604462909807314587353088), (-2986916978171/604462909807314587353088)), (45403/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((7373153443293/295147905179352825856), (-4851928157991/75557863725914323419136)), (147609/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648670190332823/2361183241434822606848), (-909340309253/1180591620717411303424)), (110751/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810586788853725/295147905179352825856), (-4998797315741/590295810358705651712)), (152353/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823130230137067/73786976294838206464), (-6244636899357/73786976294838206464)), (47637/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455566943092509/2305843009213693952), (-7019912339077/9223372036854775808)), (107257/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593514171700013/1152921504606846976), (-7013286587917/1152921504606846976)), (107349/576460752303423488), by norm_num⟩
  | 5 => ⟨((597082835355729/72057594037927936), (-6129177931793/144115188075855872)), (47017/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491010050038435/36028797018963968), (-1147360821409/4503599627370496)), (141259/18014398509481984), by norm_num⟩
  | 3 => ⟨((372116319361639/2251799813685248), (-1430950267789/1125899906842624)), (353875/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113169384847435/2251799813685248), (-22817324001971/4503599627370496)), (709935/4503599627370496), by norm_num⟩
  | 1 => ⟨((553407245514283/562949953421312), (-17015883883075/1125899906842624)), (1070381/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175543192056561/2251799813685248), (-67289555032223/2251799813685248)), (2162759/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2175543192056561/2251799813685248), (-67289555032223/2251799813685248)), (8250270852095793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099858196785583/2251799813685248), (-16252702888727/281474976710656)), (2154147/1125899906842624), by norm_num⟩
  | 2 => ⟨((975330666037941/1125899906842624), (-60624165919901/562949953421312)), (8532711/2251799813685248), by norm_num⟩
  | 3 => ⟨((1663680304879873/2251799813685248), (-420134029785769/2251799813685248)), (8310501/1125899906842624), by norm_num⟩
  | 4 => ⟨((575388526571609/1125899906842624), (-620808924946557/2251799813685248)), (15381067/1125899906842624), by norm_num⟩
  | 5 => ⟨((833896600436369/4503599627370496), (-1269051824008841/4503599627370496)), (12100935/562949953421312), by norm_num⟩
  | 6 => ⟨((-406390029095519/9007199254740992), (-29372559990319/281474976710656)), (90408189/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72957177/33554432), (-1120544075/33554432)), (1/16777216), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-75307241/33554432), (-1156638543/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-951137948072453/9007199254740992), (-165925342372149/18014398509481984)), (316848409/18014398509481984), by norm_num⟩
  | 1 => ⟨((1163301787/4294967296), (101468587/4294967296)), (195/4294967296), by norm_num⟩
  | 2 => ⟨((-745952543/2147483648), (-65065447/2147483648)), (63/1073741824), by norm_num⟩
  | 3 => ⟨((9965263/33554432), (55629859/2147483648)), (217/4294967296), by norm_num⟩
  | 4 => ⟨((-408966319/2147483648), (-142687771/8589934592)), (35/1073741824), by norm_num⟩
  | 5 => ⟨((419591159/4294967296), (146394763/17179869184)), (145/8589934592), by norm_num⟩
  | 6 => ⟨((-179371679/4294967296), (-125165051/34359738368)), (125/17179869184), by norm_num⟩
  | 7 => ⟨((1051609767/68719476736), (91726291/68719476736)), (185/68719476736), by norm_num⟩
  | 8 => ⟨((-674331449/137438953472), (-58818323/137438953472)), (15/17179869184), by norm_num⟩
  | 9 => ⟨((1537445349/1099511627776), (134103129/1099511627776)), (69/274877906944), by norm_num⟩
  | 10 => ⟨((-197173473/549755813888), (-68793547/2199023255552)), (285/4398046511104), by norm_num⟩
  | 11 => ⟨((735621779/8796093022208), (128328701/17592186044416)), (67/4398046511104), by norm_num⟩
  | 12 => ⟨((-628944203/35184372088832), (-109718873/70368744177664)), (231/70368744177664), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275821141/10141204801825835211973625643008), (-994735547069/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889247815212421/316912650057057350374175801344), (-588444040153/79228162514264337593543950336)), (11583/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((118089625671723/2475880078570760549798248448), (-5294928200885/39614081257132168796771975168)), (104277/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944594555861399/1237940039285380274899124224), (-5624569609785/2475880078570760549798248448)), (110829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770854538023649/154742504910672534362390528), (-5623116592207/154742504910672534362390528)), (110867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774618705661135/4835703278458516698824704), (-1317532045405/2417851639229258349412352)), (103979/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157313912252205/75557863725914323419136), (-288113673013/37778931862957161709568)), (91023/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887339657433483/75557863725914323419136), (-7488062136089/75557863725914323419136)), (147989/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297198732360401/4722366482869645213696), (-2806757702987/2361183241434822606848)), (27765/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101311081341207/36893488147419103232), (-3857235710245/295147905179352825856)), (76409/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822882623332473/73786976294838206464), (-9636922512961/73786976294838206464)), (191187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227748263804341/1152921504606846976), (-5416530591925/4611686018427387904)), (215313/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593228637320149/1152921504606846976), (-5411234685249/576460752303423488)), (107799/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193911482488747/144115188075855872), (-4728875204313/72057594037927936)), (23621/18014398509481984), by norm_num⟩
  | 4 => ⟨((372655025885473/9007199254740992), (-14162818817171/36028797018963968)), (142047/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487962742971295/9007199254740992), (-17661892746511/9007199254740992)), (356241/9007199254740992), by norm_num⟩
  | 2 => ⟨((556322159992103/1125899906842624), (-4399877267471/562949953421312)), (178965/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105970992546289/1125899906842624), (-6560881058895/281474976710656)), (541129/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085863535229157/1125899906842624), (-25932709425497/562949953421312)), (1099261/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1085863535229157/1125899906842624), (-25932709425497/562949953421312)), (4193347935203170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1044861615422631/1125899906842624), (-50021113535409/562949953421312)), (2221621/1125899906842624), by norm_num⟩
  | 2 => ⟨((240191721664629/281474976710656), (-185683083109631/1125899906842624)), (141195/35184372088832), by norm_num⟩
  | 3 => ⟨((789230728012313/1125899906842624), (-633797575007103/2251799813685248)), (18402831/2251799813685248), by norm_num⟩
  | 4 => ⟨((116009491017449/281474976710656), (-888555933782865/2251799813685248)), (18079685/1125899906842624), by norm_num⟩
  | 5 => ⟨((63765242802761/4503599627370496), (-183108500129031/562949953421312)), (58342899/2251799813685248), by norm_num⟩
  | 6 => ⟨((-951137948072453/9007199254740992), (-165925342372149/18014398509481984)), (316848409/18014398509481984), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75307241/33554432), (-1156638543/33554432)), (1/16777216), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-77483061/33554432), (-1190056799/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-549932436532241/9007199254740992), (705866742164207/9007199254740992)), (40665507/4503599627370496), by norm_num⟩
  | 1 => ⟨((346017653/2147483648), (-444131565/2147483648)), (105/4294967296), by norm_num⟩
  | 2 => ⟨((-913160423/4294967296), (586044331/2147483648)), (141/4294967296), by norm_num⟩
  | 3 => ⟨((200823559/1073741824), (-1031069725/4294967296)), (127/4294967296), by norm_num⟩
  | 4 => ⟨((-529984885/4294967296), (680263029/4294967296)), (43/2147483648), by norm_num⟩
  | 5 => ⟨((279732099/4294967296), (-718101253/8589934592)), (23/2147483648), by norm_num⟩
  | 6 => ⟨((-492152697/17179869184), (315851729/8589934592)), (83/17179869184), by norm_num⟩
  | 7 => ⟨((371091195/34359738368), (-952629509/68719476736)), (127/68719476736), by norm_num⟩
  | 8 => ⟨((-489665469/137438953472), (157127743/34359738368)), (85/137438953472), by norm_num⟩
  | 9 => ⟨((35895979/34359738368), (-368594775/274877906944)), (51/274877906944), by norm_num⟩
  | 10 => ⟨((-606281897/2199023255552), (389097097/1099511627776)), (55/1099511627776), by norm_num⟩
  | 11 => ⟨((290911397/4398046511104), (-746799669/8796093022208)), (27/2199023255552), by norm_num⟩
  | 12 => ⟨((-127955309/8796093022208), (656949047/35184372088832)), (97/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634167/10141204801825835211973625643008), (727070753355/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778401229407665/633825300114114700748351602688), (53757334511/9903520314283042199192993792)), (23135/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944664071095937/19807040628566084398385987584), (3869738835651/39614081257132168796771975168)), (52065/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889077060079867/2475880078570760549798248448), (513828477399/309485009821345068724781056)), (55331/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27667858967723/2417851639229258349412352), (4109537160299/154742504910672534362390528)), (55345/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549133337678033/9671406556917033397649408), (481441568259/1208925819614629174706176)), (51901/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629210375445383/302231454903657293676544), (52639574291/9444732965739290427392)), (45429/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887193487509613/75557863725914323419136), (342021545913/4722366482869645213696)), (73849/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297089952128053/4722366482869645213696), (2051179805021/2361183241434822606848)), (13853/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620829103853727/590295810358705651712), (2818829976857/295147905179352825856)), (9529/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911349718258463/36893488147419103232), (3521225198701/36893488147419103232)), (47675/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113861428360007/576460752303423488), (7916401555901/9223372036854775808)), (13419/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593028909860367/1152921504606846976), (494278940041/72057594037927936)), (1679/18014398509481984), by norm_num⟩
  | 5 => ⟨((149217585316667/18014398509481984), (3455490885237/72057594037927936)), (94141/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490371804786433/36028797018963968), (5174322235855/18014398509481984)), (141445/36028797018963968), by norm_num⟩
  | 3 => ⟨((743833073610739/4503599627370496), (12904648101627/9007199254740992)), (177217/9007199254740992), by norm_num⟩
  | 2 => ⟨((556184146093591/1125899906842624), (1607249439835/281474976710656)), (88917/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105608026320075/1125899906842624), (38341309011647/2251799813685248)), (536595/2251799813685248), by norm_num⟩
  | 0 => ⟨((135667480422907/140737488355328), (75755418653125/2251799813685248)), (1085613/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((135667480422907/140737488355328), (75755418653125/2251799813685248)), (4141284951216887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089933301568015/2251799813685248), (73026362038689/1125899906842624)), (1083027/1125899906842624), by norm_num⟩
  | 2 => ⟨((482557305979965/562949953421312), (271107982138507/2251799813685248)), (2150843/1125899906842624), by norm_num⟩
  | 3 => ⟨((101371281338443/140737488355328), (116196063873295/562949953421312)), (2102643/562949953421312), by norm_num⟩
  | 4 => ⟨((1072327376217553/2251799813685248), (669555440783795/2251799813685248)), (3897005/562949953421312), by norm_num⟩
  | 5 => ⟨((623129559953419/4503599627370496), (318848338419941/1125899906842624)), (24116269/2251799813685248), by norm_num⟩
  | 6 => ⟨((-549932436532241/9007199254740992), (705866742164207/9007199254740992)), (40665507/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77483061/33554432), (-1190056799/33554432)), (1/33554432), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-79508701/33554432), (-305292113/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((441809571082431/18014398509481984), (1625805936454253/18014398509481984)), (62121967/4503599627370496), by norm_num⟩
  | 1 => ⟨((-35656765/536870912), (-1049700759/4294967296)), (81/2147483648), by norm_num⟩
  | 2 => ⟨((193120619/2147483648), (177665147/536870912)), (111/2147483648), by norm_num⟩
  | 3 => ⟨((-174326777/2147483648), (-160375379/536870912)), (101/2147483648), by norm_num⟩
  | 4 => ⟨((14752677/268435456), (868609155/4294967296)), (139/4294967296), by norm_num⟩
  | 5 => ⟨((-255686335/8589934592), (-940894879/8589934592)), (153/8589934592), by norm_num⟩
  | 6 => ⟨((115401905/8589934592), (849330189/17179869184)), (35/4294967296), by norm_num⟩
  | 7 => ⟨((-357159031/68719476736), (-1314302165/68719476736)), (109/34359738368), by norm_num⟩
  | 8 => ⟨((120900573/68719476736), (222449765/34359738368)), (75/68719476736), by norm_num⟩
  | 9 => ⟨((-72756627/137438953472), (-1070942455/549755813888)), (183/549755813888), by norm_num⟩
  | 10 => ⟨((315245757/2199023255552), (290016593/549755813888)), (25/274877906944), by norm_num⟩
  | 11 => ⟨((-310436849/8796093022208), (-1142370171/8796093022208)), (199/8796093022208), by norm_num⟩
  | 12 => ⟨((140113095/17592186044416), (515599295/17592186044416)), (91/17592186044416), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580889171562799/10141204801825835211973625643008), (1700502125739/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778312380291767/633825300114114700748351602688), (1005738162053/316912650057057350374175801344)), (92399/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889228441132241/39614081257132168796771975168), (565610886413/9903520314283042199192993792)), (103961/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472242865139885/618970019642690137449562112), (2403265179803/2475880078570760549798248448)), (110473/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442659437138605/38685626227668133590597632), (2402611703371/154742504910672534362390528)), (55245/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774517543070699/4835703278458516698824704), (2251754379529/9671406556917033397649408)), (51801/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258335177752485/604462909807314587353088), (984795622169/302231454903657293676544)), (45335/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471763793703569/18889465931478580854784), (199955335447/4722366482869645213696)), (73685/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81061679229117/295147905179352825856), (2398326711737/4722366482869645213696)), (110557/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620688417868739/590295810358705651712), (1647926053621/295147905179352825856)), (152063/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911262579835161/36893488147419103232), (4117046224173/73786976294838206464)), (190149/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910794481142667/4611686018427387904), (4627872629139/9223372036854775808)), (214015/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592837725770667/1152921504606846976), (2311560738343/576460752303423488)), (214137/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149197054409667/18014398509481984), (2019946085997/72057594037927936)), (187507/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490131494109717/36028797018963968), (6049174818311/36028797018963968)), (281535/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487376325076665/9007199254740992), (7542840762121/9007199254740992)), (352399/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224188482406657/4503599627370496), (15029931064209/4503599627370496)), (706245/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210472210150771/2251799813685248), (22405984369487/2251799813685248)), (1062995/2251799813685248), by norm_num⟩
  | 0 => ⟨((542375496174187/562949953421312), (22129547872651/1125899906842624)), (1070285/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542375496174187/562949953421312), (22129547872651/1125899906842624)), (4082813267234420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1044671015037343/1125899906842624), (21320766499037/562949953421312)), (2104411/1125899906842624), by norm_num⟩
  | 2 => ⟨((1935374934665515/2251799813685248), (158260510687023/2251799813685248)), (63509/17592186044416), by norm_num⟩
  | 3 => ⟨((1652291525150953/2251799813685248), (272043210652687/2251799813685248)), (15116337/2251799813685248), by norm_num⟩
  | 4 => ⟨((294881871767787/562949953421312), (49903935587935/281474976710656)), (807379/70368744177664), by norm_num⟩
  | 5 => ⟨((1094146386273771/4503599627370496), (836494446886567/4503599627370496)), (36227927/2251799813685248), by norm_num⟩
  | 6 => ⟨((441809571082431/18014398509481984), (1625805936454253/18014398509481984)), (62121967/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-79508701/33554432), (-305292113/8388608)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile036Terms1
