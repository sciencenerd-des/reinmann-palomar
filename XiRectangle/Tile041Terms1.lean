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
namespace Reinmann.XiRectangle.Tile041Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨41,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/16), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((11/16), (17907/1280))
  have he : value ((11/16), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-50687053/33554432), (-257855983/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((774952745081529/4503599627370496), (77870436718161/562949953421312)), (104844519/4503599627370496), by norm_num⟩
  | 1 => ⟨((-811932191/2147483648), (-652690267/2147483648)), (7/134217728), by norm_num⟩
  | 2 => ⟨((891998683/2147483648), (179263387/536870912)), (125/2147483648), by norm_num⟩
  | 3 => ⟨((-653307143/2147483648), (-525175893/2147483648)), (93/2147483648), by norm_num⟩
  | 4 => ⟨((89716407/536870912), (288482345/2147483648)), (13/536870912), by norm_num⟩
  | 5 => ⟨((-315403351/4294967296), (-507088399/8589934592)), (93/8589934592), by norm_num⟩
  | 6 => ⟨((924015993/34359738368), (185697849/8589934592)), (139/34359738368), by norm_num⟩
  | 7 => ⟨((-1160154657/137438953472), (-29144277/4294967296)), (177/137438953472), by norm_num⟩
  | 8 => ⟨((318640041/137438953472), (256146087/137438953472)), (99/274877906944), by norm_num⟩
  | 9 => ⟨((-155583051/274877906944), (-125068995/274877906944)), (99/1099511627776), by norm_num⟩
  | 10 => ⟨((1093922891/8796093022208), (879374943/8796093022208)), (177/8796093022208), by norm_num⟩
  | 11 => ⟨((-874034277/35184372088832), (-351306225/17592186044416)), (9/2199023255552), by norm_num⟩
  | 12 => ⟨((640149865/140737488355328), (514599115/140737488355328)), (107/140737488355328), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49437751640765/316912650057057350374175801344), (881995738239/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889819198226017/316912650057057350374175801344), (261191930291/158456325028528675187087900672)), (92303/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945360021577263/19807040628566084398385987584), (1175206420195/39614081257132168796771975168)), (103847/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890556090659501/2475880078570760549798248448), (312116087651/618970019642690137449562112)), (55173/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886111078473769/77371252455336267181195264), (312061967841/38685626227668133590597632)), (55177/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550520233445093/9671406556917033397649408), (1170002419831/9671406556917033397649408)), (51733/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259634446076775/604462909807314587353088), (511761106801/302231454903657293676544)), (45271/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944583022075443/37778931862957161709568), (103924540385/4722366482869645213696)), (36787/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649284816593041/2361183241434822606848), (311679380275/1180591620717411303424)), (13797/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622864092419635/590295810358705651712), (856812124003/295147905179352825856)), (151791/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825243810790241/73786976294838206464), (2141112183475/73786976294838206464)), (189775/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228080768679497/1152921504606846976), (1203744706913/4611686018427387904)), (53387/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797946646850729/576460752303423488), (300739139963/144115188075855872)), (213611/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598124117784107/72057594037927936), (2103401949643/144115188075855872)), (186981/144115188075855872), by norm_num⟩
  | 4 => ⟨((186766943898785/4503599627370496), (3151562113849/36028797018963968)), (70153/9007199254740992), by norm_num⟩
  | 3 => ⟨((746187510220987/4503599627370496), (3933263528725/9007199254740992)), (351013/9007199254740992), by norm_num⟩
  | 2 => ⟨((2234166744824933/4503599627370496), (3923994451917/2251799813685248)), (702773/4503599627370496), by norm_num⟩
  | 1 => ⟨((556347945544351/562949953421312), (11725739979189/2251799813685248)), (33001/70368744177664), by norm_num⟩
  | 0 => ⟨((2199149840825289/2251799813685248), (23267117318271/2251799813685248)), (2119577/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2199149840825289/2251799813685248), (23267117318271/2251799813685248)), (8085544594771575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((536872620099781/562949953421312), (22723102220707/1125899906842624)), (130745/70368744177664), by norm_num⟩
  | 2 => ⟨((255886978601057/281474976710656), (21670507923279/562949953421312)), (4074473/1125899906842624), by norm_num⟩
  | 3 => ⟨((928832024117761/1125899906842624), (157604085792347/2251799813685248)), (3860921/562949953421312), by norm_num⟩
  | 4 => ⟨((1521483680488143/2251799813685248), (260036831206873/2251799813685248)), (6910731/562949953421312), by norm_num⟩
  | 5 => ⟨((498999383237749/1125899906842624), (351400504256733/2251799813685248)), (43739623/2251799813685248), by norm_num⟩
  | 6 => ⟨((774952745081529/4503599627370496), (77870436718161/562949953421312)), (104844519/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50687053/33554432), (-257855983/8388608)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-13279395/8388608), (-540441199/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((323199712118449/2251799813685248), (-661415088139349/4503599627370496)), (52543287/2251799813685248), by norm_num⟩
  | 1 => ⟨((-709719505/2147483648), (726206075/2147483648)), (117/2147483648), by norm_num⟩
  | 2 => ⟨((102136847/268435456), (-836075641/2147483648)), (137/2147483648), by norm_num⟩
  | 3 => ⟨((-627143417/2147483648), (641711769/2147483648)), (107/2147483648), by norm_num⟩
  | 4 => ⟨((361012771/2147483648), (-738797977/4294967296)), (125/4294967296), by norm_num⟩
  | 5 => ⟨((-166252525/2147483648), (170114521/2147483648)), (117/8589934592), by norm_num⟩
  | 6 => ⟨((1020828229/34359738368), (-1044541761/34359738368)), (91/17179869184), by norm_num⟩
  | 7 => ⟨((-671583961/68719476736), (343592327/34359738368)), (61/34359738368), by norm_num⟩
  | 8 => ⟨((773189609/274877906944), (-395575285/137438953472)), (143/274877906944), by norm_num⟩
  | 9 => ⟨((-791259941/1099511627776), (809640671/1099511627776)), (149/1099511627776), by norm_num⟩
  | 10 => ⟨((364388669/2199023255552), (-93213327/549755813888)), (139/4398046511104), by norm_num⟩
  | 11 => ⟨((-152551985/4398046511104), (624382887/17592186044416)), (59/8796093022208), by norm_num⟩
  | 12 => ⟨((234175951/35184372088832), (-59903947/8796093022208)), (23/17592186044416), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197739212171833/1267650600228229401496703205376), (-1038024068129/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779526410200849/633825300114114700748351602688), (-307361041525/158456325028528675187087900672)), (92321/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945297031460197/19807040628566084398385987584), (-1382930912083/39614081257132168796771975168)), (103869/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890422241210895/2475880078570760549798248448), (-734563367793/1237940039285380274899124224)), (55185/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886044156312103/77371252455336267181195264), (-1468859771255/154742504910672534362390528)), (27595/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193799344980291/1208925819614629174706176), (-1376772448881/9671406556917033397649408)), (25873/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314881165532517/151115727451828646838272), (-1204392376897/604462909807314587353088)), (90567/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944493827739157/37778931862957161709568), (-489151542649/18889465931478580854784)), (147191/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298435850653735/4722366482869645213696), (-366747441669/1180591620717411303424)), (110411/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811340078019283/295147905179352825856), (-1008177905719/295147905179352825856)), (151843/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825013912252459/73786976294838206464), (-1259656290345/36893488147419103232)), (94923/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824387543806847/9223372036854775808), (-2832670701593/9223372036854775808)), (53409/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595634725945087/1152921504606846976), (-2830726962533/1152921504606846976)), (213711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598011015756173/72057594037927936), (-1237350517757/72057594037927936)), (23385/18014398509481984), by norm_num⟩
  | 4 => ⟨((746898165439007/18014398509481984), (-3707685561187/36028797018963968)), (280787/36028797018963968), by norm_num⟩
  | 3 => ⟨((745975572923367/4503599627370496), (-2313487864997/4503599627370496)), (87819/2251799813685248), by norm_num⟩
  | 2 => ⟨((2233319450790599/4503599627370496), (-9231094812599/4503599627370496)), (351715/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224121988675047/2251799813685248), (-3447407493347/562949953421312)), (1057349/2251799813685248), by norm_num⟩
  | 0 => ⟨((1098307450828247/1125899906842624), (-27351985709805/2251799813685248)), (2123537/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1098307450828247/1125899906842624), (-27351985709805/2251799813685248)), (8100650795943450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2142450170631127/2251799813685248), (-53363339880311/2251799813685248)), (1048645/562949953421312), by norm_num⟩
  | 2 => ⟨((2037146046338273/2251799813685248), (-50771962914817/1125899906842624)), (4090291/1125899906842624), by norm_num⟩
  | 3 => ⟨((919187580547823/1125899906842624), (-45932104127623/562949953421312)), (15539329/2251799813685248), by norm_num⟩
  | 4 => ⟨((1485863477546085/2251799813685248), (-299992703834139/2251799813685248)), (27908461/2251799813685248), by norm_num⟩
  | 5 => ⟨((940489753432251/2251799813685248), (-395903933776373/2251799813685248)), (44267255/2251799813685248), by norm_num⟩
  | 6 => ⟨((323199712118449/2251799813685248), (-661415088139349/4503599627370496)), (52543287/2251799813685248), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13279395/8388608), (-540441199/16777216)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-13829065/8388608), (-562811511/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-459698341372107/4503599627370496), (-734115114090517/4503599627370496)), (154575357/4503599627370496), by norm_num⟩
  | 1 => ⟨((525621643/2147483648), (839391309/2147483648)), (179/2147483648), by norm_num⟩
  | 2 => ⟨((-630192827/2147483648), (-503193113/1073741824)), (217/2147483648), by norm_num⟩
  | 3 => ⟨((251856067/1073741824), (804402925/2147483648)), (11/134217728), by norm_num⟩
  | 4 => ⟨((-75490559/536870912), (-482218493/2147483648)), (107/2147483648), by norm_num⟩
  | 5 => ⟨((579259055/8589934592), (231261889/2147483648)), (207/8589934592), by norm_num⟩
  | 6 => ⟨((-231500425/8589934592), (-369694527/8589934592)), (167/17179869184), by norm_num⟩
  | 7 => ⟨((634415743/68719476736), (506565005/34359738368)), (231/68719476736), by norm_num⟩
  | 8 => ⟨((-95078907/34359738368), (-1214689831/274877906944)), (35/34359738368), by norm_num⟩
  | 9 => ⟨((405314243/549755813888), (1294532891/1099511627776)), (301/1099511627776), by norm_num⟩
  | 10 => ⟨((-388760443/2199023255552), (-155207715/549755813888)), (291/4398046511104), by norm_num⟩
  | 11 => ⟨((677968603/17592186044416), (541340867/8796093022208)), (1/68719476736), by norm_num⟩
  | 12 => ⟨((-135474809/17592186044416), (-216346451/17592186044416)), (103/35184372088832), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581828342743005/10141204801825835211973625643008), (-2774893226773/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889710178025987/316912650057057350374175801344), (-3286251022043/633825300114114700748351602688)), (23131/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472618620507313/9903520314283042199192993792), (-3696483549067/39614081257132168796771975168)), (52055/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890294840902871/2475880078570760549798248448), (-3926851876653/2475880078570760549798248448)), (110641/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771960523736257/154742504910672534362390528), (-3926107291139/154742504910672534362390528)), (27667/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193784318138807/1208925819614629174706176), (-1839967276477/4835703278458516698824704)), (25945/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259419061834037/604462909807314587353088), (-804787950513/151115727451828646838272)), (22709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((29512738785227/1180591620717411303424), (-5229638895351/75557863725914323419136)), (73831/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298305895103643/4722366482869645213696), (-3920931950631/4722366482869645213696)), (55397/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622500370224919/590295810358705651712), (-82232267/9007199254740992)), (76209/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57024610508871/2305843009213693952), (-1683326660879/18446744073709551616)), (190637/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912065306754189/4611686018427387904), (-946328149833/1152921504606846976)), (214625/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595374978110193/1152921504606846976), (-1891298987083/288230376151711744)), (214823/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195791588103597/144115188075855872), (-3306720457087/72057594037927936)), (188193/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493444351832699/36028797018963968), (-9907956213063/36028797018963968)), (17671/2251799813685248), by norm_num⟩
  | 3 => ⟨((1491500154512537/9007199254740992), (-12363599588307/9007199254740992)), (354201/9007199254740992), by norm_num⟩
  | 2 => ⟨((139524033922715/281474976710656), (-12331607823737/2251799813685248)), (355375/2251799813685248), by norm_num⟩
  | 1 => ⟨((555659439415143/562949953421312), (-9208763101751/562949953421312)), (268001/562949953421312), by norm_num⟩
  | 0 => ⟨((1096660811694811/1125899906842624), (-18258037755293/562949953421312)), (1083797/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1096660811694811/1125899906842624), (-18258037755293/562949953421312)), (4134357456687545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1066996723985293/1125899906842624), (-35567770070831/562949953421312)), (2181605/1125899906842624), by norm_num⟩
  | 2 => ⟨((1006680733372269/1125899906842624), (-67413975104527/562949953421312)), (551327/140737488355328), by norm_num⟩
  | 3 => ⟨((1767879216859133/2251799813685248), (-482205208369387/2251799813685248)), (17887049/2251799813685248), by norm_num⟩
  | 4 => ⟨((1284694600666779/2251799813685248), (-757154842057043/2251799813685248)), (35746847/2251799813685248), by norm_num⟩
  | 5 => ⟨((478353695379829/2251799813685248), (-863942461978865/2251799813685248)), (16206965/562949953421312), by norm_num⟩
  | 6 => ⟨((-459698341372107/4503599627370496), (-734115114090517/4503599627370496)), (154575357/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13829065/8388608), (-562811511/16777216)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-7165437/4194304), (-291617003/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1597267462254825/9007199254740992), (333666066521565/9007199254740992)), (277251491/9007199254740992), by norm_num⟩
  | 1 => ⟨((473148887/1073741824), (-197679765/2147483648)), (83/1073741824), by norm_num⟩
  | 2 => ⟨((-1175730815/2147483648), (245607881/2147483648)), (13/134217728), by norm_num⟩
  | 3 => ⟨((121732555/268435456), (-12714847/134217728)), (87/1073741824), by norm_num⟩
  | 4 => ⟨((-1209976141/4294967296), (252761663/4294967296)), (109/2147483648), by norm_num⟩
  | 5 => ⟨((1202671103/8589934592), (-251235655/8589934592)), (219/8589934592), by norm_num⟩
  | 6 => ⟨((-249043785/4294967296), (104049525/8589934592)), (183/17179869184), by norm_num⟩
  | 7 => ⟨((176814445/8589934592), (-147744775/34359738368)), (131/34359738368), by norm_num⟩
  | 8 => ⟨((-219683695/34359738368), (183565987/137438953472)), (41/34359738368), by norm_num⟩
  | 9 => ⟨((121309661/68719476736), (-202730819/549755813888)), (183/549755813888), by norm_num⟩
  | 10 => ⟨((-482309093/1099511627776), (12594179/137438953472)), (23/274877906944), by norm_num⟩
  | 11 => ⟨((871631325/8796093022208), (-364164179/17592186044416)), (335/17592186044416), by norm_num⟩
  | 12 => ⟨((-1443948317/70368744177664), (301637997/70368744177664)), (35/8796093022208), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395437605032651/2535301200456458802993406410752), (3824019830817/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444830722045977/158456325028528675187087900672), (4528264069781/633825300114114700748351602688)), (46323/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945182274307697/19807040628566084398385987584), (2546750056321/19807040628566084398385987584)), (104255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945088836833375/1237940039285380274899124224), (5410897078485/2475880078570760549798248448)), (27701/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885921474187025/77371252455336267181195264), (5409831811799/154742504910672534362390528)), (110841/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550163884818581/9671406556917033397649408), (5070585485993/9671406556917033397649408)), (51977/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259321800963205/604462909807314587353088), (4435630471749/604462909807314587353088)), (90999/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888656421830907/75557863725914323419136), (3602888678961/37778931862957161709568)), (147947/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298186040298795/4722366482869645213696), (5402476149901/4722366482869645213696)), (55513/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622334418044223/590295810358705651712), (7425387333927/590295810358705651712)), (76383/295147905179352825856), by norm_num⟩
  | 8 => ⟨((14254518517449/576460752303423488), (1159651022499/9223372036854775808)), (47779/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823892931798289/9223372036854775808), (10430636089209/9223372036854775808)), (215223/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595134338677341/1152921504606846976), (10422857384185/1152921504606846976)), (215497/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195577707561893/144115188075855872), (9111249436651/144115188075855872)), (188867/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493116904937067/36028797018963968), (3412343328451/9007199254740992)), (70979/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491079286210695/9007199254740992), (17031091862367/9007199254740992)), (355973/9007199254740992), by norm_num⟩
  | 2 => ⟨((278938533857563/562949953421312), (16985158325115/2251799813685248)), (357593/2251799813685248), by norm_num⟩
  | 1 => ⟨((138827344637539/140737488355328), (12681458736497/562949953421312)), (16889/35184372088832), by norm_num⟩
  | 0 => ⟨((1095090403038709/1125899906842624), (12566661686487/281474976710656)), (1097183/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1095090403038709/1125899906842624), (12566661686487/281474976710656)), (4185420994285201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1062879788673499/1125899906842624), (97782266629353/1125899906842624)), (69759/35184372088832), by norm_num⟩
  | 2 => ⟨((994894898468111/1125899906842624), (46154544582243/281474976710656)), (4602421/1125899906842624), by norm_num⟩
  | 3 => ⟨((848860526073349/1125899906842624), (326273557121173/1125899906842624)), (1205395/140737488355328), by norm_num⟩
  | 4 => ⟨((1090878069918623/2251799813685248), (983962221360819/2251799813685248)), (20129687/1125899906842624), by norm_num⟩
  | 5 => ⟨((197027559036001/4503599627370496), (1906710893903585/4503599627370496)), (37095559/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1597267462254825/9007199254740992), (333666066521565/9007199254740992)), (277251491/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7165437/4194304), (-291617003/8388608)), (1/16777216), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-59169975/33554432), (-1204041761/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-93677699857573/2251799813685248), (1498231117786783/9007199254740992)), (65761745/2251799813685248), by norm_num⟩
  | 1 => ⟨((7160859/67108864), (-916215645/2147483648)), (163/2147483648), by norm_num⟩
  | 2 => ⟨((-293875851/2147483648), (1175023365/2147483648)), (211/2147483648), by norm_num⟩
  | 3 => ⟨((62814723/536870912), (-502312571/1073741824)), (91/1073741824), by norm_num⟩
  | 4 => ⟨((-322233167/4294967296), (644203153/2147483648)), (59/1073741824), by norm_num⟩
  | 5 => ⟨((165302351/4294967296), (-1321878771/8589934592)), (61/2147483648), by norm_num⟩
  | 6 => ⟨((-282661439/17179869184), (1130184035/17179869184)), (211/17179869184), by norm_num⟩
  | 7 => ⟨((414292729/68719476736), (-414123545/17179869184)), (39/8589934592), by norm_num⟩
  | 8 => ⟨((-265659967/137438953472), (1062205921/137438953472)), (101/68719476736), by norm_num⟩
  | 9 => ⟨((302846383/549755813888), (-605445421/274877906944)), (29/68719476736), by norm_num⟩
  | 10 => ⟨((-155357127/1099511627776), (1242349475/2199023255552)), (15/137438953472), by norm_num⟩
  | 11 => ⟨((289805937/8796093022208), (-1158750359/8796093022208)), (113/4398046511104), by norm_num⟩
  | 12 => ⟨((-15486199/2199023255552), (247677999/8796093022208)), (195/35184372088832), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790839369120983/5070602400912917605986812821504), (1182687434203/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889622388661339/316912650057057350374175801344), (2800735960217/633825300114114700748351602688)), (23119/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890277078290469/39614081257132168796771975168), (3150332392311/39614081257132168796771975168)), (104053/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236260656578531/309485009821345068724781056), (1673312616425/1237940039285380274899124224)), (110577/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110734444234079/9671406556917033397649408), (1672973517793/77371252455336267181195264)), (13825/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550078400601175/9671406556917033397649408), (3136104887637/9671406556917033397649408)), (3241/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((629623809146519/302231454903657293676544), (342921432567/75557863725914323419136)), (22693/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944268514640789/37778931862957161709568), (4456628332521/75557863725914323419136)), (147551/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298097505142489/4722366482869645213696), (3341290046833/4722366482869645213696)), (110703/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622214320842977/590295810358705651712), (4592354926391/590295810358705651712)), (76141/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912215352118653/36893488147419103232), (5737566316787/73786976294838206464)), (190451/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113983136243005/576460752303423488), (6450807372371/9223372036854775808)), (26799/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398743949052927/288230376151711744), (6445866370199/1152921504606846976)), (214561/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597721855158683/72057594037927936), (5634577767797/144115188075855872)), (187931/144115188075855872), by norm_num⟩
  | 4 => ⟨((373231335843677/9007199254740992), (8440764343381/36028797018963968)), (70569/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490856298142927/9007199254740992), (658221567205/562949953421312)), (44189/1125899906842624), by norm_num⟩
  | 2 => ⟨((1115555750959259/2251799813685248), (5251233459915/1125899906842624)), (354513/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110382366867863/1125899906842624), (15681135823899/1125899906842624)), (133569/281474976710656), by norm_num⟩
  | 0 => ⟨((1094860435706439/1125899906842624), (31072798564887/1125899906842624)), (1078609/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1094860435706439/1125899906842624), (31072798564887/1125899906842624)), (4114566807273482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2127638252006817/2251799813685248), (15108082685065/281474976710656)), (4314565/2251799813685248), by norm_num⟩
  | 2 => ⟨((1001917718792061/1125899906842624), (228400655794489/2251799813685248)), (8616497/2251799813685248), by norm_num⟩
  | 3 => ⟨((1760009738549771/2251799813685248), (50812390744831/281474976710656)), (8541637/1125899906842624), by norm_num⟩
  | 4 => ⟨((1302243975047585/2251799813685248), (317720259168293/1125899906842624)), (16436215/1125899906842624), by norm_num⟩
  | 5 => ⟨((71723444861275/281474976710656), (734966386866039/2251799813685248)), (56573767/2251799813685248), by norm_num⟩
  | 6 => ⟨((-93677699857573/2251799813685248), (1498231117786783/9007199254740992)), (65761745/2251799813685248), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-59169975/33554432), (-1204041761/33554432)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-15219887/8388608), (-1238829619/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1044298458089663/9007199254740992), (64453210063615/562949953421312)), (20703031/1125899906842624), by norm_num⟩
  | 1 => ⟨((-328536451/1073741824), (-40553979/134217728)), (53/1073741824), by norm_num⟩
  | 2 => ⟨((867026529/2147483648), (214048551/536870912)), (71/1073741824), by norm_num⟩
  | 3 => ⟨((-762710905/2147483648), (-753181863/2147483648)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((503209451/2147483648), (496922529/2147483648)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((-132799859/1073741824), (-524562817/4294967296)), (91/4294967296), by norm_num⟩
  | 6 => ⟨((116822147/2147483648), (461450449/8589934592)), (163/17179869184), by norm_num⟩
  | 7 => ⟨((-704686499/34359738368), (-347941197/17179869184)), (125/34359738368), by norm_num⟩
  | 8 => ⟨((929854035/137438953472), (459118383/68719476736)), (167/137438953472), by norm_num⟩
  | 9 => ⟨((-545319579/274877906944), (-134626637/68719476736)), (25/68719476736), by norm_num⟩
  | 10 => ⟨((575651853/1099511627776), (568459861/1099511627776)), (107/1099511627776), by norm_num⟩
  | 11 => ⟨((-552428451/4398046511104), (-136381651/1099511627776)), (105/4398046511104), by norm_num⟩
  | 12 => ⟨((485963451/17592186044416), (239945997/8796093022208)), (187/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395403092790235/2535301200456458802993406410752), (1014880569187/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889584810333561/316912650057057350374175801344), (300393572051/158456325028528675187087900672)), (46159/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((14767130759927/309485009821345068724781056), (1351555270759/39614081257132168796771975168)), (51933/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889995909285919/2475880078570760549798248448), (717880829355/1237940039285380274899124224)), (110367/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771662066830303/154742504910672534362390528), (1435462702561/154742504910672534362390528)), (110377/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774997622952537/4835703278458516698824704), (672714362755/4835703278458516698824704)), (103489/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629587589453653/302231454903657293676544), (1176932669797/604462909807314587353088)), (90563/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944209958352399/37778931862957161709568), (1911920539309/75557863725914323419136)), (9199/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((649005098278495/2361183241434822606848), (179177491781/590295810358705651712)), (55203/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405523781322543/147573952589676412928), (1970107016067/590295810358705651712)), (151835/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912141494557145/36893488147419103232), (307670791007/9223372036854775808)), (47459/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823565757309045/9223372036854775808), (1383647719561/4611686018427387904)), (213623/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199351695826431/144115188075855872), (1382559958735/576460752303423488)), (3339/18014398509481984), by norm_num⟩
  | 5 => ⟨((597652111068723/72057594037927936), (2417034634435/144115188075855872)), (93533/72057594037927936), by norm_num⟩
  | 4 => ⟨((746360512803143/18014398509481984), (3620666781365/36028797018963968)), (140381/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490609476732253/9007199254740992), (2258648301147/4503599627370496)), (43905/1125899906842624), by norm_num⟩
  | 2 => ⟨((557660872090705/1125899906842624), (9009031209073/4503599627370496)), (175835/1125899906842624), by norm_num⟩
  | 1 => ⟨((2220126443892785/2251799813685248), (13449811722367/2251799813685248)), (1057171/2251799813685248), by norm_num⟩
  | 0 => ⟨((2188697164002135/2251799813685248), (13322850036373/1125899906842624)), (2123021/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2188697164002135/2251799813685248), (13322850036373/1125899906842624)), (8098682412154387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((531761888120499/562949953421312), (51798004269861/2251799813685248)), (4177299/2251799813685248), by norm_num⟩
  | 2 => ⟨((62750475056013/70368744177664), (97856672281491/2251799813685248)), (8083925/2251799813685248), by norm_num⟩
  | 3 => ⟨((1786370661313899/2251799813685248), (10907812738495/140737488355328)), (15120093/2251799813685248), by norm_num⟩
  | 4 => ⟨((1403615518323291/2251799813685248), (276904140934469/2251799813685248)), (822923/70368744177664), by norm_num⟩
  | 5 => ⟨((420432715311515/1125899906842624), (86301399205535/562949953421312)), (39305471/2251799813685248), by norm_num⟩
  | 6 => ⟨((1044298458089663/9007199254740992), (64453210063615/562949953421312)), (20703031/1125899906842624), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15219887/8388608), (-1238829619/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-31235561/16777216), (-317804085/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1375509965677771/9007199254740992), (-258961067004497/9007199254740992)), (51170719/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1776194591/4294967296), (334396157/4294967296)), (67/2147483648), by norm_num⟩
  | 2 => ⟨((601253015/1073741824), (-226390395/2147483648)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((-135685279/268435456), (51089713/536870912)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((367442547/1073741824), (-276707015/4294967296)), (59/2147483648), by norm_num⟩
  | 5 => ⟨((-1592084581/8589934592), (299734595/8589934592)), (65/4294967296), by norm_num⟩
  | 6 => ⟨((1437148323/17179869184), (-270565443/17179869184)), (119/17179869184), by norm_num⟩
  | 7 => ⟨((-1111962801/34359738368), (209344229/34359738368)), (47/17179869184), by norm_num⟩
  | 8 => ⟨((1505625543/137438953472), (-283457341/137438953472)), (65/68719476736), by norm_num⟩
  | 9 => ⟨((-453034395/137438953472), (170581491/274877906944)), (5/17179869184), by norm_num⟩
  | 10 => ⟨((981471907/1099511627776), (-11548581/68719476736)), (89/1099511627776), by norm_num⟩
  | 11 => ⟨((-966500071/4398046511104), (22744827/549755813888)), (89/4398046511104), by norm_num⟩
  | 12 => ⟨((1744887141/35184372088832), (-82125511/8796093022208)), (163/35184372088832), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581550584901671/10141204801825835211973625643008), (-242399545067/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444774299854707/158456325028528675187087900672), (-286968022813/633825300114114700748351602688)), (92229/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945055659137887/19807040628566084398385987584), (-161393165863/19807040628566084398385987584)), (103759/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944954735781893/1237940039285380274899124224), (-42861919003/309485009821345068724781056)), (55123/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885787853882229/77371252455336267181195264), (-171411055025/77371252455336267181195264)), (110249/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549914367812135/9671406556917033397649408), (-10041185333/302231454903657293676544)), (103361/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259104494061117/604462909807314587353088), (-281075416653/604462909807314587353088)), (22611/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888305210266327/75557863725914323419136), (-228300890541/37778931862957161709568)), (146975/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648962151756085/2361183241434822606848), (-21395239935/295147905179352825856)), (110235/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810988622222005/295147905179352825856), (-470488195053/590295810358705651712)), (37895/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824135970871245/73786976294838206464), (-73474973933/9223372036854775808)), (189485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455850204721133/2305843009213693952), (-660848174237/9223372036854775808)), (213185/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594649198779505/1152921504606846976), (-660315356209/1152921504606846976)), (106601/576460752303423488), by norm_num⟩
  | 5 => ⟨((1167149454227/140737488355328), (-72147136833/18014398509481984)), (46643/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492507533102811/36028797018963968), (-432284701049/18014398509481984)), (139949/18014398509481984), by norm_num⟩
  | 3 => ⟨((745172421677887/4503599627370496), (-269655394487/2251799813685248)), (349943/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115060447181227/2251799813685248), (-2150985591659/4503599627370496)), (350049/2251799813685248), by norm_num⟩
  | 1 => ⟨((2219359150989399/2251799813685248), (-1605439871331/1125899906842624)), (1050685/2251799813685248), by norm_num⟩
  | 0 => ⟨((136701779360443/140737488355328), (-3179817877157/1125899906842624)), (1051775/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((136701779360443/140737488355328), (-3179817877157/1125899906842624)), (4012203220847701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2124490776186483/2251799813685248), (-6177270419265/1125899906842624)), (2049171/1125899906842624), by norm_num⟩
  | 2 => ⟨((1002155785783579/1125899906842624), (-23312114954411/2251799813685248)), (1944561/562949953421312), by norm_num⟩
  | 3 => ⟨((1783782642134907/2251799813685248), (-20749953649015/1125899906842624)), (14007775/2251799813685248), by norm_num⟩
  | 4 => ⟨((1412273974244391/2251799813685248), (-8218627366267/281474976710656)), (11354539/1125899906842624), by norm_num⟩
  | 5 => ⟨((441912028045837/1125899906842624), (-164944730349129/4503599627370496)), (59622601/4503599627370496), by norm_num⟩
  | 6 => ⟨((1375509965677771/9007199254740992), (-258961067004497/9007199254740992)), (51170719/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-31235561/16777216), (-317804085/8388608)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨41,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile041Terms1
