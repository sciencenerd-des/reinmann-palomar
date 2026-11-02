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
namespace Reinmann.XiRectangle.Tile013Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3807/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3807/640))
  have he : value ((3/4), (3807/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-8931133415/17179869184), (-70835051901/17179869184)), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-93011086849791/281474976710656), (556565514014793/1125899906842624)), (230009/1125899906842624), by norm_num⟩
  | 1 => ⟨((15739837063/68719476736), (-23546253469/68719476736)), (21/137438953472), by norm_num⟩
  | 2 => ⟨((-43640094731/549755813888), (65284076819/549755813888)), (31/549755813888), by norm_num⟩
  | 3 => ⟨((5041501437/274877906944), (-60335298377/2199023255552)), (31/2199023255552), by norm_num⟩
  | 4 => ⟨((-27956020055/8796093022208), (20910620979/4398046511104)), (23/8796093022208), by norm_num⟩
  | 5 => ⟨((31004218369/70368744177664), (-46381241521/70368744177664)), (27/70368744177664), by norm_num⟩
  | 6 => ⟨((-1790873879/35184372088832), (42865369055/562949953421312)), (27/562949953421312), by norm_num⟩
  | 7 => ⟨((45397547153/9007199254740992), (-33956582519/4503599627370496)), (45/9007199254740992), by norm_num⟩
  | 8 => ⟨((-31467181813/72057594037927936), (47073818869/72057594037927936)), (33/72057594037927936), by norm_num⟩
  | 9 => ⟨((19387900759/576460752303423488), (-58007261915/1152921504606846976)), (21/576460752303423488), by norm_num⟩
  | 10 => ⟨((-21501869997/9223372036854775808), (64332112077/18446744073709551616)), (49/18446744073709551616), by norm_num⟩
  | 11 => ⟨((21678488095/147573952589676412928), (-16215135311/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-40070354405/4722366482869645213696), (29971934195/2361183241434822606848)), (25/2361183241434822606848), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455347/5070602400912917605986812821504), (2813696689515/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781162999789993/633825300114114700748351602688), (3338407925351/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892434738037157/39614081257132168796771975168), (938880003953/9903520314283042199192993792)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946188684082727/1237940039285380274899124224), (3990026712645/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774042775486061/154742504910672534362390528), (3989786642225/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388056590817643/2417851639229258349412352), (1870084903419/4835703278458516698824704)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261126609730471/604462909807314587353088), (3272393303439/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472897374482345/18889465931478580854784), (2658580122385/37778931862957161709568)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300386075616593/4722366482869645213696), (3987450941597/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625359835860445/590295810358705651712), (2741031674751/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914180346756511/36893488147419103232), (6851555897277/73786976294838206464)), (373/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828148798461513/9223372036854775808), (3853296074211/4611686018427387904)), (105/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1599391139567203/1152921504606846976), (7704830035495/1152921504606846976)), (105/288230376151711744), by norm_num⟩
  | 5 => ⟨((1199303449742469/144115188075855872), (6739741406527/144115188075855872)), (23/9007199254740992), by norm_num⟩
  | 4 => ⟨((374676894257787/9007199254740992), (5052818061707/18014398509481984)), (553/36028797018963968), by norm_num⟩
  | 3 => ⟨((187258896923297/1125899906842624), (12625073161777/9007199254740992)), (693/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122751240613091/2251799813685248), (3153646796119/562949953421312)), (87/281474976710656), by norm_num⟩
  | 1 => ⟨((1121127079196801/1125899906842624), (18895568072035/1125899906842624)), (131/140737488355328), by norm_num⟩
  | 0 => ⟨((139519432128899/140737488355328), (1177665635833/35184372088832)), (1059/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((139519432128899/140737488355328), (1177665635833/35184372088832)), (4039766551780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((69077123043731/70368744177664), (74718282462135/1125899906842624)), (2171/562949953421312), by norm_num⟩
  | 2 => ⟨((539994406449291/562949953421312), (73346825377785/562949953421312)), (4551/562949953421312), by norm_num⟩
  | 3 => ⟨((254209277808857/281474976710656), (140711888131821/562949953421312)), (9917/562949953421312), by norm_num⟩
  | 4 => ⟨((423997889659909/562949953421312), (508326074013765/1125899906842624)), (22871/562949953421312), by norm_num⟩
  | 5 => ⟨((204592540341321/562949953421312), (382856737674585/562949953421312)), (861/8796093022208), by norm_num⟩
  | 6 => ⟨((-93011086849791/281474976710656), (556565514014793/1125899906842624)), (230009/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/17179869184), (-70835051901/17179869184)), (1/8589934592), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-55294967/67108864), (-14033862625/2147483648)), (3/17179869184), by norm_num⟩
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
  | 0 => ⟨((956683748873873/2251799813685248), (-246158671857791/2251799813685248)), (220475/2251799813685248), by norm_num⟩
  | 1 => ⟨((-64149445977/137438953472), (8252958431/68719476736)), (17/137438953472), by norm_num⟩
  | 2 => ⟨((35237684831/137438953472), (-4533400775/68719476736)), (21/274877906944), by norm_num⟩
  | 3 => ⟨((-25808369053/274877906944), (13281199469/549755813888)), (33/1099511627776), by norm_num⟩
  | 4 => ⟨((886043481/34359738368), (-14590888945/2199023255552)), (5/549755813888), by norm_num⟩
  | 5 => ⟨((-24919507367/4398046511104), (6411891959/4398046511104)), (19/8796093022208), by norm_num⟩
  | 6 => ⟨((73005005389/70368744177664), (-18784488799/70368744177664)), (15/35184372088832), by norm_num⟩
  | 7 => ⟨((-22915484587/140737488355328), (11792497275/281474976710656)), (5/70368744177664), by norm_num⟩
  | 8 => ⟨((3146904121/140737488355328), (-25910764841/4503599627370496)), (47/4503599627370496), by norm_num⟩
  | 9 => ⟨((-98338916653/36028797018963968), (25303008589/36028797018963968)), (49/36028797018963968), by norm_num⟩
  | 10 => ⟨((86429073831/288230376151711744), (-22238556941/288230376151711744)), (23/144115188075855872), by norm_num⟩
  | 11 => ⟨((-17264007747/576460752303423488), (17768401409/2305843009213693952)), (39/2305843009213693952), by norm_num⟩
  | 12 => ⟨((101154405667/36893488147419103232), (-26027445517/36893488147419103232)), (15/9223372036854775808), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (-82012829643/2535301200456458802993406410752)), (57/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((890349489263219/316912650057057350374175801344), (-389033009345/633825300114114700748351602688)), (271/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891913103151671/39614081257132168796771975168), (-13675929911/1237940039285380274899124224)), (305/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891823603013339/2475880078570760549798248448), (-464942511111/2475880078570760549798248448)), (81/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773489541179769/154742504910672534362390528), (-464898522419/154742504910672534362390528)), (81/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387927067511195/2417851639229258349412352), (-27237227031/604462909807314587353088)), (19/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1260673841996041/604462909807314587353088), (-95318613147/151115727451828646838272)), (133/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29544606364823/1180591620717411303424), (-619483388147/75557863725914323419136)), (27/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1299835982336499/4722366482869645213696), (-116133976779/1180591620717411303424)), (81/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1624604959773695/590295810358705651712), (-638612367635/590295810358705651712)), (445/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913709675489443/36893488147419103232), (-798078747343/73786976294838206464)), (139/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1827092884285377/9223372036854775808), (-897581934221/9223372036854775808)), (313/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799169546968133/576460752303423488), (-897261222617/1152921504606846976)), (313/576460752303423488), by norm_num⟩
  | 5 => ⟨((599193629813263/72057594037927936), (-392371459577/72057594037927936)), (137/36028797018963968), by norm_num⟩
  | 4 => ⟨((748670992859737/18014398509481984), (-294098363023/9007199254740992)), (821/36028797018963968), by norm_num⟩
  | 3 => ⟨((11690463965105/70368744177664), (-1469231035967/9007199254740992)), (513/4503599627370496), by norm_num⟩
  | 2 => ⟨((2242164457430159/4503599627370496), (-2934683102121/4503599627370496)), (2053/4503599627370496), by norm_num⟩
  | 1 => ⟨((2237360820374689/2251799813685248), (-137268406413/70368744177664)), (3081/2251799813685248), by norm_num⟩
  | 0 => ⟨((2222977933942419/2251799813685248), (-1093438249617/281474976710656)), (3085/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2222977933942419/2251799813685248), (-1093438249617/281474976710656)), (11768345359420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1097245489119767/1125899906842624), (-17271084836261/2251799813685248)), (12231/2251799813685248), by norm_num⟩
  | 2 => ⟨((1069254099306979/1125899906842624), (-33663063321385/2251799813685248)), (6007/562949953421312), by norm_num⟩
  | 3 => ⟨((2030413221424137/2251799813685248), (-31969421289465/1125899906842624)), (46357/2251799813685248), by norm_num⟩
  | 4 => ⟨((1828976825166077/2251799813685248), (-57652669898019/1125899906842624)), (10779/281474976710656), by norm_num⟩
  | 5 => ⟨((1479643476902261/2251799813685248), (-187308652414989/2251799813685248)), (148913/2251799813685248), by norm_num⟩
  | 6 => ⟨((956683748873873/2251799813685248), (-246158671857791/2251799813685248)), (220475/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-14033862625/2147483648)), (3/17179869184), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-8931133415/8589934592), (-70835051901/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-608751005013863/4503599627370496), (-1471299906416707/4503599627370496)), (67301/281474976710656), by norm_num⟩
  | 1 => ⟨((6438507733/34359738368), (31122661801/68719476736)), (3/8589934592), by norm_num⟩
  | 2 => ⟨((-35702667857/274877906944), (-86290341115/274877906944)), (69/274877906944), by norm_num⟩
  | 3 => ⟨((16498135709/274877906944), (79749208871/549755813888)), (33/274877906944), by norm_num⟩
  | 4 => ⟨((-11435636251/549755813888), (-55277939281/1099511627776)), (3/68719476736), by norm_num⟩
  | 5 => ⟨((25365052881/4398046511104), (478946847/34359738368)), (55/4398046511104), by norm_num⟩
  | 6 => ⟨((-23442286519/17592186044416), (-28329016033/8796093022208)), (53/17592186044416), by norm_num⟩
  | 7 => ⟨((37140468129/140737488355328), (44882691637/70368744177664)), (43/70368744177664), by norm_num⟩
  | 8 => ⟨((-1608988173/35184372088832), (-7777577791/70368744177664)), (61/562949953421312), by norm_num⟩
  | 9 => ⟨((15861555423/2251799813685248), (76672087003/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 10 => ⟨((-17591027873/18014398509481984), (-42516032747/18014398509481984)), (11/4503599627370496), by norm_num⟩
  | 11 => ⟨((35471043995/288230376151711744), (10716315719/36028797018963968)), (91/288230376151711744), by norm_num⟩
  | 12 => ⟨((-32782205515/2305843009213693952), (-79231829617/2305843009213693952)), (43/1152921504606846976), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414716005/10141204801825835211973625643008), (-2557157004855/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((445090229344035/158456325028528675187087900672), (-3031431112695/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891532529012799/39614081257132168796771975168), (-1705016980275/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945709462421921/1237940039285380274899124224), (-3622775518989/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443271126303755/38685626227668133590597632), (-1811170860975/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96958010550023/604462909807314587353088), (-3395484441841/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260340873525909/604462909807314587353088), (-2970587949341/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890313021617933/75557863725914323419136), (-4826341128983/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299429020378083/4722366482869645213696), (-1809499781459/2361183241434822606848)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624044375840003/590295810358705651712), (-4974895379513/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228339638152395/9223372036854775808), (-3108387796793/36893488147419103232)), (373/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826300775177117/9223372036854775808), (-6991337386247/9223372036854775808)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597544384024211/1152921504606846976), (-436760512237/72057594037927936)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((1197688965960837/144115188075855872), (-6111081497893/144115188075855872)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((374072177190427/9007199254740992), (-4579745035909/18014398509481984)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((1495052596707859/9007199254740992), (-5718439719995/4503599627370496)), (1383/9007199254740992), by norm_num⟩
  | 2 => ⟨((559870092138323/1125899906842624), (-5709075538995/1125899906842624)), (1387/2251799813685248), by norm_num⟩
  | 1 => ⟨((1116629343557443/1125899906842624), (-8540196602275/562949953421312)), (2091/1125899906842624), by norm_num⟩
  | 0 => ⟨((1107235637426509/1125899906842624), (-33973379497539/1125899906842624)), (33/8796093022208), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1107235637426509/1125899906842624), (-33973379497539/1125899906842624)), (125885043320057/33554432000000000000000000), by norm_num⟩
  | 1 => ⟨((1087855642254713/1125899906842624), (-16705097973131/281474976710656)), (2141/281474976710656), by norm_num⟩
  | 2 => ⟨((523565605809015/562949953421312), (-129125049031759/1125899906842624)), (17567/1125899906842624), by norm_num⟩
  | 3 => ⟨((959064379963683/1125899906842624), (-120091375992771/562949953421312)), (18353/562949953421312), by norm_num⟩
  | 4 => ⟨((765713475349173/1125899906842624), (-409185080682635/1125899906842624)), (19549/281474976710656), by norm_num⟩
  | 5 => ⟨((744088694798347/2251799813685248), (-1113131028029571/2251799813685248)), (163199/1125899906842624), by norm_num⟩
  | 6 => ⟨((-608751005013863/4503599627370496), (-1471299906416707/4503599627370496)), (67301/281474976710656), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/8589934592), (-70835051901/8589934592)), (1/4294967296), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-5184362399/4294967296), (-82236948557/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-2601551428709/8796093022208), (199762273262821/4503599627370496)), (109305/562949953421312), by norm_num⟩
  | 1 => ⟨((127778183/268435456), (-9811553225/137438953472)), (45/137438953472), by norm_num⟩
  | 2 => ⟨((-105293338677/274877906944), (3947771435/68719476736)), (75/274877906944), by norm_num⟩
  | 3 => ⟨((112975394129/549755813888), (-16943181379/549755813888)), (83/549755813888), by norm_num⟩
  | 4 => ⟨((-45456720621/549755813888), (6817249617/549755813888)), (69/1099511627776), by norm_num⟩
  | 5 => ⟨((29263907817/1099511627776), (-17555103987/4398046511104)), (91/4398046511104), by norm_num⟩
  | 6 => ⟨((-62797923609/8796093022208), (9417949971/8796093022208)), (25/4398046511104), by norm_num⟩
  | 7 => ⟨((115507838947/70368744177664), (-17322977989/70368744177664)), (47/35184372088832), by norm_num⟩
  | 8 => ⟨((-92951347593/281474976710656), (6970064383/140737488355328)), (77/281474976710656), by norm_num⟩
  | 9 => ⟨((4155539523/70368744177664), (-9971454107/1125899906842624)), (57/1125899906842624), by norm_num⟩
  | 10 => ⟨((-1337616571/140737488355328), (6419374513/4503599627370496)), (19/2251799813685248), by norm_num⟩
  | 11 => ⟨((100203558245/72057594037927936), (-7513879793/36028797018963968)), (91/72057594037927936), by norm_num⟩
  | 12 => ⟨((-107514270401/576460752303423488), (16124164011/576460752303423488)), (25/144115188075855872), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791201706336853/5070602400912917605986812821504), (3898364681111/10141204801825835211973625643008)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890048013632581/316912650057057350374175801344), (2310058685723/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236404272051837/4951760157141521099596496896), (2598520288881/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945550741020665/1237940039285380274899124224), (5521171493113/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772766564026399/154742504910672534362390528), (2760200800345/77371252455336267181195264)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551029569629389/9671406556917033397649408), (2587279167495/4835703278458516698824704)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157509883775189/75557863725914323419136), (4526920203191/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944943299896651/37778931862957161709568), (7354710572959/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649554168530431/2361183241434822606848), (344668102987/295147905179352825856)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623602028510845/590295810358705651712), (7580514741135/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826162061197519/73786976294838206464), (4736183465845/36893488147419103232)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912836726253545/4611686018427387904), (10651905659211/9223372036854775808)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798456721520491/576460752303423488), (332695900145/36028797018963968)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197132828006647/144115188075855872), (4654569862143/72057594037927936)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495446387667625/36028797018963968), (13951008615701/36028797018963968)), (555/18014398509481984), by norm_num⟩
  | 3 => ⟨((373496382342883/2251799813685248), (17416511641277/9007199254740992)), (87/562949953421312), by norm_num⟩
  | 2 => ⟨((559325967822211/1125899906842624), (17383093328401/2251799813685248)), (699/1125899906842624), by norm_num⟩
  | 1 => ⟨((278736063569825/281474976710656), (25990939112903/1125899906842624)), (2113/1125899906842624), by norm_num⟩
  | 0 => ⟨((34489250495899/35184372088832), (25823076351529/562949953421312)), (2145/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((34489250495899/35184372088832), (25823076351529/562949953421312)), (8182527782249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((539741263360891/562949953421312), (101251606436405/1125899906842624)), (8805/1125899906842624), by norm_num⟩
  | 2 => ⟨((1025873286490233/1125899906842624), (194154630063199/1125899906842624)), (4617/281474976710656), by norm_num⟩
  | 3 => ⟨((901252387883117/1125899906842624), (44226411073429/140737488355328)), (40025/1125899906842624), by norm_num⟩
  | 4 => ⟨((305121900515957/562949953421312), (566432711756139/1125899906842624)), (89235/1125899906842624), by norm_num⟩
  | 5 => ⟨((45786911817971/1125899906842624), (1228038297010701/2251799813685248)), (186519/1125899906842624), by norm_num⟩
  | 6 => ⟨((-2601551428709/8796093022208), (199762273262821/4503599627370496)), (109305/562949953421312), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/4294967296), (-82236948557/8589934592)), (1/4294967296), by norm_num⟩, -2, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-2885830621/2147483648), (-91552976451/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-388889548539557/4503599627370496), (554258083736739/2251799813685248)), (790765/4503599627370496), by norm_num⟩
  | 1 => ⟨((10632271287/68719476736), (-30306920469/68719476736)), (45/137438953472), by norm_num⟩
  | 2 => ⟨((-9525236379/68719476736), (54302711733/137438953472)), (21/68719476736), by norm_num⟩
  | 3 => ⟨((5688977493/68719476736), (-506757281/2147483648)), (13/68719476736), by norm_num⟩
  | 4 => ⟨((-20386558587/549755813888), (58111178037/549755813888)), (3/34359738368), by norm_num⟩
  | 5 => ⟨((29222247515/2199023255552), (-83297002813/2199023255552)), (71/2199023255552), by norm_num⟩
  | 6 => ⟨((-34906159131/8796093022208), (99498795699/8796093022208)), (87/8796093022208), by norm_num⟩
  | 7 => ⟨((2233694327/2199023255552), (-25468272767/8796093022208)), (23/8796093022208), by norm_num⟩
  | 8 => ⟨((-16008971847/70368744177664), (45633018895/70368744177664)), (21/35184372088832), by norm_num⟩
  | 9 => ⟨((25497090577/562949953421312), (-72678572191/562949953421312)), (69/562949953421312), by norm_num⟩
  | 10 => ⟨((-1142116337/140737488355328), (52089007973/2251799813685248)), (51/2251799813685248), by norm_num⟩
  | 11 => ⟨((23812628501/18014398509481984), (-67877071475/18014398509481984)), (17/4503599627370496), by norm_num⟩
  | 12 => ⟨((-28444335069/144115188075855872), (20269897593/36028797018963968)), (83/144115188075855872), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (2485645370867/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779891714093095/633825300114114700748351602688), (2945179934599/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945502375764559/19807040628566084398385987584), (414115486341/4951760157141521099596496896)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945429124979761/1237940039285380274899124224), (3519497984165/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772523930138375/154742504910672534362390528), (3518953889619/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550802735726871/9671406556917033397649408), (412305151341/1208925819614629174706176)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314970306416143/151115727451828646838272), (1442779021589/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236195786596971/9444732965739290427392), (1171987033645/18889465931478580854784)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298869147848647/4722366482869645213696), (878753242737/1180591620717411303424)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405818708523975/147573952589676412928), (4831602301947/590295810358705651712)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456438900658309/18446744073709551616), (6037192389861/73786976294838206464)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825219668776863/9223372036854775808), (6788665026025/9223372036854775808)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596464007921993/1152921504606846976), (6784695273307/1152921504606846976)), (105/144115188075855872), by norm_num⟩
  | 5 => ⟨((598372229424843/72057594037927936), (5932143443439/144115188075855872)), (735/144115188075855872), by norm_num⟩
  | 4 => ⟨((747436796514803/18014398509481984), (4444643978735/18014398509481984)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((1493286582866683/9007199254740992), (11095993275619/9007199254740992)), (1383/9007199254740992), by norm_num⟩
  | 2 => ⟨((558989248008781/1125899906842624), (5536290097045/1125899906842624)), (1387/2251799813685248), by norm_num⟩
  | 1 => ⟨((1113997640198315/1125899906842624), (517199359659/35184372088832)), (1045/562949953421312), by norm_num⟩
  | 0 => ⟨((1102015636175555/1125899906842624), (32867048881787/1125899906842624)), (1055/281474976710656), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1102015636175555/1125899906842624), (32867048881787/1125899906842624)), (4024506688976199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((538839292950939/562949953421312), (64339647889745/1125899906842624)), (2127/281474976710656), by norm_num⟩
  | 2 => ⟨((256961461935411/281474976710656), (61584036319613/562949953421312)), (4315/281474976710656), by norm_num⟩
  | 3 => ⟨((115607158579731/140737488355328), (224882853737131/1125899906842624)), (35291/1125899906842624), by norm_num⟩
  | 4 => ⟨((1429591857244547/2251799813685248), (369454763441737/1125899906842624)), (72077/1125899906842624), by norm_num⟩
  | 5 => ⟨((665132655344515/2251799813685248), (938217541766515/2251799813685248)), (69411/562949953421312), by norm_num⟩
  | 6 => ⟨((-388889548539557/4503599627370496), (554258083736739/2251799813685248)), (790765/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-91552976451/8589934592)), (1/4294967296), by norm_num⟩, -2, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-12536430677/8589934592), (-24857391451/2147483648)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((286554837744883/2251799813685248), (875609775750011/4503599627370496)), (515965/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4254226433/17179869184), (-1624925565/4294967296)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((33113369569/137438953472), (25295673187/68719476736)), (33/137438953472), by norm_num⟩
  | 3 => ⟨((-42957094609/274877906944), (-8203851197/34359738368)), (45/274877906944), by norm_num⟩
  | 4 => ⟨((41795323187/549755813888), (31927914611/274877906944)), (23/274877906944), by norm_num⟩
  | 5 => ⟨((-32531977429/1099511627776), (-1553221327/34359738368)), (37/1099511627776), by norm_num⟩
  | 6 => ⟨((2637679377/274877906944), (16119622101/1099511627776)), (25/2199023255552), by norm_num⟩
  | 7 => ⟨((-46927424637/17592186044416), (-4481048035/1099511627776)), (29/8796093022208), by norm_num⟩
  | 8 => ⟨((45658275935/70368744177664), (34878867399/35184372088832)), (29/35184372088832), by norm_num⟩
  | 9 => ⟨((-9871878059/70368744177664), (-60329904053/281474976710656)), (13/70368744177664), by norm_num⟩
  | 10 => ⟨((3841957541/140737488355328), (46958629035/1125899906842624)), (21/562949953421312), by norm_num⟩
  | 11 => ⟨((-2718583335/562949953421312), (-33228099209/4503599627370496)), (61/9007199254740992), by norm_num⟩
  | 12 => ⟨((28213967481/36028797018963968), (43105930323/36028797018963968)), (41/36028797018963968), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693181983/10141204801825835211973625643008), (645604106633/5070602400912917605986812821504)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779716672264867/633825300114114700748351602688), (1529629223223/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118175503304887/2475880078570760549798248448), (430152375365/9903520314283042199192993792)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890649537553835/2475880078570760549798248448), (114242203451/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((886157766253555/77371252455336267181195264), (913784466097/77371252455336267181195264)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387651924317089/2417851639229258349412352), (856510233651/4835703278458516698824704)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259710901191315/604462909807314587353088), (749283785765/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472322535446719/18889465931478580854784), (2434562443359/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((324665645574673/1180591620717411303424), (912694175915/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((811495847947499/295147905179352825856), (1254521176733/295147905179352825856)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825403013032553/73786976294838206464), (391875434867/9223372036854775808)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228103104617713/1152921504606846976), (3525092936217/9223372036854775808)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596071462995531/1152921504606846976), (1761430819821/576460752303423488)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74775221967561/9007199254740992), (384999417689/18014398509481984)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494367362539739/36028797018963968), (1153744965615/9007199254740992)), (1099/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492662754532601/9007199254740992), (5759960892251/9007199254740992)), (1375/9007199254740992), by norm_num⟩
  | 2 => ⟨((2234736139943399/4503599627370496), (2873416563249/1125899906842624)), (2753/4503599627370496), by norm_num⟩
  | 1 => ⟨((1113115376183071/1125899906842624), (8587493692189/1125899906842624)), (4139/2251799813685248), by norm_num⟩
  | 0 => ⟨((275095956409777/281474976710656), (34088686732761/2251799813685248)), (8321/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((275095956409777/281474976710656), (34088686732761/2251799813685248)), (31742104537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((537593993360449/562949953421312), (16658070264523/562949953421312)), (8259/1125899906842624), by norm_num⟩
  | 2 => ⟨((2051548693716375/2251799813685248), (15907770239181/281474976710656)), (16263/1125899906842624), by norm_num⟩
  | 3 => ⟨((465478365278491/562949953421312), (115944819093741/1125899906842624)), (1967/70368744177664), by norm_num⟩
  | 4 => ⟨((757826897319327/1125899906842624), (383478527895881/2251799813685248)), (1829/35184372088832), by norm_num⟩
  | 5 => ⟨((954858700483889/2251799813685248), (4033028674687/17592186044416)), (197447/2251799813685248), by norm_num⟩
  | 6 => ⟨((286554837744883/2251799813685248), (875609775750011/4503599627370496)), (515965/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12536430677/8589934592), (-24857391451/2147483648)), (1/4294967296), by norm_num⟩, -2, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-13396700123/8589934592), (-106252577853/8589934592)), (3/8589934592), by norm_num⟩
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
  | 0 => ⟨((1856927339093215/9007199254740992), (185255364208103/4503599627370496)), (101909/1125899906842624), by norm_num⟩
  | 1 => ⟨((-58919858533/137438953472), (-11756216435/137438953472)), (7/34359738368), by norm_num⟩
  | 2 => ⟨((15315050183/34359738368), (6111591207/68719476736)), (31/137438953472), by norm_num⟩
  | 3 => ⟨((-21231167709/68719476736), (-2118116107/34359738368)), (23/137438953472), by norm_num⟩
  | 4 => ⟨((88297944225/549755813888), (4404498623/137438953472)), (25/274877906944), by norm_num⟩
  | 5 => ⟨((-73444165307/1099511627776), (-14654235851/1099511627776)), (11/274877906944), by norm_num⟩
  | 6 => ⟨((101815232223/4398046511104), (20315084527/4398046511104)), (1/68719476736), by norm_num⟩
  | 7 => ⟨((-30245546209/4398046511104), (-6034861527/4398046511104)), (5/1099511627776), by norm_num⟩
  | 8 => ⟨((31446922619/17592186044416), (6274570879/17592186044416)), (11/8796093022208), by norm_num⟩
  | 9 => ⟨((-58126255335/140737488355328), (-11597869637/140737488355328)), (43/140737488355328), by norm_num⟩
  | 10 => ⟨((96696120005/1125899906842624), (19293673535/1125899906842624)), (37/562949953421312), by norm_num⟩
  | 11 => ⟨((-9139724039/562949953421312), (-14589114997/4503599627370496)), (29/2251799813685248), by norm_num⟩
  | 12 => ⟨((25340695795/9007199254740992), (10112403927/18014398509481984)), (83/36028797018963968), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521241/10141204801825835211973625643008), (256539684433/10141204801825835211973625643008)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779563342536327/633825300114114700748351602688), (37982430097/79228162514264337593543950336)), (541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472658912509467/9903520314283042199192993792), (341794806949/39614081257132168796771975168)), (609/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890466476455009/2475880078570760549798248448), (363099203691/2475880078570760549798248448)), (647/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772132602881403/154742504910672534362390528), (363034219887/154742504910672534362390528)), (647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96902271273715/604462909807314587353088), (340275552237/9671406556917033397649408)), (607/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259561103486811/604462909807314587353088), (148836048867/302231454903657293676544)), (531/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889046982085533/75557863725914323419136), (483587803343/75557863725914323419136)), (431/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298480441263703/4722366482869645213696), (362577705613/4722366482869645213696)), (647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622741623429795/590295810358705651712), (124590138721/147573952589676412928)), (445/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825090979207223/73786976294838206464), (311337568223/36893488147419103232)), (1111/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824474563728551/9223372036854775808), (350065422925/4611686018427387904)), (625/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797861072392261/576460752303423488), (699657805005/1152921504606846976)), (625/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196098970983689/144115188075855872), (305834418881/72057594037927936)), (547/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493912634072299/36028797018963968), (114555105725/4503599627370496)), (1641/36028797018963968), by norm_num⟩
  | 3 => ⟨((746049042427545/4503599627370496), (571847124287/4503599627370496)), (513/2251799813685248), by norm_num⟩
  | 2 => ⟨((1116808995520429/2251799813685248), (1140913849713/2251799813685248)), (513/562949953421312), by norm_num⟩
  | 1 => ⟨((2224581392450327/2251799813685248), (1704436597971/1125899906842624)), (3079/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098789855495541/1125899906842624), (6762474362869/2251799813685248)), (1541/281474976710656), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1098789855495541/1125899906842624), (6762474362869/2251799813685248)), (5878449560069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2144644841761751/2251799813685248), (6599643700839/1125899906842624)), (24137/2251799813685248), by norm_num⟩
  | 2 => ⟨((510627903972091/562949953421312), (25142362539423/2251799813685248)), (46261/2251799813685248), by norm_num⟩
  | 3 => ⟨((1852394487864487/2251799813685248), (2850695653847/140737488355328)), (84957/2251799813685248), by norm_num⟩
  | 4 => ⟨((761454224884329/1125899906842624), (37521011476581/1125899906842624)), (143219/2251799813685248), by norm_num⟩
  | 5 => ⟨((1027453163068459/2251799813685248), (101502922372191/2251799813685248)), (101633/1125899906842624), by norm_num⟩
  | 6 => ⟨((1856927339093215/9007199254740992), (185255364208103/4503599627370496)), (101909/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13396700123/8589934592), (-106252577853/8589934592)), (3/8589934592), by norm_num⟩, -2, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile013Terms0
