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
namespace Reinmann.XiRectangle.Tile032Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8037/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8037/640))
  have he : value ((7/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-64510795/33554432), (-57865319/2097152)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-511251853993375/4503599627370496), (-830246385370197/9007199254740992)), (89569047/4503599627370496), by norm_num⟩
  | 1 => ⟨((1071295871/4294967296), (869864351/4294967296)), (95/2147483648), by norm_num⟩
  | 2 => ⟨((-1176938809/4294967296), (-477821833/2147483648)), (211/4294967296), by norm_num⟩
  | 3 => ⟨((430999813/2147483648), (349960625/2147483648)), (157/4294967296), by norm_num⟩
  | 4 => ⟨((-473501691/4294967296), (-768942087/8589934592)), (175/8589934592), by norm_num⟩
  | 5 => ⟨((832311643/17179869184), (675815381/17179869184)), (39/4294967296), by norm_num⟩
  | 6 => ⟨((-304795933/17179869184), (-247486361/17179869184)), (29/8589934592), by norm_num⟩
  | 7 => ⟨((765377275/137438953472), (621466417/137438953472)), (37/34359738368), by norm_num⟩
  | 8 => ⟨((-52553305/34359738368), (-682750643/549755813888)), (165/549755813888), by norm_num⟩
  | 9 => ⟨((821130051/2199023255552), (666736219/2199023255552)), (163/2199023255552), by norm_num⟩
  | 10 => ⟨((-180420713/2199023255552), (-585987683/8796093022208)), (145/8796093022208), by norm_num⟩
  | 11 => ⟨((576617927/35184372088832), (936397483/70368744177664)), (235/70368744177664), by norm_num⟩
  | 12 => ⟨((-211159847/70368744177664), (-171456297/70368744177664)), (175/281474976710656), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403057283/10141204801825835211973625643008), (-3203894551881/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1778995812075327/633825300114114700748351602688), (-3792594084291/633825300114114700748351602688)), (34715/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472499209969269/9903520314283042199192993792), (-4265931823597/39614081257132168796771975168)), (78127/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889787297267847/2475880078570760549798248448), (-566457704751/309485009821345068724781056)), (83031/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885726462642657/77371252455336267181195264), (-4530659417193/154742504910672534362390528)), (41527/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774899306716443/4835703278458516698824704), (-1061607122099/2417851639229258349412352)), (1217/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((314750640903109/151115727451828646838272), (-464320046789/75557863725914323419136)), (34089/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472034591038801/18889465931478580854784), (-754270614519/9444732965739290427392)), (55417/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297798111868669/4722366482869645213696), (-2261938900781/2361183241434822606848)), (83167/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810901007477447/295147905179352825856), (-6217495560515/590295810358705651712)), (28605/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911957181545015/36893488147419103232), (-3883807979751/36893488147419103232)), (143125/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911573990033583/4611686018427387904), (-4366360624097/4611686018427387904)), (161153/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594391954803361/1152921504606846976), (-8725415634361/1152921504606846976)), (161325/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597465503519405/72057594037927936), (-3813261838241/72057594037927936)), (17669/18014398509481984), by norm_num⟩
  | 4 => ⟨((186519077024939/4503599627370496), (-2855841262845/9007199254740992)), (212415/36028797018963968), by norm_num⟩
  | 3 => ⟨((744941994657221/4503599627370496), (-7125246007519/4503599627370496)), (66549/2251799813685248), by norm_num⟩
  | 2 => ⟨((557286947713935/1125899906842624), (-3551865921087/562949953421312)), (133607/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108885902186033/1125899906842624), (-21203776037583/1125899906842624)), (100843/281474976710656), by norm_num⟩
  | 0 => ⟨((545886944800457/562949953421312), (-5247348190245/140737488355328)), (816979/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((545886944800457/562949953421312), (-5247348190245/140737488355328)), (3116527561668014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1057117067287203/1125899906842624), (-10176602216479/140737488355328)), (1645355/1125899906842624), by norm_num⟩
  | 2 => ⟨((986649381803471/1125899906842624), (-76439191971877/562949953421312)), (3327625/1125899906842624), by norm_num⟩
  | 3 => ⟨((843862937159583/1125899906842624), (-66985245354631/281474976710656)), (13471611/2251799813685248), by norm_num⟩
  | 4 => ⟨((1137423110698557/2251799813685248), (-803287973259817/2251799813685248)), (26605901/2251799813685248), by norm_num⟩
  | 5 => ⟨((575947969110151/4503599627370496), (-1623018706687987/4503599627370496)), (45860531/2251799813685248), by norm_num⟩
  | 6 => ⟨((-511251853993375/4503599627370496), (-830246385370197/9007199254740992)), (89569047/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/33554432), (-57865319/2097152)), (3/67108864), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-67604193/33554432), (-1940481785/67108864)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-60164534973401/562949953421312), (359183176066063/4503599627370496)), (163356995/9007199254740992), by norm_num⟩
  | 1 => ⟨((1056930247/4294967296), (-394368089/2147483648)), (91/2147483648), by norm_num⟩
  | 2 => ⟨((-304208979/1073741824), (908066083/4294967296)), (53/1073741824), by norm_num⟩
  | 3 => ⟨((58372255/268435456), (-696966475/4294967296)), (165/4294967296), by norm_num⟩
  | 4 => ⟨((-537628337/4294967296), (200603077/2147483648)), (3/134217728), by norm_num⟩
  | 5 => ⟨((247586999/4294967296), (-92381131/2147483648)), (179/17179869184), by norm_num⟩
  | 6 => ⟨((-380060089/17179869184), (567241107/34359738368)), (139/34359738368), by norm_num⟩
  | 7 => ⟨((500068969/68719476736), (-373177405/68719476736)), (185/137438953472), by norm_num⟩
  | 8 => ⟨((-575725677/274877906944), (429636365/274877906944)), (27/68719476736), by norm_num⟩
  | 9 => ⟨((1178362099/2199023255552), (-219838731/549755813888)), (7/68719476736), by norm_num⟩
  | 10 => ⟨((-1085311601/8796093022208), (101239477/1099511627776)), (209/8796093022208), by norm_num⟩
  | 11 => ⟨((908735387/35184372088832), (-678145485/35184372088832)), (177/35184372088832), by norm_num⟩
  | 12 => ⟨((-697480185/140737488355328), (520495895/140737488355328)), (69/70368744177664), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314710245/10141204801825835211973625643008), (3257173481393/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((889426705417403/316912650057057350374175801344), (3855076264605/633825300114114700748351602688)), (69435/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236229581685119/4951760157141521099596496896), (2168089062813/19807040628566084398385987584)), (19533/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472404278651607/618970019642690137449562112), (2303120166471/1237940039285380274899124224)), (83037/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771282759963755/154742504910672534362390528), (1151293221213/38685626227668133590597632)), (83061/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387409775472047/2417851639229258349412352), (1079053897071/2417851639229258349412352)), (77895/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629431504739175/302231454903657293676544), (3775554842059/604462909807314587353088)), (8523/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887911623363303/75557863725914323419136), (6133151159205/75557863725914323419136)), (110845/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324407021666387/1180591620717411303424), (4598004004389/4722366482869645213696)), (10397/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621568279778001/590295810358705651712), (6319234810319/590295810358705651712)), (57217/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823622268496351/73786976294838206464), (7894513821947/73786976294838206464)), (17893/9223372036854775808), by norm_num⟩
  | 7 => ⟨((113926217261247/576460752303423488), (8875101924265/9223372036854775808)), (20147/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594063579471197/1152921504606846976), (8867322569763/1152921504606846976)), (161351/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597321911892419/72057594037927936), (1937540004987/36028797018963968)), (70689/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491722132980911/36028797018963968), (5803878474747/18014398509481984)), (53115/9007199254740992), by norm_num⟩
  | 3 => ⟨((372336599675475/2251799813685248), (1809890803927/1125899906842624)), (33283/1125899906842624), by norm_num⟩
  | 2 => ⟨((34813658778331/70368744177664), (14433323162365/2251799813685248)), (66825/562949953421312), by norm_num⟩
  | 1 => ⟨((1108082641419861/1125899906842624), (10767828382011/562949953421312)), (50443/140737488355328), by norm_num⟩
  | 0 => ⟨((1090175335854385/1125899906842624), (21307543047677/562949953421312)), (204375/281474976710656), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1090175335854385/1125899906842624), (21307543047677/562949953421312)), (779628754735851199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1053971325630615/1125899906842624), (82525836469333/1125899906842624)), (1645007/1125899906842624), by norm_num⟩
  | 2 => ⟨((980588980296375/1125899906842624), (77253639274451/562949953421312)), (1660491/562949953421312), by norm_num⟩
  | 3 => ⟨((1665658276469089/2251799813685248), (8410390979243/35184372088832)), (837027/140737488355328), by norm_num⟩
  | 4 => ⟨((137927905726663/281474976710656), (199077552209091/562949953421312)), (6553845/562949953421312), by norm_num⟩
  | 5 => ⟨((518192520630259/4503599627370496), (1560826481942873/4503599627370496)), (88466541/4503599627370496), by norm_num⟩
  | 6 => ⟨((-60164534973401/562949953421312), (359183176066063/4503599627370496)), (163356995/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67604193/33554432), (-1940481785/67108864)), (3/67108864), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-4400157/2097152), (-126300221/4194304)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((291749453645365/9007199254740992), (532906481280521/4503599627370496)), (40541343/4503599627370496), by norm_num⟩
  | 1 => ⟨((-166793975/2147483648), (-1218656475/4294967296)), (95/4294967296), by norm_num⟩
  | 2 => ⟨((99988621/1073741824), (365276325/1073741824)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((-319682989/4294967296), (-291964791/1073741824)), (95/4294967296), by norm_num⟩
  | 4 => ⟨((95820791/2147483648), (5469539/33554432)), (29/2147483648), by norm_num⟩
  | 5 => ⟨((-367629155/17179869184), (-1343015087/17179869184)), (57/8589934592), by norm_num⟩
  | 6 => ⟨((73461351/8589934592), (1073469843/34359738368)), (93/34359738368), by norm_num⟩
  | 7 => ⟨((-201317287/68719476736), (-735448075/68719476736)), (65/68719476736), by norm_num⟩
  | 8 => ⟨((241368885/274877906944), (881763731/274877906944)), (5/17179869184), by norm_num⟩
  | 9 => ⟨((-257234359/1099511627776), (-234930787/274877906944)), (87/1099511627776), by norm_num⟩
  | 10 => ⟨((246728421/4398046511104), (450671539/2199023255552)), (85/4398046511104), by norm_num⟩
  | 11 => ⟨((-215137787/17592186044416), (-1571873677/35184372088832)), (75/17592186044416), by norm_num⟩
  | 12 => ⟨((85979647/35184372088832), (1256396153/140737488355328)), (61/70368744177664), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581242681581499/10141204801825835211973625643008), (849047031549/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778730637213645/633825300114114700748351602688), (502381992241/158456325028528675187087900672)), (5775/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472424721861775/9903520314283042199192993792), (2260302679835/39614081257132168796771975168)), (51981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889471196164273/2475880078570760549798248448), (1200528711283/1237940039285380274899124224)), (55237/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771137356379015/154742504910672534362390528), (2400479155223/154742504910672534362390528)), (55245/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387375833185285/2417851639229258349412352), (281229371373/1208925819614629174706176)), (51801/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629372378912905/302231454903657293676544), (491997889019/151115727451828646838272)), (45335/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471930122016561/18889465931478580854784), (799208839515/18889465931478580854784)), (36843/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648742815053297/2361183241434822606848), (599154968495/1180591620717411303424)), (55279/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202671731850251/73786976294838206464), (3293717299493/590295810358705651712)), (297/2305843009213693952), by norm_num⟩
  | 8 => ⟨((1823381413942473/73786976294838206464), (4114695430763/73786976294838206464)), (47537/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822551503626091/9223372036854775808), (578208019569/1152921504606846976)), (107007/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398449834200333/288230376151711744), (4621457183009/1152921504606846976)), (107067/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194416799133573/144115188075855872), (4039046697111/144115188075855872)), (93753/144115188075855872), by norm_num⟩
  | 4 => ⟨((745694975155549/18014398509481984), (3024562314085/18014398509481984)), (70383/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488945743076829/9007199254740992), (7544901610237/9007199254740992)), (176197/9007199254740992), by norm_num⟩
  | 2 => ⟨((556829094931911/1125899906842624), (15040391787787/4503599627370496)), (353113/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107568386350277/1125899906842624), (22437412336699/2251799813685248)), (531475/2251799813685248), by norm_num⟩
  | 0 => ⟨((2178722355688951/2251799813685248), (44384238029785/2251799813685248)), (1070201/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2178722355688951/2251799813685248), (44384238029785/2251799813685248)), (4082492836959075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((263392704457817/281474976710656), (85887680643737/2251799813685248)), (2113129/2251799813685248), by norm_num⟩
  | 2 => ⟨((984250276626903/1125899906842624), (160740316945601/2251799813685248)), (4115957/2251799813685248), by norm_num⟩
  | 3 => ⟨((427342270311467/562949953421312), (70258777204481/562949953421312)), (1945969/562949953421312), by norm_num⟩
  | 4 => ⟨((631264357127357/1125899906842624), (53334306499889/281474976710656)), (6880301/1125899906842624), by norm_num⟩
  | 5 => ⟨((1254043683410905/4503599627370496), (478451720276295/2251799813685248)), (41290443/4503599627370496), by norm_num⟩
  | 6 => ⟨((291749453645365/9007199254740992), (532906481280521/4503599627370496)), (40541343/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4400157/2097152), (-126300221/4194304)), (1/33554432), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-72957177/33554432), (-1047065775/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((500659021282773/4503599627370496), (53600518010013/2251799813685248)), (76903269/9007199254740992), by norm_num⟩
  | 1 => ⟨((-37076799/134217728), (-31755515/536870912)), (93/4294967296), by norm_num⟩
  | 2 => ⟨((737059075/2147483648), (315637961/4294967296)), (59/2147483648), by norm_num⟩
  | 3 => ⟨((-1221015331/4294967296), (-261443623/4294967296)), (25/1073741824), by norm_num⟩
  | 4 => ⟨((1517054557/8589934592), (324831499/8589934592)), (127/8589934592), by norm_num⟩
  | 5 => ⟨((-753947791/8589934592), (-322870381/17179869184)), (129/17179869184), by norm_num⟩
  | 6 => ⟨((1248993253/34359738368), (66858563/8589934592)), (109/34359738368), by norm_num⟩
  | 7 => ⟨((-886751897/68719476736), (-94935593/34359738368)), (79/68719476736), by norm_num⟩
  | 8 => ⟨((1101747843/274877906944), (117953043/137438953472)), (25/68719476736), by norm_num⟩
  | 9 => ⟨((-608386787/549755813888), (-260535379/1099511627776)), (113/1099511627776), by norm_num⟩
  | 10 => ⟨((604713749/2199023255552), (129481219/2199023255552)), (57/2199023255552), by norm_num⟩
  | 11 => ⟨((-1092841611/17592186044416), (-233999085/17592186044416)), (105/17592186044416), by norm_num⟩
  | 12 => ⟨((905203129/70368744177664), (193821961/70368744177664)), (89/70368744177664), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790571753654357/5070602400912917605986812821504), (274766060551/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889307693358627/316912650057057350374175801344), (325117857047/633825300114114700748351602688)), (11529/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944784686925249/19807040628566084398385987584), (365688366413/39614081257132168796771975168)), (25941/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889333773196581/2475880078570760549798248448), (194228870293/1237940039285380274899124224)), (110251/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771000141632627/154742504910672534362390528), (388360862009/154742504910672534362390528)), (55127/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549374915020957/9671406556917033397649408), (363985408749/9671406556917033397649408)), (51683/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258632613278231/604462909807314587353088), (318384371649/604462909807314587353088)), (90449/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471884666789939/18889465931478580854784), (258590910529/37778931862957161709568)), (146983/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297349626350209/4722366482869645213696), (387717762257/4722366482869645213696)), (110243/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202648429647275/73786976294838206464), (532838095037/590295810358705651712)), (151591/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56973414756333/2305843009213693952), (665637143717/73786976294838206464)), (47375/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822291552908531/9223372036854775808), (748277817035/9223372036854775808)), (53301/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796770447261445/576460752303423488), (186893376199/288230376151711744)), (26653/144115188075855872), by norm_num⟩
  | 5 => ⟨((597096177860475/72057594037927936), (10208364969/2251799813685248)), (93297/72057594037927936), by norm_num⟩
  | 4 => ⟨((372764165958899/9007199254740992), (978422348397/36028797018963968)), (2187/281474976710656), by norm_num⟩
  | 3 => ⟨((1488535028479773/9007199254740992), (610133368771/4503599627370496)), (350001/9007199254740992), by norm_num⟩
  | 2 => ⟨((556628138675291/1125899906842624), (1216134936151/2251799813685248)), (700245/4503599627370496), by norm_num⟩
  | 1 => ⟨((553493694824971/562949953421312), (56684618779/35184372088832)), (1050983/2251799813685248), by norm_num⟩
  | 0 => ⟨((2176571754586909/2251799813685248), (3586845917649/1125899906842624)), (2104473/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176571754586909/2251799813685248), (3586845917649/1125899906842624)), (8027927407271575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2103834058524873/2251799813685248), (108344271227/17592186044416)), (4081743/2251799813685248), by norm_num⟩
  | 2 => ⟨((1965505723748771/2251799813685248), (12956796118341/1125899906842624)), (7677341/2251799813685248), by norm_num⟩
  | 3 => ⟨((857656442715753/1125899906842624), (22618935108949/1125899906842624)), (3394797/562949953421312), by norm_num⟩
  | 4 => ⟨((326433527989057/562949953421312), (68920071156099/2251799813685248)), (21233549/2251799813685248), by norm_num⟩
  | 5 => ⟨((1510073483961667/4503599627370496), (159856639759981/4503599627370496)), (51849703/4503599627370496), by norm_num⟩
  | 6 => ⟨((500659021282773/4503599627370496), (53600518010013/2251799813685248)), (76903269/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72957177/33554432), (-1047065775/33554432)), (1/16777216), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-75307241/33554432), (-67549587/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((83640415333461/1125899906842624), (-21282607797543/281474976710656)), (109453621/9007199254740992), by norm_num⟩
  | 1 => ⟨((-818380087/4294967296), (832959155/4294967296)), (17/536870912), by norm_num⟩
  | 2 => ⟨((1049551739/4294967296), (-1068249025/4294967296)), (177/4294967296), by norm_num⟩
  | 3 => ⟨((-224337255/1073741824), (228333721/1073741824)), (77/2147483648), by norm_num⟩
  | 4 => ⟨((287706849/2147483648), (-585664431/4294967296)), (25/1073741824), by norm_num⟩
  | 5 => ⟨((-295181399/4294967296), (300439921/4294967296)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((1009500453/34359738368), (-1027484243/34359738368)), (91/17179869184), by norm_num⟩
  | 7 => ⟨((-739805011/68719476736), (188246075/17179869184)), (135/68719476736), by norm_num⟩
  | 8 => ⟨((474390597/137438953472), (-482841649/137438953472)), (175/274877906944), by norm_num⟩
  | 9 => ⟨((-540794603/549755813888), (137607153/137438953472)), (101/549755813888), by norm_num⟩
  | 10 => ⟨((138711077/549755813888), (-282364303/1099511627776)), (105/2199023255552), by norm_num⟩
  | 11 => ⟨((-1035016401/17592186044416), (526727373/8796093022208)), (99/8796093022208), by norm_num⟩
  | 12 => ⟨((884921551/70368744177664), (-900686025/70368744177664)), (171/70368744177664), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275821141/10141204801825835211973625643008), (-64660548709/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778506697170819/633825300114114700748351602688), (-612007718159/316912650057057350374175801344)), (92321/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944723539871243/19807040628566084398385987584), (-1376748215869/39614081257132168796771975168)), (103869/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889203810008045/2475880078570760549798248448), (-1462460145875/2475880078570760549798248448)), (55185/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770870149577843/154742504910672534362390528), (-1462083605641/154742504910672534362390528)), (27595/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774626508416265/4835703278458516698824704), (-1370303437867/9671406556917033397649408)), (25873/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258525921763813/604462909807314587353088), (-149826964221/75557863725914323419136)), (45283/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887365236154357/75557863725914323419136), (-1947001234923/75557863725914323419136)), (73595/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297219503043107/4722366482869645213696), (-729797801537/2361183241434822606848)), (55205/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621008436443849/590295810358705651712), (-2005879643229/590295810358705651712)), (75921/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455731349941191/18446744073709551616), (-2505754117783/73786976294838206464)), (94923/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455509882437259/2305843009213693952), (-2816781330627/9223372036854775808)), (53409/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398322165915869/288230376151711744), (-1407021886587/576460752303423488)), (106855/576460752303423488), by norm_num⟩
  | 5 => ⟨((596985710463161/72057594037927936), (-2459211993721/144115188075855872)), (23385/18014398509481984), by norm_num⟩
  | 4 => ⟨((93170299889265/2251799813685248), (-3682673975775/36028797018963968)), (280787/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488119390363305/9007199254740992), (-4592609768111/9007199254740992)), (175639/4503599627370496), by norm_num⟩
  | 2 => ⟨((2225678879562857/4503599627370496), (-9153098591263/4503599627370496)), (351719/2251799813685248), by norm_num⟩
  | 1 => ⟨((2212718337006651/2251799813685248), (-13649614966983/2251799813685248)), (1057375/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174035555491357/2251799813685248), (-26980709983175/2251799813685248)), (1061835/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174035555491357/2251799813685248), (-26980709983175/2251799813685248)), (4050579075339889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1049316775210011/1125899906842624), (-6512237728609/281474976710656)), (4151553/2251799813685248), by norm_num⟩
  | 2 => ⟨((1954680234372209/2251799813685248), (-48554229385793/1125899906842624)), (1982609/562949953421312), by norm_num⟩
  | 3 => ⟨((1692577085545999/2251799813685248), (-168590461547751/2251799813685248)), (7226033/1125899906842624), by norm_num⟩
  | 4 => ⟨((1259612168698301/2251799813685248), (-31680475138501/281474976710656)), (23889973/2251799813685248), by norm_num⟩
  | 5 => ⟨((1352153105227637/4503599627370496), (-567085748949123/4503599627370496)), (64209735/4503599627370496), by norm_num⟩
  | 6 => ⟨((83640415333461/1125899906842624), (-21282607797543/281474976710656)), (109453621/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75307241/33554432), (-67549587/2097152)), (1/16777216), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-77483061/33554432), (-17375317/524288)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-274625099146763/18014398509481984), (-442102591649677/4503599627370496)), (301185447/18014398509481984), by norm_num⟩
  | 1 => ⟨((86397097/2147483648), (1112684331/4294967296)), (3/67108864), by norm_num⟩
  | 2 => ⟨((-57001723/1073741824), (-1468218869/4294967296)), (255/4294967296), by norm_num⟩
  | 3 => ⟨((50143605/1073741824), (161446407/536870912)), (227/4294967296), by norm_num⟩
  | 4 => ⟨((-264663697/8589934592), (-852132647/4294967296)), (151/4294967296), by norm_num⟩
  | 5 => ⟨((69846267/4294967296), (899530763/8589934592)), (321/17179869184), by norm_num⟩
  | 6 => ⟨((-122885535/17179869184), (-1582608835/34359738368)), (285/34359738368), by norm_num⟩
  | 7 => ⟨((46328853/17179869184), (149164123/8589934592)), (217/68719476736), by norm_num⟩
  | 8 => ⟨((-122264499/137438953472), (-6150823/1073741824)), (9/8589934592), by norm_num⟩
  | 9 => ⟨((286811575/1099511627776), (1846883501/1099511627776)), (85/274877906944), by norm_num⟩
  | 10 => ⟨((-75691219/1099511627776), (-60925393/137438953472)), (181/2199023255552), by norm_num⟩
  | 11 => ⟨((9079703/549755813888), (935479883/8796093022208)), (175/8796093022208), by norm_num⟩
  | 12 => ⟨((-255593139/70368744177664), (-822928347/35184372088832)), (155/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634167/10141204801825835211973625643008), (-1123411749257/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444600946447777/158456325028528675187087900672), (-2657969488431/633825300114114700748351602688)), (46231/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944665580301433/19807040628566084398385987584), (-2989610238127/39614081257132168796771975168)), (104037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889080454769929/2475880078570760549798248448), (-1587856115373/1237940039285380274899124224)), (55279/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442686644879037/38685626227668133590597632), (-396858782907/19342813113834066795298816)), (27645/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774568470912291/4835703278458516698824704), (-2975546539147/9671406556917033397649408)), (103693/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629212064126831/302231454903657293676544), (-2602709179045/604462909807314587353088)), (45377/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943599697423457/37778931862957161709568), (-2113863350923/37778931862957161709568)), (147519/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297094748983623/4722366482869645213696), (-3169329392343/4722366482869645213696)), (55339/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810418147070847/295147905179352825856), (-4355447413399/590295810358705651712)), (38061/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822709315050229/73786976294838206464), (-2720370267153/36893488147419103232)), (95199/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821795189766253/9223372036854775808), (-6115929373709/9223372036854775808)), (107163/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593042771160397/1152921504606846976), (-1527451157893/288230376151711744)), (107243/576460752303423488), by norm_num⟩
  | 5 => ⟨((74609657685653/9007199254740992), (-667399434335/18014398509481984)), (187857/144115188075855872), by norm_num⟩
  | 4 => ⟨((745197989333329/18014398509481984), (-7995042936381/36028797018963968)), (282147/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487702314414405/9007199254740992), (-2492444658821/2251799813685248)), (176659/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112413337649715/2251799813685248), (-9933816893337/2251799813685248)), (11071/70368744177664), by norm_num⟩
  | 1 => ⟨((1105697627935513/1125899906842624), (-29622171894487/2251799813685248)), (1067599/2251799813685248), by norm_num⟩
  | 0 => ⟨((2171212421210105/2251799813685248), (-58530402177211/2251799813685248)), (538601/562949953421312), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2171212421210105/2251799813685248), (-58530402177211/2251799813685248)), (2054599764110374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((522996931322297/562949953421312), (-112871433289271/2251799813685248)), (4266603/2251799813685248), by norm_num⟩
  | 2 => ⟨((1937859953530399/2251799813685248), (-104860854655865/1125899906842624)), (8355325/2251799813685248), by norm_num⟩
  | 3 => ⟨((206019534995117/281474976710656), (-180482873917651/1125899906842624)), (7968623/1125899906842624), by norm_num⟩
  | 4 => ⟨((574234626974229/1125899906842624), (-264201089515103/1125899906842624)), (28439361/2251799813685248), by norm_num⟩
  | 5 => ⟨((923503730786253/4503599627370496), (-538994321473361/2251799813685248)), (84712953/4503599627370496), by norm_num⟩
  | 6 => ⟨((-274625099146763/18014398509481984), (-442102591649677/4503599627370496)), (301185447/18014398509481984), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77483061/33554432), (-17375317/524288)), (1/16777216), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-79508701/33554432), (-142636479/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-718006234053477/9007199254740992), (-440541947932161/9007199254740992)), (76368597/4503599627370496), by norm_num⟩
  | 1 => ⟨((927160705/4294967296), (8888615/67108864)), (199/4294967296), by norm_num⟩
  | 2 => ⟨((-1255398867/4294967296), (-192566525/1073741824)), (17/268435456), by norm_num⟩
  | 3 => ⟨((566613859/2147483648), (347653211/2147483648)), (31/536870912), by norm_num⟩
  | 4 => ⟨((-767209387/4294967296), (-235365587/2147483648)), (85/2147483648), by norm_num⟩
  | 5 => ⟨((415528307/4294967296), (127476365/2147483648)), (93/4294967296), by norm_num⟩
  | 6 => ⟨((-375090505/8589934592), (-230141597/8589934592)), (85/8589934592), by norm_num⟩
  | 7 => ⟨((145109131/8589934592), (712268569/68719476736)), (265/68719476736), by norm_num⟩
  | 8 => ⟨((-785925623/137438953472), (-60276845/17179869184)), (181/137438953472), by norm_num⟩
  | 9 => ⟨((945922685/549755813888), (145095753/137438953472)), (55/137438953472), by norm_num⟩
  | 10 => ⟨((-1024642447/2199023255552), (-628682533/2199023255552)), (15/137438953472), by norm_num⟩
  | 11 => ⟨((1009012067/8796093022208), (619092313/8796093022208)), (119/4398046511104), by norm_num⟩
  | 12 => ⟨((-227704611/8796093022208), (-279422177/17592186044416)), (217/35184372088832), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580889171562799/10141204801825835211973625643008), (-3375405615915/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778306006636169/633825300114114700748351602688), (-998168184841/158456325028528675187087900672)), (46297/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472305229165571/9903520314283042199192993792), (-4490813099959/39614081257132168796771975168)), (104193/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944481499071309/1237940039285380274899124224), (-4770333624445/2475880078570760549798248448)), (55367/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885314380250663/77371252455336267181195264), (-4769034141889/154742504910672534362390528)), (110767/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387256525439979/2417851639229258349412352), (-139674659735/302231454903657293676544)), (12985/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((78645422424657/37778931862957161709568), (-3909510417291/604462909807314587353088)), (45465/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887040449433961/75557863725914323419136), (-3175183774807/37778931862957161709568)), (73913/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296974910599851/4722366482869645213696), (-4760512868841/4722366482869645213696)), (110927/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50645952970235/18446744073709551616), (-3271014757817/295147905179352825856)), (76309/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822500536542371/73786976294838206464), (-8172025756873/73786976294838206464)), (2983/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1821558214479973/9223372036854775808), (-9185955032041/9223372036854775808)), (214969/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592803177222279/1152921504606846976), (-9176493407929/1152921504606846976)), (215211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193541940090543/144115188075855872), (-8018795391341/144115188075855872)), (188581/144115188075855872), by norm_num⟩
  | 4 => ⟨((186258905930927/4503599627370496), (-6003470190055/18014398509481984)), (35427/4503599627370496), by norm_num⟩
  | 3 => ⟨((1487286194540101/9007199254740992), (-467860256311/281474976710656)), (355223/9007199254740992), by norm_num⟩
  | 2 => ⟨((138997749530641/281474976710656), (-14915897273729/2251799813685248)), (22291/140737488355328), by norm_num⟩
  | 1 => ⟨((552506433225643/562949953421312), (-22235083764415/1125899906842624)), (33661/70368744177664), by norm_num⟩
  | 0 => ⟨((135510938693507/140737488355328), (-43917011871535/1125899906842624)), (1091579/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((135510938693507/140737488355328), (-43917011871535/1125899906842624)), (4164043430808639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042114860562277/1125899906842624), (-5285758944607/70368744177664)), (273405/140737488355328), by norm_num⟩
  | 2 => ⟨((958212118730273/1125899906842624), (-156557233183461/1125899906842624)), (8755077/2251799813685248), by norm_num⟩
  | 3 => ⟨((396864895266579/562949953421312), (-133240119480925/562949953421312)), (17337051/2251799813685248), by norm_num⟩
  | 4 => ⟨((992975057952077/2251799813685248), (-751446209265847/2251799813685248)), (16325533/1125899906842624), by norm_num⟩
  | 5 => ⟨((374214490768061/4503599627370496), (-662729731709553/2251799813685248)), (50588169/2251799813685248), by norm_num⟩
  | 6 => ⟨((-718006234053477/9007199254740992), (-440541947932161/9007199254740992)), (76368597/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-79508701/33554432), (-142636479/4194304)), (1/16777216), by norm_num⟩, -5, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile032Terms1
