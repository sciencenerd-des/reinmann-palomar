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
namespace Reinmann.XiRectangle.Tile042Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (3525/256))
  have he : value ((7/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10175445/4194304), (-40031745/1048576)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((176712224215841/2251799813685248), (-22894964705235/562949953421312)), (74316893/9007199254740992), by norm_num⟩
  | 1 => ⟨((-934506073/4294967296), (484301155/4294967296)), (25/1073741824), by norm_num⟩
  | 2 => ⟨((323875125/1073741824), (-83922995/536870912)), (141/4294967296), by norm_num⟩
  | 3 => ⟨((-299324173/1073741824), (155122633/1073741824)), (33/1073741824), by norm_num⟩
  | 4 => ⟨((414951413/2147483648), (-430091263/4294967296)), (93/4294967296), by norm_num⟩
  | 5 => ⟨((-460195843/4294967296), (238493237/4294967296)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((106327817/2147483648), (-220414553/8589934592)), (99/17179869184), by norm_num⟩
  | 7 => ⟨((-1347672257/68719476736), (174605401/17179869184)), (5/2147483648), by norm_num⟩
  | 8 => ⟨((934135225/137438953472), (-242054483/68719476736)), (113/137438953472), by norm_num⟩
  | 9 => ⟨((-575549509/274877906944), (596548915/549755813888)), (141/549755813888), by norm_num⟩
  | 10 => ⟨((638304831/1099511627776), (-330796959/1099511627776)), (159/2199023255552), by norm_num⟩
  | 11 => ⟨((-1287095837/8796093022208), (41689269/549755813888)), (81/4398046511104), by norm_num⟩
  | 12 => ⟨((594764567/17592186044416), (-616465051/35184372088832)), (19/4398046511104), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395203902880331/2535301200456458802993406410752), (-622824487735/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778227249322421/633825300114114700748351602688), (-736652943177/633825300114114700748351602688)), (92273/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944566396723881/19807040628566084398385987584), (-414280233417/19807040628566084398385987584)), (25953/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944434999031875/1237940039285380274899124224), (-880127728513/2475880078570760549798248448)), (110305/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885268234728113/77371252455336267181195264), (-439941425447/77371252455336267181195264)), (13789/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774470165858345/4835703278458516698824704), (-824630085459/9671406556917033397649408)), (101/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1258252462214249/604462909807314587353088), (-721291344683/604462909807314587353088)), (45251/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886921126597459/75557863725914323419136), (-1171611200037/75557863725914323419136)), (73539/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296886650158677/4722366482869645213696), (-219570574205/1180591620717411303424)), (6895/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1620551136029151/590295810358705651712), (-150868270835/73786976294838206464)), (75853/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822354332202097/73786976294838206464), (-1507645466617/73786976294838206464)), (189659/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910698922562123/4611686018427387904), (-847338076459/4611686018427387904)), (106701/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398161983952543/288230376151711744), (-211612090057/144115188075855872)), (26681/144115188075855872), by norm_num⟩
  | 5 => ⟨((596705929382183/72057594037927936), (-23113832189/2251799813685248)), (186817/144115188075855872), by norm_num⟩
  | 4 => ⟨((744943800132703/18014398509481984), (-1107467684619/18014398509481984)), (280327/36028797018963968), by norm_num⟩
  | 3 => ⟨((5808893116617/35184372088832), (-1380848135683/4503599627370496)), (87647/2251799813685248), by norm_num⟩
  | 2 => ⟨((555901143069863/1125899906842624), (-2751264746707/2251799813685248)), (175429/1125899906842624), by norm_num⟩
  | 1 => ⟨((138102171310537/140737488355328), (-2050457825589/562949953421312)), (1053931/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083989524680829/1125899906842624), (-63269433075/8796093022208)), (2113347/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1083989524680829/1125899906842624), (-63269433075/8796093022208)), (8061779030806731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2087161917286297/2251799813685248), (-31188120686145/2251799813685248)), (4099763/2251799813685248), by norm_num⟩
  | 2 => ⟨((120883086043807/140737488355328), (-28907835133585/1125899906842624)), (3856797/1125899906842624), by norm_num⟩
  | 3 => ⟨((1659789547620701/2251799813685248), (-49659381627881/1125899906842624)), (13646911/2251799813685248), by norm_num⟩
  | 4 => ⟨((1219041368141783/2251799813685248), (-146414653853925/2251799813685248)), (21321963/2251799813685248), by norm_num⟩
  | 5 => ⟨((1300847968346575/4503599627370496), (-79263493524315/1125899906842624)), (25858607/2251799813685248), by norm_num⟩
  | 6 => ⟨((176712224215841/2251799813685248), (-22894964705235/562949953421312)), (74316893/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/4194304), (-40031745/1048576)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41591753/16777216), (-654513081/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((192554773607071/9007199254740992), (-730032674817209/9007199254740992)), (111874107/9007199254740992), by norm_num⟩
  | 1 => ⟨((-130068959/2147483648), (986260565/4294967296)), (153/4294967296), by norm_num⟩
  | 2 => ⟨((184256555/2147483648), (-1397143297/4294967296)), (219/4294967296), by norm_num⟩
  | 3 => ⟨((-87006355/1073741824), (164933543/536870912)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((123253783/2147483648), (-467291915/2147483648)), (149/4294967296), by norm_num⟩
  | 5 => ⟨((-139681705/4294967296), (1059150151/8589934592)), (171/8589934592), by norm_num⟩
  | 6 => ⟨((263832047/17179869184), (-500133057/8589934592)), (163/17179869184), by norm_num⟩
  | 7 => ⟨((-213569279/34359738368), (1619409887/68719476736)), (133/34359738368), by norm_num⟩
  | 8 => ⟨((151271833/68719476736), (-1147033425/137438953472)), (191/137438953472), by norm_num⟩
  | 9 => ⟨((-380964779/549755813888), (361087823/137438953472)), (243/549755813888), by norm_num⟩
  | 10 => ⟨((215870899/1099511627776), (-818431071/1099511627776)), (139/1099511627776), by norm_num⟩
  | 11 => ⟨((-444806045/8796093022208), (1686392605/8796093022208)), (289/8796093022208), by norm_num⟩
  | 12 => ⟨((420076807/35184372088832), (-1592636677/35184372088832)), (69/8796093022208), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580746512500455/10141204801825835211973625643008), (-427552265639/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222267952915063/79228162514264337593543950336), (-252824071365/79228162514264337593543950336)), (5775/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889038628682785/39614081257132168796771975168), (-2274926358553/39614081257132168796771975168)), (51981/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888769832933333/2475880078570760549798248448), (-1208249005513/1237940039285380274899124224)), (110475/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770436175030151/154742504910672534362390528), (-301976329881/19342813113834066795298816)), (27623/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548846168431563/9671406556917033397649408), (-1132046196265/4835703278458516698824704)), (25901/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258169932209653/604462909807314587353088), (-247543880557/75557863725914323419136)), (90671/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471696689624573/18889465931478580854784), (-201043917145/4722366482869645213696)), (147373/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162098206203105/590295810358705651712), (-1205665402191/2361183241434822606848)), (110559/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202551487008429/73786976294838206464), (-3313637153143/590295810358705651712)), (76033/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822179736815553/73786976294838206464), (-258695897095/4611686018427387904)), (95077/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227650084601795/1152921504606846976), (-4652525220101/9223372036854775808)), (214021/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592449834080443/1152921504606846976), (-1161882211677/288230376151711744)), (214143/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193237472680435/144115188075855872), (-4060973395577/144115188075855872)), (93757/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489623934550283/36028797018963968), (-6080247821327/36028797018963968)), (140773/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486743421127061/9007199254740992), (-7580725191779/9007199254740992)), (352417/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111463651327481/2251799813685248), (-15102843941269/4503599627370496)), (353145/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104295990833395/1125899906842624), (-11254132132563/1125899906842624)), (66443/140737488355328), by norm_num⟩
  | 0 => ⟨((270723439624419/281474976710656), (-11108899909543/562949953421312)), (1070431/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((270723439624419/281474976710656), (-11108899909543/562949953421312)), (4083370213035201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2082183779287345/2251799813685248), (-42738287134439/1125899906842624)), (1050667/562949953421312), by norm_num⟩
  | 2 => ⟨((480524847243767/562949953421312), (-158076162339167/2251799813685248)), (2022817/562949953421312), by norm_num⟩
  | 3 => ⟨((814787790126215/1125899906842624), (-134931219550277/1125899906842624)), (14949161/2251799813685248), by norm_num⟩
  | 4 => ⟨((1146945132520891/2251799813685248), (-390586443886339/2251799813685248)), (3152479/281474976710656), by norm_num⟩
  | 5 => ⟨((516442607285933/2251799813685248), (-795774505213985/4503599627370496)), (34440263/2251799813685248), by norm_num⟩
  | 6 => ⟨((192554773607071/9007199254740992), (-730032674817209/9007199254740992)), (111874107/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41591753/16777216), (-654513081/16777216)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-84861685/33554432), (-1335434995/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-362535041613883/9007199254740992), (-1239893985578733/18014398509481984)), (259108013/18014398509481984), by norm_num⟩
  | 1 => ⟨((499659083/4294967296), (427216835/2147483648)), (45/1073741824), by norm_num⟩
  | 2 => ⟨((-722100251/4294967296), (-1234815475/4294967296)), (131/2147483648), by norm_num⟩
  | 3 => ⟨((173928181/1073741824), (1189691925/4294967296)), (255/4294967296), by norm_num⟩
  | 4 => ⟨((-251358551/2147483648), (-859662985/4294967296)), (93/2147483648), by norm_num⟩
  | 5 => ⟨((290607863/4294967296), (993898245/8589934592)), (217/8589934592), by norm_num⟩
  | 6 => ⟨((-559976507/17179869184), (-957578473/17179869184)), (211/17179869184), by norm_num⟩
  | 7 => ⟨((28902505/2147483648), (24712123/1073741824)), (11/2147483648), by norm_num⟩
  | 8 => ⟨((-334155937/68719476736), (-1142835559/137438953472)), (257/137438953472), by norm_num⟩
  | 9 => ⟨((107314987/68719476736), (734048805/274877906944)), (167/274877906944), by norm_num⟩
  | 10 => ⟨((-124072083/274877906944), (-424334787/549755813888)), (195/1099511627776), by norm_num⟩
  | 11 => ⟨((521621011/4398046511104), (445994649/2199023255552)), (207/4398046511104), by norm_num⟩
  | 12 => ⟨((-251279773/8796093022208), (-859393559/17592186044416)), (201/17592186044416), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395170341040317/2535301200456458802993406410752), (-1367711234679/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111128947586759/39614081257132168796771975168), (-3234802289027/633825300114114700748351602688)), (92519/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944473969918065/19807040628566084398385987584), (-454793329435/4951760157141521099596496896)), (13013/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944336624518819/1237940039285380274899124224), (-3864745232377/2475880078570760549798248448)), (110635/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885169668026569/77371252455336267181195264), (-1931811377565/77371252455336267181195264)), (110661/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548755111091057/9671406556917033397649408), (-3620954057453/9671406556917033397649408)), (51887/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258089986489651/604462909807314587353088), (-3167142925743/604462909807314587353088)), (45415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886656339963751/75557863725914323419136), (-2572186670719/37778931862957161709568)), (36913/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296687392862633/4722366482869645213696), (-964081545985/1180591620717411303424)), (55393/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620276074373535/590295810358705651712), (-662409392293/73786976294838206464)), (76203/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911004441742119/36893488147419103232), (-6619336668913/73786976294838206464)), (190621/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821006989870867/9223372036854775808), (-465013566563/576460752303423488)), (53651/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796127152610865/576460752303423488), (-929006625989/144115188075855872)), (214801/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596532159316201/72057594037927936), (-6493871166253/144115188075855872)), (188171/144115188075855872), by norm_num⟩
  | 4 => ⟨((372340021375609/9007199254740992), (-4861239837813/18014398509481984)), (282697/36028797018963968), by norm_num⟩
  | 3 => ⟨((743203218086899/4503599627370496), (-12121079731981/9007199254740992)), (354145/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222231942699291/4503599627370496), (-1509144359487/281474976710656)), (710615/4503599627370496), by norm_num⟩
  | 1 => ⟨((68984247593997/70368744177664), (-17990287026145/1125899906842624)), (1071751/2251799813685248), by norm_num⟩
  | 0 => ⟨((2163386049698629/2251799813685248), (-35504990572013/1125899906842624)), (2166919/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2163386049698629/2251799813685248), (-35504990572013/1125899906842624)), (8266139992720793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((129762777817637/140737488355328), (-136443747497193/2251799813685248)), (537543/281474976710656), by norm_num⟩
  | 2 => ⟨((1906034442077587/2251799813685248), (-31450965727025/281474976710656)), (8451151/2251799813685248), by norm_num⟩
  | 3 => ⟨((1585247864841763/2251799813685248), (-106486595385589/562949953421312)), (2024443/281474976710656), by norm_num⟩
  | 4 => ⟨((16178589530821/35184372088832), (-299862620013289/1125899906842624)), (28930091/2251799813685248), by norm_num⟩
  | 5 => ⟨((632777707730695/4503599627370496), (-275767561381119/1125899906842624)), (84030885/4503599627370496), by norm_num⟩
  | 6 => ⟨((-362535041613883/9007199254740992), (-1239893985578733/18014398509481984)), (259108013/18014398509481984), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-84861685/33554432), (-1335434995/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-86449105/33554432), (-170051951/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-654962387153355/9007199254740992), (-200567283943347/9007199254740992)), (120352499/9007199254740992), by norm_num⟩
  | 1 => ⟨((919578925/4294967296), (70400015/1073741824)), (171/4294967296), by norm_num⟩
  | 2 => ⟨((-21153469/67108864), (-414577097/4294967296)), (127/2147483648), by norm_num⟩
  | 3 => ⟨((332187193/1073741824), (101724747/1073741824)), (251/4294967296), by norm_num⟩
  | 4 => ⟨((-978104919/4294967296), (-149761155/2147483648)), (187/4294967296), by norm_num⟩
  | 5 => ⟨((287997025/2147483648), (176385033/4294967296)), (111/4294967296), by norm_num⟩
  | 6 => ⟨((-141331611/2147483648), (-86559161/4294967296)), (55/4294967296), by norm_num⟩
  | 7 => ⟨((475591205/17179869184), (145638953/17179869184)), (187/34359738368), by norm_num⟩
  | 8 => ⟨((-700174641/68719476736), (-214412505/68719476736)), (277/137438953472), by norm_num⟩
  | 9 => ⟨((894801/268435456), (280588683/274877906944)), (183/274877906944), by norm_num⟩
  | 10 => ⟨((-269791943/274877906944), (-165235251/549755813888)), (217/1099511627776), by norm_num⟩
  | 11 => ⟨((1155470419/4398046511104), (176918223/2199023255552)), (117/2199023255552), by norm_num⟩
  | 12 => ⟨((-567035357/8796093022208), (-347283275/17592186044416)), (29/2199023255552), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395154934790955/2535301200456458802993406410752), (-3705191158407/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((13890512550191/4951760157141521099596496896), (-4381269977995/633825300114114700748351602688)), (11579/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944430226009649/19807040628566084398385987584), (-4927805217811/39614081257132168796771975168)), (104239/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236072496593759/309485009821345068724781056), (-5234414544337/2475880078570760549798248448)), (55393/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885122849807251/77371252455336267181195264), (-2616432004691/77371252455336267181195264)), (55411/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548666944590763/9671406556917033397649408), (-4904162954871/9671406556917033397649408)), (51967/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258012458824323/604462909807314587353088), (-134046749031/18889465931478580854784)), (90981/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117908102629213/4722366482869645213696), (-6967344473297/75557863725914323419136)), (147915/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162073968024685/590295810358705651712), (-81606384657/73786976294838206464)), (13875/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810071771438411/295147905179352825856), (-1794244130297/147573952589676412928)), (152727/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821841699753831/73786976294838206464), (-8964645711125/73786976294838206464)), (191063/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910408411567815/4611686018427387904), (-10076190843969/9223372036854775808)), (215157/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199007692287835/144115188075855872), (-10064903813193/1152921504606846976)), (215423/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192892730767539/144115188075855872), (-8794103168745/144115188075855872)), (188793/144115188075855872), by norm_num⟩
  | 4 => ⟨((744548445520293/18014398509481984), (-13165805034645/36028797018963968)), (70947/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486067317994565/9007199254740992), (-16412951958765/9007199254740992)), (355783/9007199254740992), by norm_num⟩
  | 2 => ⟨((555380879705083/1125899906842624), (-4086652721821/562949953421312)), (178679/1125899906842624), by norm_num⟩
  | 1 => ⟨((275794809196559/281474976710656), (-24354468034993/1125899906842624)), (269993/562949953421312), by norm_num⟩
  | 0 => ⟨((1080407905481035/1125899906842624), (-24024786073927/562949953421312)), (273959/281474976710656), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1080407905481035/1125899906842624), (-24024786073927/562949953421312)), (1045070649267101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1034703417028671/1125899906842624), (-11527032129593/140737488355328)), (2196651/1125899906842624), by norm_num⟩
  | 2 => ⟨((1886681607652713/2251799813685248), (-338987420397221/2251799813685248)), (2198641/562949953421312), by norm_num⟩
  | 3 => ⟨((1529734124913179/2251799813685248), (-568044572525639/2251799813685248)), (8692509/1125899906842624), by norm_num⟩
  | 4 => ⟨((895910837316573/2251799813685248), (-771789003430169/2251799813685248)), (32391797/2251799813685248), by norm_num⟩
  | 5 => ⟨((183851123308143/4503599627370496), (-307067319258379/1125899906842624)), (47979217/2251799813685248), by norm_num⟩
  | 6 => ⟨((-654962387153355/9007199254740992), (-200567283943347/9007199254740992)), (120352499/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-86449105/33554432), (-170051951/4194304)), (1/16777216), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-87955083/33554432), (-346028647/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1201738846990415/18014398509481984), (521063057251503/18014398509481984)), (29336927/2251799813685248), by norm_num⟩
  | 1 => ⟨((429163915/2147483648), (-372163157/4294967296)), (85/2147483648), by norm_num⟩
  | 2 => ⟨((-1285660191/4294967296), (278725295/2147483648)), (257/4294967296), by norm_num⟩
  | 3 => ⟨((641915621/2147483648), (-556657575/4294967296)), (259/4294967296), by norm_num⟩
  | 4 => ⟨((-961503671/4294967296), (208449633/2147483648)), (49/1073741824), by norm_num⟩
  | 5 => ⟨((1152163031/8589934592), (-249783717/4294967296)), (237/8589934592), by norm_num⟩
  | 6 => ⟨((-143815499/2147483648), (249428381/8589934592)), (239/17179869184), by norm_num⟩
  | 7 => ⟨((492380265/17179869184), (-426983229/34359738368)), (103/17179869184), by norm_num⟩
  | 8 => ⟨((-1475039451/137438953472), (79945465/17179869184)), (311/137438953472), by norm_num⟩
  | 9 => ⟨((981960731/274877906944), (-212884631/137438953472)), (209/274877906944), by norm_num⟩
  | 10 => ⟨((-1176676581/1099511627776), (7971817/17179869184)), (253/1099511627776), by norm_num⟩
  | 11 => ⟨((640910547/2199023255552), (-555785995/4398046511104)), (139/2199023255552), by norm_num⟩
  | 12 => ⟨((-1279997607/17592186044416), (138748837/4398046511104)), (35/2199023255552), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790280637907115/5070602400912917605986812821504), (3559344621897/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777917272255077/633825300114114700748351602688), (4208499105473/633825300114114700748351602688)), (46307/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888783638393605/39614081257132168796771975168), (4733467205053/39614081257132168796771975168)), (104219/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888498438524747/2475880078570760549798248448), (5027962043261/2475880078570760549798248448)), (110763/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770164255617881/154742504910672534362390528), (5026447151915/154742504910672534362390528)), (55399/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387147671664393/2417851639229258349412352), (4710685047945/9671406556917033397649408)), (51955/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628972914442681/302231454903657293676544), (4120240726279/604462909807314587353088)), (45479/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886421547822961/75557863725914323419136), (6692375876151/75557863725914323419136)), (36969/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648255415182515/2361183241434822606848), (5016644507099/4722366482869645213696)), (13871/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810016270498407/295147905179352825856), (1723400570143/147573952589676412928)), (152679/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910851664469007/36893488147419103232), (4305290114031/36893488147419103232)), (47749/18446744073709551616), by norm_num⟩
  | 7 => ⟨((113791354992917/576460752303423488), (2419519234023/2305843009213693952)), (215075/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591907048916787/1152921504606846976), (9667052589951/1152921504606846976)), (107665/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192758286727921/144115188075855872), (8446279531331/144115188075855872)), (47175/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488896689772605/36028797018963968), (12644663593077/36028797018963968)), (283625/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485819621803981/9007199254740992), (15762568369751/9007199254740992)), (355537/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110517880348179/2251799813685248), (15697799437497/2251799813685248)), (357051/2251799813685248), by norm_num⟩
  | 1 => ⟨((275705726306743/281474976710656), (11692603290151/562949953421312)), (269685/562949953421312), by norm_num⟩
  | 0 => ⟨((2159465712872767/2251799813685248), (92254044756503/2251799813685248)), (1093983/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2159465712872767/2251799813685248), (92254044756503/2251799813685248)), (4173213963035201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1033569087271847/1125899906842624), (88471206594275/1125899906842624)), (2187889/1125899906842624), by norm_num⟩
  | 2 => ⟨((117732257694815/140737488355328), (81216015467941/562949953421312)), (2180389/562949953421312), by norm_num⟩
  | 3 => ⟨((191116554459651/281474976710656), (135880567057963/562949953421312)), (17108321/2251799813685248), by norm_num⟩
  | 4 => ⟨((14170733592125/35184372088832), (738084105311755/2251799813685248)), (31491451/2251799813685248), by norm_num⟩
  | 5 => ⟨((246690086965813/4503599627370496), (74317037679029/281474976710656)), (46011005/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1201738846990415/18014398509481984), (521063057251503/18014398509481984)), (29336927/2251799813685248), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-87955083/33554432), (-346028647/8388608)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5586723/2097152), (-1406657049/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-590520220190671/18014398509481984), (1107501098780277/18014398509481984)), (225869163/18014398509481984), by norm_num⟩
  | 1 => ⟨((214320667/2147483648), (-803902613/4294967296)), (83/2147483648), by norm_num⟩
  | 2 => ⟨((-40781505/268435456), (305937443/1073741824)), (255/4294967296), by norm_num⟩
  | 3 => ⟨((662187771/4294967296), (-1241911213/4294967296)), (261/4294967296), by norm_num⟩
  | 4 => ⟨((-252005691/2147483648), (945256639/4294967296)), (201/4294967296), by norm_num⟩
  | 5 => ⟨((613789585/8589934592), (-1151142019/8589934592)), (247/8589934592), by norm_num⟩
  | 6 => ⟨((-622898721/17179869184), (584112951/8589934592)), (253/17179869184), by norm_num⟩
  | 7 => ⟨((541836895/34359738368), (-1016197135/34359738368)), (111/17179869184), by norm_num⟩
  | 8 => ⟨((-206204323/34359738368), (773458745/68719476736)), (171/68719476736), by norm_num⟩
  | 9 => ⟨((279019417/137438953472), (-1046583335/274877906944)), (233/274877906944), by norm_num⟩
  | 10 => ⟨((-679584701/1099511627776), (1274538579/1099511627776)), (143/549755813888), by norm_num⟩
  | 11 => ⟨((376183795/2199023255552), (-705520237/2199023255552)), (5/68719476736), by norm_num⟩
  | 12 => ⟨((-95441667/2199023255552), (715990731/8796093022208)), (41/2199023255552), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790252832762771/5070602400912917605986812821504), (2684227071663/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888927809146893/316912650057057350374175801344), (3173553503427/633825300114114700748351602688)), (92513/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944357259874103/19807040628566084398385987584), (3569418437203/39614081257132168796771975168)), (104097/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888425321409415/2475880078570760549798248448), (14810452803/9671406556917033397649408)), (55313/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442522874943565/38685626227668133590597632), (1895158130539/77371252455336267181195264)), (110653/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387130715403045/2417851639229258349412352), (1776094881397/4835703278458516698824704)), (103765/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257886865198903/604462909807314587353088), (3106934763725/604462909807314587353088)), (45411/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886326449685133/75557863725914323419136), (5046461306343/75557863725914323419136)), (73819/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296440134182863/4722366482869645213696), (3782827718225/4722366482869645213696)), (110775/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809968175997223/295147905179352825856), (5076279533/576460752303423488)), (152389/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821584617764229/73786976294838206464), (6492724152211/73786976294838206464)), (95299/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820530223077403/9223372036854775808), (7297563528765/9223372036854775808)), (13411/576460752303423488), by norm_num⟩
  | 6 => ⟨((397944550776557/288230376151711744), (7289132285989/1152921504606846976)), (13423/72057594037927936), by norm_num⟩
  | 5 => ⟨((74540529772351/9007199254740992), (6368516162661/144115188075855872)), (188139/144115188075855872), by norm_num⟩
  | 4 => ⟨((744368907262853/18014398509481984), (1191731431235/4503599627370496)), (282641/36028797018963968), by norm_num⟩
  | 3 => ⟨((742815602674303/4503599627370496), (742766170259/562949953421312)), (354061/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110344644628443/2251799813685248), (11834793805069/2251799813685248)), (710405/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102600704562627/1125899906842624), (35257884803947/2251799813685248)), (535667/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158874561137073/2251799813685248), (34767370495781/1125899906842624)), (2165679/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2158874561137073/2251799813685248), (34767370495781/1125899906842624)), (8261409768111418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2067636857514555/2251799813685248), (133330487487927/2251799813685248)), (4286367/2251799813685248), by norm_num⟩
  | 2 => ⟨((1890641046235551/2251799813685248), (122426082676173/1125899906842624)), (2094803/562949953421312), by norm_num⟩
  | 3 => ⟨((195097881341029/281474976710656), (51395282926725/281474976710656)), (3973211/562949953421312), by norm_num⟩
  | 4 => ⟨((1006745497893465/2251799813685248), (569975259732405/2251799813685248)), (27835353/2251799813685248), by norm_num⟩
  | 5 => ⟨((611657125679111/4503599627370496), (1019309128917913/4503599627370496)), (77961779/4503599627370496), by norm_num⟩
  | 6 => ⟨((-590520220190671/18014398509481984), (1107501098780277/18014398509481984)), (225869163/18014398509481984), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5586723/2097152), (-1406657049/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 12 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile042Terms2
